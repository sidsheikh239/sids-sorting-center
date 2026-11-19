"""
SID's Sorting Center - Pokemon Center order tracker for Windows.

Reads Pokemon Center shipping emails over IMAP (read-only), pulls out the
Royal Mail tracking numbers, checks each parcel every few minutes and posts
every change (new shipment, new tracking stage) to the app and, optionally,
to a Discord webhook.

Secrets (app password, Royal Mail client secret, Discord webhook) are kept in
Windows Credential Manager through the `keyring` package, never in a file.
"""

from __future__ import annotations

import email
import imaplib
import base64
import csv
import io
import json
import os
import queue
import re
import sys
import threading
import shutil
import time
import traceback
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from email.header import decode_header, make_header
from email.utils import parsedate_to_datetime
from html import unescape
from pathlib import Path

import requests

try:
    import keyring  # Windows Credential Manager
except Exception:  # pragma: no cover
    keyring = None

VERSION = "4.8"
KEEP_DAYS = 14  # only emails/parcels from the last 2 weeks onwards
APP_NAME = "SID's Sorting Center"
UPDATE_REPO = "sidsheikh239/sids-sorting-center"   # where "Check for updates" looks (public GitHub repo)
UPDATE_URL = f"https://raw.githubusercontent.com/{UPDATE_REPO}/main/sids_sorting_center.py"
KEYRING_SERVICE = "SIDsSortingCenter"
DATA_DIR = Path(os.environ.get("APPDATA", Path.home())) / "SIDsSortingCenter"
SETTINGS_FILE = DATA_DIR / "settings.json"   # non-secret settings only
STATE_FILE = DATA_DIR / "parcels.json"
ARCHIVE_FILE = DATA_DIR / "history.json"   # parcels older than KEEP_DAYS (kept for the History tab)
SUMMARY_FILE = DATA_DIR / "summary.json"   # when the last daily summary went out
PHOTOS_DIR = DATA_DIR / "Delivery photos"   # Royal Mail delivery photos, named <tracking>.png/.jpg
PHOTOS_SENT_FILE = DATA_DIR / "photos_sent.json"   # photos already posted to Discord
PHOTO_HOLD_FILE = DATA_DIR / "photo_hold.json"   # Delivered alerts waiting for their photo
PHOTO_WAIT_HOURS = 3   # send the Delivered alert without a photo if none has arrived by then
PICS_DIR = DATA_DIR / "My pictures"   # your own pictures (Settings > Look & pictures)
PIC_TYPES = (".png", ".jpg", ".jpeg", ".gif", ".webp")

# Royal Mail tracking numbers, e.g. FE827634825GB (2 letters, 9 digits, GB)
TRACKING_RE = re.compile(r"\b([A-Z]{2}\d{9}GB)\b")
# Whatever follows "Tracking Number:" (covers non-GB / other courier formats)
LABEL_RE = re.compile(r"Tracking\s*(?:Number|No\.?|#)\s*:?\s*(?:<[^>]+>\s*)*([A-Z0-9]{8,30})", re.I)
ORDER_RE = re.compile(r"Order Number:\s*(?:</b>)?\s*([A-Z]?\d{6,})", re.I)
FULFIL_RE = re.compile(r"(?:Fulfillment ID:\s*(?:</b>)?\s*|order_number=)(\d{5,})", re.I)
ITEM_RE = re.compile(r"font-weight:600; line-height:22px;\">\s*([^<]+?)\s*</td>.*?<b>Qty</b>:\s*(\d+)", re.S)

SENDERS = ["info@em.pokemon.com", "pokemoncenter.narvar.com"]

# Stage order. A parcel never moves backwards.
STAGES = ["Shipped", "Dispatched", "With Royal Mail", "At mail centre", "At delivery office",
          "Out for delivery", "Delivery attempted", "Delivered"]
# The journey bar skips "Delivery attempted" (it only happens sometimes)
JOURNEY = ["Shipped", "Dispatched", "With Royal Mail", "At mail centre", "At delivery office", "Out for delivery", "Delivered"]
MOVING = ("With Royal Mail", "At mail centre", "At delivery office")


# --------------------------------------------------------------------------
# Data
# --------------------------------------------------------------------------

@dataclass
class Parcel:
    tracking: str
    order: str = ""
    fulfilment: str = ""
    items: str = ""
    name: str = ""
    address: str = ""
    rm_status: str = ""
    carrier: str = "royalmail-is"
    shipped_at: str = ""
    stage: str = "Shipped"
    detail: str = "Shipping email received"
    updated_at: str = ""
    last_checked: str = ""
    history: list = field(default_factory=list)
    sent: list = field(default_factory=list)  # Discord alerts already sent (no repeats)
    discord_msg: str = ""   # id of this parcel's live Discord message (edited as it moves)
    paid: bool = False      # your own tick-boxes and note
    handed: bool = False
    note: str = ""

    @property
    def done(self) -> bool:
        return self.stage == "Delivered"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def local_time(iso: str) -> str:
    if not iso:
        return ""
    try:
        return datetime.fromisoformat(iso).astimezone().strftime("%d %b %H:%M")
    except ValueError:
        return iso


def load_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


OWN_WRITES: dict = {}   # file -> mtime of our own last write


def save_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, indent=2), encoding="utf-8")
    tmp.replace(path)
    try:
        OWN_WRITES[str(path)] = path.stat().st_mtime
    except OSError:
        pass


def _vtuple(v: str) -> tuple:
    try:
        return tuple(int(x) for x in v.split("."))
    except ValueError:
        return (0,)


# If pictures with these names are in "My pictures", each is used for its stage automatically
# (you can change any of them in Settings › Look & pictures).
DEFAULT_STAGE_PICS = {"Shipped": "Mimikyu", "Dispatched": "Pikachu", "With Royal Mail": "Greninja",
                      "At mail centre": "Mewtwo", "At delivery office": "Umbreon", "Out for delivery": "Rayquaza",
                      "Delivery attempted": "Gengar", "Delivered": "Charizard"}


def import_pictures(settings: dict) -> int:
    """Pictures put in a 'My pictures' folder next to the app (e.g. sent by a friend) are copied into
    your picture library, and any matching the names above are set for their stage (only on first use)."""
    src = Path(__file__).resolve().parent / "My pictures"
    added = 0
    if src.is_dir():
        PICS_DIR.mkdir(parents=True, exist_ok=True)
        for f in src.iterdir():
            if f.is_file() and f.suffix.lower() in PIC_TYPES and not (PICS_DIR / f.name).exists():
                shutil.copy2(f, PICS_DIR / f.name)
                added += 1
    if "stage_pics" not in settings:
        have = {p.stem.lower(): p.name for p in library_pictures()}
        mapping = {st: have[n.lower()] for st, n in DEFAULT_STAGE_PICS.items() if n.lower() in have}
        if mapping:
            settings["stage_pics"] = {"*": "mascot", **mapping}
            s2 = load_json(SETTINGS_FILE, {})
            s2["stage_pics"] = settings["stage_pics"]
            save_json(SETTINGS_FILE, s2)
    return added


IMAP_SERVERS = {"gmail.com": "imap.gmail.com", "googlemail.com": "imap.gmail.com",
                "outlook.com": "outlook.office365.com", "hotmail.com": "outlook.office365.com",
                "hotmail.co.uk": "outlook.office365.com", "live.com": "outlook.office365.com",
                "live.co.uk": "outlook.office365.com", "msn.com": "outlook.office365.com",
                "yahoo.com": "imap.mail.yahoo.com", "yahoo.co.uk": "imap.mail.yahoo.com",
                "icloud.com": "imap.mail.me.com", "me.com": "imap.mail.me.com", "aol.com": "imap.aol.com"}


def imap_server_for(address: str) -> str:
    return IMAP_SERVERS.get(address.strip().lower().rpartition("@")[2], "imap.gmail.com")


def check_update() -> tuple[str, bytes] | None:
    """Look at the GitHub copy. Returns (version, code) if it's newer than this one, else None."""
    r = requests.get(UPDATE_URL, timeout=20, headers={"Cache-Control": "no-cache"})
    r.raise_for_status()
    code = r.content
    m = re.search(rb'^VERSION = "([\d.]+)"', code, re.M)
    if not m:
        raise RuntimeError("The online copy doesn't look like SID's Sorting Center.")
    ver = m.group(1).decode()
    return (ver, code) if _vtuple(ver) > _vtuple(VERSION) else None


def install_update(code: bytes) -> Path:
    """Swap in the new program (your settings, parcels and pictures live elsewhere and are kept).
    The old program is kept as sids_sorting_center.previous.py. The app then restarts itself."""
    compile(code, "update", "exec")   # refuse anything that isn't valid Python
    if b"APP_NAME = \"SID's Sorting Center\"" not in code:
        raise RuntimeError("The online copy doesn't look like SID's Sorting Center.")
    here = Path(__file__).resolve()
    shutil.copy2(here, here.with_name("sids_sorting_center.previous.py"))
    tmp = here.with_suffix(".download")
    tmp.write_bytes(code)
    tmp.replace(here)
    return here


BACKUP_DIR = DATA_DIR / "Backups"
BACKUP_KEEP = 14


def backup_data(force: bool = False) -> Path | None:
    """Copy parcels, history, settings and summary into Backups/<date> (once a day; keeps 14 days).
    Passwords are never in these files (they live in Windows Credential Manager)."""
    day = datetime.now().strftime("%Y-%m-%d")
    dest = BACKUP_DIR / day
    if dest.exists() and not force:
        return None
    dest.mkdir(parents=True, exist_ok=True)
    for f in (STATE_FILE, ARCHIVE_FILE, SETTINGS_FILE, SUMMARY_FILE):
        if f.exists():
            shutil.copy2(f, dest / f.name)
    olds = sorted(d for d in BACKUP_DIR.iterdir() if d.is_dir() and re.fullmatch(r"\d{4}-\d{2}-\d{2}", d.name))
    for d in olds[:-BACKUP_KEEP]:
        shutil.rmtree(d, ignore_errors=True)
    return dest


def new_mail_ids(host: str, user: str, password: str) -> set:
    """Quick, read-only look for Pokémon Center emails from the last day (ids only, nothing downloaded)."""
    with imaplib.IMAP4_SSL(host, 993, timeout=30) as M:
        M.login(user, password)
        box = _find_all_mail(M) or "INBOX"
        if M.select(box, readonly=True)[0] != "OK":
            M.select("INBOX", readonly=True)
        q = '(from:pokemon.com OR from:narvar.com OR from:pokemoncenter.com OR subject:(order is on its way)) newer_than:1d'
        try:
            typ, data = M.search(None, "X-GM-RAW", f'"{q}"')
        except imaplib.IMAP4.error:
            since = datetime.fromtimestamp(time.time() - 86400).strftime("%d-%b-%Y")
            typ, data = M.search(None, "SINCE", since, "FROM", '"pokemon"')
        return set(data[0].split()) if typ == "OK" and data and data[0] else set()


def lan_ip() -> str:
    import socket
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("10.255.255.255", 1))   # picks the network card; sends nothing
            return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"


PHONE_PORT = 8765


def phone_page(parcels: list, last_check: str, status: str, key: str = "") -> str:
    """A small dark page for your phone: counts plus every parcel, newest movement first."""
    from html import escape
    order = ["Delivery attempted", "Out for delivery", "At delivery office", "At mail centre", "With Royal Mail",
             "Dispatched", "Shipped", "Delivered"]
    colour = {"Shipped": "#4D7CFF", "Dispatched": "#FF9F1C", "With Royal Mail": "#00E5FF", "At mail centre": "#FFC300",
              "At delivery office": "#FF2E97", "Out for delivery": "#B36BFF", "Delivery attempted": "#FFD60A",
              "Delivered": "#2BE38B"}
    counts = {st: sum(1 for p in parcels if p.stage == st) for st in order}
    chips = "".join(f'<div class="chip" style="border-color:{colour[st]}"><b style="color:{colour[st]}">{n}</b>'
                    f'<span>{escape(nice_stage(st))}</span></div>' for st, n in counts.items() if n)
    rows = []
    for p in sorted(parcels, key=lambda p: (order.index(p.stage) if p.stage in order else 9, p.updated_at), reverse=False):
        pc = POSTCODE_RE.search(p.address or "")
        c = colour.get(p.stage, "#7D8BA8")
        rows.append(f'<a class="card" style="border-left-color:{c}" href="{escape(NARVAR_URL.format(carrier=p.carrier or "royalmail-is", tracking=p.tracking))}">'
                    f'<div class="top"><span class="st" style="color:{c}">{escape(nice_stage(p.stage))}</span>'
                    f'<span class="tn">{escape(p.tracking)}</span></div>'
                    f'<div class="nm">{escape(p.name)}{" · " + escape(pc.group(0)) if pc else ""}'
                    f'{" · 💷 paid" if p.paid else ""}{" · 🤝 handed" if p.handed else ""}</div>'
                    f'<div class="up">{escape(p.rm_status or p.detail or "")}</div>'
                    f'{"<div class=nt>📝 " + escape(p.note) + "</div>" if p.note else ""}</a>')
    return f"""<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta http-equiv="refresh" content="60">
<meta name="theme-color" content="#05070F"><meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="Sorting Center">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<link rel="manifest" href="manifest.json?key={key}"><link rel="apple-touch-icon" href="icon.png">
<title>SID's Sorting Center</title><style>
body{{margin:0;background:#05070F;color:#E4EEFF;font:15px system-ui,-apple-system,Segoe UI,sans-serif}}
header{{padding:16px;background:linear-gradient(#0B1B3A,#05070F);border-bottom:3px solid #00E5FF}}
h1{{margin:0;font-size:20px;letter-spacing:.5px}} .sub{{color:#00E5FF;font-size:12px;margin-top:4px}}
.chips{{display:flex;flex-wrap:wrap;gap:8px;padding:12px 16px}}
.chip{{border:1px solid;border-radius:10px;padding:6px 10px;background:#0C1322;display:flex;gap:6px;align-items:baseline}}
.chip b{{font-size:18px}} .chip span{{font-size:12px;color:#B8C4DC}}
.list{{padding:0 12px 24px}} .card{{display:block;text-decoration:none;color:inherit;background:#0C1322;border:1px solid #1E2C4A;
border-left:5px solid;border-radius:10px;padding:10px 12px;margin:8px 0}}
.top{{display:flex;justify-content:space-between;gap:8px}} .st{{font-weight:700;font-size:13px}}
.tn{{color:#7D8BA8;font-size:12px;font-family:monospace}} .nm{{margin-top:4px;font-weight:600}}
.up{{margin-top:3px;color:#B8C4DC;font-size:13px}} .nt{{margin-top:3px;color:#FFD60A;font-size:13px}}
</style></head><body><header><h1>SID'S SORTING CENTER</h1>
<div class="sub">{escape(status)} · last check {escape(last_check or "—")} · {len(parcels)} parcels · refreshes every minute</div></header>
<div class="chips">{chips}</div><div class="list">{"".join(rows) or "<p>No parcels yet.</p>"}</div></body></html>"""


def stage_rank(stage: str) -> int:
    if stage == "In transit":  # saved by older versions
        return STAGES.index("With Royal Mail")
    return STAGES.index(stage) if stage in STAGES else 0


# --------------------------------------------------------------------------
# Secrets
# --------------------------------------------------------------------------

def get_secret(name: str) -> str:
    if keyring is None:
        return ""
    try:
        return keyring.get_password(KEYRING_SERVICE, name) or ""
    except Exception:
        return ""


def set_secret(name: str, value: str) -> None:
    if keyring is None:
        raise RuntimeError("The 'keyring' package is missing. Run: pip install keyring")
    if value:
        keyring.set_password(KEYRING_SERVICE, name, value)
    else:
        try:
            keyring.delete_password(KEYRING_SERVICE, name)
        except Exception:
            pass


# --------------------------------------------------------------------------
# Email parsing
# --------------------------------------------------------------------------

def _decode(value) -> str:
    try:
        return str(make_header(decode_header(value or "")))
    except Exception:
        return value or ""


def message_html_and_text(msg) -> str:
    parts = []
    for part in msg.walk():
        if part.get_content_type() in ("text/html", "text/plain"):
            payload = part.get_payload(decode=True)
            if payload:
                parts.append(payload.decode(part.get_content_charset() or "utf-8", "replace"))
    return "\n".join(parts)


def classify(subject: str, body: str) -> tuple[str, str] | None:
    """Map a Pokemon Center / Narvar email to (stage, detail)."""
    s = subject.lower()
    if "delivered" in s:
        return "Delivered", "Pokémon Center says the parcel was delivered"
    if "arrive soon" in s or "out for delivery" in s:
        return "Out for delivery", "Pokémon Center says it will arrive soon"
    if "on its way" in s or "has shipped" in s:
        return "Shipped", "Shipping email received"
    if "delay" in s or "exception" in s or "problem" in s:
        return None
    return None


STOP_WORDS = ("billing address", "order summary", "order details", "payment", "shipping method",
              "subtotal", "sku", "qty", "price", "total", "sincerely")


def html_to_lines(body: str) -> list[str]:
    t = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", body)
    t = re.sub(r"(?i)<br\s*/?>|</(td|tr|p|div|li|h\d)>", "\n", t)
    t = unescape(re.sub(r"<[^>]+>", " ", t))
    return [re.sub(r"\s+", " ", l).strip(" >*") for l in t.splitlines()]


POSTCODE_RE = re.compile(r"\b([A-Z]{1,2}\d[A-Z\d]?\s*\d[A-Z]{2})\b", re.I)
DEBUG_FILE = Path(__file__).with_name("address_debug.txt")


def parse_ship_to(flat: str) -> tuple[str, str]:
    """Return (name, address incl. postcode) from the 'Shipping Address' block."""
    lines = html_to_lines(flat)
    for k, line in enumerate(lines):
        low = line.lower()
        if not low.startswith(("shipping address", "ship to", "delivery address", "shipping to")):
            continue
        window = [l for l in lines[k:k + 30] if l]
        try:  # debug copy of what the app sees (stays on this PC)
            DEBUG_FILE.write_text("\n".join(window), encoding="utf-8")
        except Exception:
            pass
        rest = line.split(":", 1)[1].strip() if ":" in line else re.sub(r"(?i)^(shipping address|ship to|delivery address|shipping to)", "", line).strip()
        block = [rest] if rest else []
        for nxt in lines[k + 1:]:
            if not nxt:
                continue
            nl = nxt.lower()
            if nl.startswith(STOP_WORDS):
                break
            if nl in ("united kingdom", "gb", "uk", "great britain"):
                break
            block.append(nxt)
            if POSTCODE_RE.search(nxt) or len(block) >= 7:
                break
        if not block:
            continue
        name, addr = block[0], block[1:]
        # Name and street on one line? Split at the first comma, else the first digit
        if "," in name and (not addr or all(POSTCODE_RE.fullmatch(a.strip()) for a in addr)):
            first, other = name.split(",", 1)
            name, addr = first.strip(), [other] + addr
        if not addr:
            m = re.search(r"\d", name)
            if m and m.start() > 0:
                name, addr = name[:m.start()].strip(" ,"), [name[m.start():]]
        address = ", ".join(a.strip(" ,") for a in addr if a.strip(" ,"))
        # Make sure the postcode is there
        if not POSTCODE_RE.search(address):
            pc = POSTCODE_RE.search(" ".join(window[1:12]))
            if pc:
                address = f"{address}, {pc.group(1).upper()}" if address else pc.group(1).upper()
        address = re.sub(r",?\s*United Kingdom\s*$", "", address, flags=re.I)
        return name, address
    return "", ""


def parse_shipping_email(subject: str, body: str, date_iso: str) -> list[Parcel]:
    """Return parcels found in a 'Your order is on its way' email."""
    flat = unescape(body)
    numbers = list(dict.fromkeys(TRACKING_RE.findall(flat)))
    if not numbers:
        numbers = list(dict.fromkeys(m.upper() for m in LABEL_RE.findall(flat)))
    if not numbers:
        return []
    order = (ORDER_RE.search(flat) or [None, ""])[1]
    name, address = parse_ship_to(flat)
    fulfil = (FULFIL_RE.search(flat) or [None, ""])[1]
    cm = re.search(r"narvar\.com/pokemoncenter/tracking(?:img)?/([a-z0-9_-]+)\?", flat)
    carrier = cm.group(1) if cm else "royalmail-is"
    items = ", ".join(f"{n.strip()} x{q}" for n, q in ITEM_RE.findall(flat))[:200]
    return [Parcel(tracking=n, order=order, fulfilment=fulfil, items=items, name=name, address=address, carrier=carrier,
                   shipped_at=date_iso, updated_at=date_iso,
                   history=[{"at": date_iso, "stage": "Shipped", "detail": "Shipping email received"}])
            for n in numbers]


# --------------------------------------------------------------------------
# IMAP (read-only)
# --------------------------------------------------------------------------

def _find_all_mail(M) -> str:
    """Find Gmail's 'All Mail' folder whatever language/region it's named in."""
    try:
        typ, rows = M.list()
        for raw in rows or []:
            line = raw.decode(errors="replace") if isinstance(raw, bytes) else str(raw)
            if "\\All" in line:
                name = line.rsplit(' "/" ', 1)[-1].strip()
                return name if name.startswith('"') else f'"{name}"'
    except Exception:
        pass
    return ""


def fetch_pokemon_emails(host: str, user: str, password: str, since_days: int = 730, log=lambda msg: None):
    """Yield (subject, body, date_iso) for Pokemon Center emails. Read-only:
    the mailbox is opened with readonly=True and bodies are fetched with
    BODY.PEEK, so nothing is marked read, moved or deleted."""
    since = datetime.fromtimestamp(time.time() - since_days * 86400).strftime("%d-%b-%Y")
    with imaplib.IMAP4_SSL(host, 993, timeout=60) as M:
        M.login(user, password)
        # Search All Mail (so archived / Updates-tab emails count too), else INBOX
        chosen = None
        for box in [b for b in (_find_all_mail(M), '"[Gmail]/All Mail"', '"[Google Mail]/All Mail"', "INBOX") if b]:
            try:
                typ, _ = M.select(box, readonly=True)
            except imaplib.IMAP4.error:
                typ = "NO"
            if typ == "OK":
                chosen = box
                break
        if not chosen:
            raise RuntimeError("Couldn't open any mailbox folder")

        ids = set()
        gmail = any(b"X-GM-EXT-1" in c for c in [x if isinstance(x, bytes) else str(x).encode() for x in M.capabilities])
        if gmail:
            # Gmail's own search syntax, same as the Gmail search box
            q = f'(from:pokemon.com OR from:narvar.com OR from:pokemoncenter.com OR subject:(order is on its way)) newer_than:{since_days}d'
            typ, data = M.search(None, "X-GM-RAW", f'"{q}"')
            if typ == "OK" and data and data[0]:
                ids.update(data[0].split())
        # Plain IMAP search as well (works on any provider)
        for crit in (["FROM", '"pokemon"'], ["FROM", '"narvar"'], ["SUBJECT", '"on its way"']):
            try:
                typ, data = M.search(None, "SINCE", since, *crit)
                if typ == "OK" and data and data[0]:
                    ids.update(data[0].split())
            except imaplib.IMAP4.error:
                pass
        log(f"Searched {chosen.strip(chr(34))}: {len(ids)} matching emails")

        for mid in sorted(ids, key=int):
            typ, data = M.fetch(mid, "(BODY.PEEK[])")
            if typ != "OK" or not data or not isinstance(data[0], tuple):
                continue
            msg = email.message_from_bytes(data[0][1])
            subject = _decode(msg.get("Subject"))
            try:
                date_iso = parsedate_to_datetime(msg.get("Date")).astimezone(timezone.utc).isoformat(timespec="seconds")
            except Exception:
                date_iso = now_iso()
            yield subject, message_html_and_text(msg), date_iso


# --------------------------------------------------------------------------
# Royal Mail (official Tracking API, optional)
# --------------------------------------------------------------------------

RM_URL = "https://api.royalmail.net/mailpieces/v2/{}/events"
REDELIVERY_URL = "https://www.royalmail.com/receiving-mail/redelivery"
NARVAR_URL = "https://pokemoncenter.narvar.com/pokemoncenter/tracking/{carrier}?tracking_numbers={tracking}&locale=en_GB"


def stage_from_text(text: str, location: str = "") -> str:
    """Map a carrier scan (status text + location) to one of STAGES.
    Waiting-for-collection messages are checked first, so a parcel only counts
    as 'At mail centre' once it has really been scanned into one."""
    t = text.lower()
    loc = f" {location} ".upper().replace(",", " ")
    if "delivered" in t and not re.search(r"not delivered|attempt|tried to deliver|to be delivered", t):
        return "Delivered"
    if re.search(r"attempt|tried to deliver|something for you|card left|awaiting collection by you|ready for collection|"
                 r"available for collection|held at|redeliver|couldn.t deliver|unable to deliver", t):
        return "Delivery attempted"
    if re.search(r"out for delivery|with (our|the) delivery|on its way to you today|with your postman|due to be delivered today", t):
        return "Out for delivery"
    # Not handed to Royal Mail yet: label made / waiting for the carrier to collect it
    if re.search(r"await\w*\s+(carrier\s+)?(pick\s?-?up|collection)|pick\s?-?up\s+(is\s+)?(pending|scheduled|requested)|"
                 r"carrier pick\s?-?up|ready (for|to) (ship|dispatch|despatch)|label|information received|pre.?advice|"
                 r"shipment (created|information)|expecting|awaiting (your )?item|not yet (been )?(received|scanned)|"
                 r"order (has been )?shipped|electronic|shipping email|preparing|being prepared|order (processed|confirmed|placed)", t):
        return "Shipped"
    # Scanned out of Pokémon Center's warehouse but not yet with Royal Mail
    if re.search(r"(order|item|parcel|package)\s+(has been\s+)?(dispatched|despatched)|^\s*(dispatched|despatched)\b|"
                 r"(dispatched|despatched) (by|from)|left (the )?(warehouse|seller|retailer)|on (its|the) way to royal mail", t):
        return "Dispatched"
    if re.search(r"delivery office|local office|\bdo\b", t) or re.search(r"\sDO\s|DELIVERY OFFICE", loc):
        return "At delivery office"
    if re.search(r"mail cent|\bmc\b|national distribution|\bndc\b|\bpsc\b|parcel hub|sort(ing)? cent|parcel cent", t) or \
            re.search(r"\s(MC|NDC|PSC)\s|MAIL CENT|PARCEL HUB", loc):
        return "At mail centre"
    if t.strip():
        return "With Royal Mail"   # any other real carrier scan (received, in transit, processing...)
    return "Shipped"


SHIP24_URL = "https://api.ship24.com/public/v1/trackers/track"
SHIP24_MILESTONES = {"delivered": "Delivered", "out_for_delivery": "Out for delivery",
                     "available_for_pickup": "Delivery attempted", "failed_attempt": "Delivery attempted",
                     "info_received": "Shipped", "pending": "Shipped"}


def ship24_status(tracking: str, api_key: str) -> tuple[str, str] | None:
    """Full Royal Mail scan history via Ship24 (free plan: 10 new parcels a month;
    re-checking a parcel it already knows doesn't use up the allowance)."""
    r = requests.post(SHIP24_URL, json={"trackingNumber": tracking, "destinationCountryCode": "GB"},
                      headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                      timeout=25)
    if r.status_code in (401, 403):
        raise RuntimeError("Ship24 rejected the API key")
    r.raise_for_status()
    trackings = (r.json().get("data") or {}).get("trackings") or []
    if not trackings:
        return None
    t = trackings[0]
    events = t.get("events") or []
    if not events:
        return None
    ev = max(events, key=lambda e: e.get("occurrenceDatetime") or "")
    milestone = (ev.get("statusMilestone") or (t.get("shipment") or {}).get("statusMilestone") or "").lower()
    stage = SHIP24_MILESTONES.get(milestone) or stage_from_text(ev.get("status") or "", ev.get("location") or "")
    when = ev.get("occurrenceDatetime") or ""
    try:
        when = datetime.fromisoformat(when.replace("Z", "+00:00")).strftime("%a %d %b %H:%M")
    except ValueError:
        pass
    where = ev.get("location") or ""
    detail = (ev.get("status") or milestone.replace("_", " ").title()) + (f" - {where}" if where else "") + (f" ({when})" if when else "")
    return stage, detail


def narvar_status(tracking: str, carrier: str = "royalmail-is") -> tuple[str, str] | None:
    """Read the latest Royal Mail scan from Pokémon Center's own tracking page
    (the 'track your parcel' link in their shipping email). No sign-up needed."""
    r = requests.get(
        NARVAR_URL.format(carrier=carrier or "royalmail-is", tracking=tracking),
        headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                               "Chrome/130.0 Safari/537.36",
                 "Accept-Language": "en-GB,en;q=0.9"},
        timeout=25,
    )
    r.raise_for_status()
    lines = [l for l in html_to_lines(r.text) if l]
    try:  # diagnostics: what the tracking page said (stays on this PC)
        dbg = Path(__file__).with_name("tracking_debug")
        dbg.mkdir(exist_ok=True)
        (dbg / f"{tracking}.txt").write_text("\n".join(lines[:150]), encoding="utf-8")
    except Exception:
        pass
    return parse_narvar_lines(lines)


WHEN_RE = re.compile(r"^(today|yesterday|(?:mon|tues|wednes|thurs|fri|satur|sun)day,?\s+[a-z]+\s+\d{1,2})\s+(\d{1,2}:\d{2})\s*\|?\s*(.*)$", re.I)


def parse_narvar_lines(lines: list[str]) -> tuple[str, str] | None:
    """Read Pokémon Center's tracking page text.

    Page layout (as served):  'Your package is <Headline>' ... 'Latest Update' then one line like
    'Today 10:24 | PSC Northampton Shipment Received' or
    'Wednesday, November 11 23:18 Order Despatched'.
    No 'Latest Update' at all means no scans yet."""
    headline = ""
    for l in lines[:6]:
        m = re.match(r"(?i)your package is\s+(.*)", l)
        if m:
            headline = m.group(1).strip()
            break
    event, when = "", ""
    for k, line in enumerate(lines):
        if line.strip().lower() == "latest update" and k + 1 < len(lines):
            m = WHEN_RE.match(lines[k + 1].strip())
            if m:
                day, tm, event = m.group(1), m.group(2), m.group(3).strip()
                today = datetime.now()
                if day.lower() == "today":
                    day = today.strftime("%a %d %b")
                elif day.lower() == "yesterday":
                    day = datetime.fromtimestamp(today.timestamp() - 86400).strftime("%a %d %b")
                when = f"{day} {tm}"
            else:
                event = lines[k + 1].strip()
            break
    if not event and not headline:
        return None
    h = headline.lower()
    if not event:  # page has no scans yet
        stage = stage_from_text(headline) if headline else "Shipped"
        if stage in MOVING:
            stage = "Shipped"
        return stage, f"{headline or 'No scans yet'}"
    stage = stage_from_text(event)
    if re.search(r"recipient communication|notification|email sent|sms sent", event, re.I):
        stage = "Dispatched" if "awaiting" in h else "With Royal Mail"   # a message, not a movement
    if "awaiting carrier pickup" in h and stage in MOVING:
        stage = "Dispatched"
    if "delivered" in h and "not" not in h:
        stage = "Delivered"
    elif "out for delivery" in h and stage_rank(stage) < stage_rank("Out for delivery"):
        stage = "Out for delivery"
    detail = event.title().replace("Psc ", "PSC ") + (f" ({when})" if when else "")
    return stage, detail


def royal_mail_status(tracking: str, client_id: str, client_secret: str) -> tuple[str, str] | None:
    """Ask Royal Mail's official Tracking API for the latest event.
    Needs your own free API keys from https://developer.royalmail.net
    Returns (stage, detail) or None if unavailable."""
    r = requests.get(
        RM_URL.format(tracking),
        headers={
            "X-IBM-Client-Id": client_id,
            "X-IBM-Client-Secret": client_secret,
            "X-Accept-RMG-Terms": "yes",
            "Accept": "application/json",
        },
        timeout=20,
    )
    if r.status_code == 404:
        return None
    r.raise_for_status()
    data = r.json().get("mailPieces", {})
    summary = data.get("summary", {}) or {}
    events = data.get("events", []) or []
    desc = summary.get("lastEventName") or (events[0].get("eventName") if events else "")
    where = summary.get("lastEventLocationName") or (events[0].get("locationName") if events else "")
    when = summary.get("lastEventDateTime") or (events[0].get("eventDateTime") if events else "")
    if not desc:
        return None
    stage = stage_from_text(desc, where)
    detail = desc + (f" - {where}" if where else "") + (f" ({local_time(when)})" if when else "")
    return stage, detail


# --------------------------------------------------------------------------
# Discord
# --------------------------------------------------------------------------

STAGE_COLOURS = {"Shipped": 0x3B6FE0, "Dispatched": 0xD9480F, "With Royal Mail": 0x0EA5A4, "At mail centre": 0xF08C00,
                 "At delivery office": 0xE0457B, "Out for delivery": 0x8E3FD1,
                 "Delivery attempted": 0xB7791F, "Delivered": 0x1F9D55}


def library_pictures() -> list:
    """Your own pictures in the 'My pictures' folder, sorted by name."""
    try:
        return sorted((p for p in PICS_DIR.iterdir() if p.is_file() and p.suffix.lower() in PIC_TYPES),
                      key=lambda p: p.name.lower())
    except OSError:
        return []


_turn = {"n": 0}


def pick_picture(choice: str) -> Path | None:
    """'turns' = the next picture in the library each time; a file name = that picture."""
    pics = library_pictures()
    if not pics or not choice or choice in ("mascot", "mascots"):
        return None
    if choice == "turns":
        _turn["n"] += 1
        return pics[_turn["n"] % len(pics)]
    for p in pics:
        if p.name == choice:
            return p
    return None


def discord_picture(stage: str, cfg: dict) -> tuple[str, bytes] | None:
    """The picture shown in the corner of a Discord alert: the picture you chose for this stage
    from 'My pictures' (or one picture for all), otherwise the built-in mascot for the stage."""
    choice = ((cfg or {}).get("stage_pics") or {}).get(stage) or ((cfg or {}).get("stage_pics") or {}).get("*", "")
    lib = pick_picture(choice)
    if lib:
        try:
            data = lib.read_bytes()
            if len(data) < 8_000_000:
                return f"picture{lib.suffix.lower()}", data
        except OSError:
            pass
    own = (cfg or {}).get("discord_image", "")
    if own:
        try:
            data = Path(own).read_bytes()
            if len(data) < 8_000_000:
                ext = Path(own).suffix.lower().lstrip(".") or "png"
                return f"picture.{ext}", data
        except OSError:
            pass
    if (cfg or {}).get("discord_mascots", True) is False:
        return None
    b64 = MASCOTS.get(stage) or MASCOTS.get("Shipped")
    return ("mascot.png", base64.b64decode(b64)) if b64 else None


SCAN_TIME_RE = re.compile(r"\((?:[A-Za-z]+,?\s+)?(\d{1,2}\s+[A-Za-z]{3,9}|[A-Za-z]{3,9}\s+\d{1,2})\s+(\d{1,2}):(\d{2})\)\s*$")


def scan_time(text: str) -> float | None:
    """When the latest scan happened, from text like 'X (Tue 17 Nov 19:13)' or
    'Order Despatched (Thursday, November 12 23:13)'."""
    m = SCAN_TIME_RE.search(text or "")
    if not m:
        return None
    now = datetime.now()
    for fmt in ("%d %b", "%d %B", "%b %d", "%B %d"):
        try:
            d = datetime.strptime(m[1], fmt).replace(year=now.year, hour=int(m[2]), minute=int(m[3]))
        except ValueError:
            continue
        if d > now.replace(second=0, microsecond=0) and (d - now).days > 1:
            d = d.replace(year=now.year - 1)
        return d.timestamp()
    return None


def last_moved(p: Parcel) -> float:
    """Time of the latest real scan; for parcels with no scan yet, when it shipped."""
    t = scan_time(p.rm_status or "") or scan_time(p.detail or "")
    if t:
        return t
    if p.stage == "Shipped":
        try:
            return datetime.fromisoformat(p.shipped_at).timestamp()
        except (TypeError, ValueError):
            pass
    for iso in (p.updated_at, p.shipped_at):
        try:
            return datetime.fromisoformat(iso).timestamp()
        except (TypeError, ValueError):
            continue
    return time.time()


def is_stuck(p: Parcel, days) -> bool:
    """Not delivered and no new scan or stage for `days` days."""
    try:
        days = float(days or 0)
    except ValueError:
        return False
    return bool(days) and not p.done and time.time() - last_moved(p) >= days * 86400


def days_since(p: Parcel) -> int:
    return int((time.time() - last_moved(p)) // 86400)


def log_entries(parcels: list) -> list:
    """Every recorded movement of every parcel, newest first (for the Logs tab)."""
    out = []
    for p in parcels:
        prev = prev_detail = None
        for h in p.history or []:
            stage = h.get("stage", "")
            try:
                ts = datetime.fromisoformat(h.get("at", "")).timestamp()
            except (ValueError, TypeError):
                ts = 0.0
            out.append({"ts": ts, "at": h.get("at", ""), "tracking": p.tracking, "name": p.name,
                        "stage": stage, "detail": h.get("detail", ""), "source": h.get("source", "email"),
                        "kind": "new" if prev is None else ("stage" if stage != prev else "moved"),
                        "prev_stage": prev or "", "prev_detail": prev_detail or "",
                        "carrier": p.carrier})
            prev, prev_detail = stage, h.get("detail", "")
    out.sort(key=lambda e: e["ts"], reverse=True)
    return out


def nice_stage(stage: str) -> str:
    return {"Shipped": "Awaiting scan", "Dispatched": "At Pokémon Center hub",
            "At mail centre": "At Royal Mail hub"}.get(stage, stage)


def _event_time(h: dict) -> float | None:
    t = scan_time(h.get("detail", ""))
    if t:
        return t
    try:
        return datetime.fromisoformat(h.get("at", "")).timestamp()
    except (TypeError, ValueError):
        return None


def parcel_times(p: Parcel) -> dict:
    """When each milestone happened (best guess from scan times, else when we saw it)."""
    out = {}
    try:
        out["shipped"] = datetime.fromisoformat(p.shipped_at).timestamp()
    except (TypeError, ValueError):
        pass
    for h in p.history or []:
        st, t = h.get("stage", ""), _event_time(h)
        if not t:
            continue
        key = {"Dispatched": "hub", "Out for delivery": "ofd", "Delivered": "delivered"}.get(st)
        if st in MOVING:
            key = "royal_mail"
        if key and key not in out:
            out[key] = t
    if "royal_mail" not in out and p.stage in MOVING:
        t = scan_time(p.rm_status or "")
        if t:
            out["royal_mail"] = t
    if "hub" not in out and p.stage == "Dispatched":
        t = scan_time(p.rm_status or "")
        if t:
            out["hub"] = t
    return out


def delivery_stats(parcels: list) -> list:
    """[(label, n, average days, fastest, slowest)] for each leg of the journey."""
    legs = [("Shipping email → delivered", "shipped", "delivered"),
            ("Despatched at Pokémon Center → first Royal Mail scan", "hub", "royal_mail"),
            ("First Royal Mail scan → delivered", "royal_mail", "delivered"),
            ("Out for delivery → delivered", "ofd", "delivered")]
    rows = []
    times = [parcel_times(p) for p in parcels]
    for label, a, b in legs:
        days = [(t[b] - t[a]) / 86400 for t in times if a in t and b in t and t[b] >= t[a]]
        if days:
            rows.append((label, len(days), sum(days) / len(days), min(days), max(days)))
        else:
            rows.append((label, 0, None, None, None))
    # still waiting at the Pokémon Center hub right now
    now = time.time()
    waiting = [(now - t["hub"]) / 86400 for p, t in zip(parcels, times) if p.stage == "Dispatched" and "hub" in t]
    rows.append(("Waiting at Pokémon Center hub right now", len(waiting),
                 sum(waiting) / len(waiting) if waiting else None,
                 min(waiting) if waiting else None, max(waiting) if waiting else None))
    return rows


def summary_embed(parcels: list, cfg: dict) -> dict:
    """The daily Discord summary: counts per stage plus anything that needs a look."""
    lines = []
    for st in STAGES:
        n = sum(p.stage == st for p in parcels)
        if n:
            lines.append(f"**{nice_stage(st)}**: {n}")
    stuck = [p for p in parcels if is_stuck(p, cfg.get("stuck_days", 3))]
    attempted = [p for p in parcels if p.stage == "Delivery attempted"]
    fields = []

    def plist(ps):
        out = "\n".join(f"`{p.tracking}` {p.name or ''} · {nice_stage(p.stage)} · {days_since(p)}d" for p in ps[:15])
        return (out + (f"\n…and {len(ps) - 15} more" if len(ps) > 15 else ""))[:1020]
    if attempted:
        fields.append({"name": f"🔔 Delivery attempted ({len(attempted)})", "value": plist(attempted), "inline": False})
    if stuck:
        fields.append({"name": f"⚠ Not moved in {cfg.get('stuck_days', 3)}+ days ({len(stuck)})", "value": plist(stuck), "inline": False})
    return {"title": f"☀ Daily summary · {len(parcels)} parcels",
            "description": "\n".join(lines) or "No parcels in the last 2 weeks.",
            "color": 0xFFCB05, "fields": fields, "timestamp": now_iso()}


CARD_REF_RE = re.compile(r"(?:card|ref(?:erence)?)\s*(?:no\.?|number)?\s*[:#]?\s*([A-Z0-9]{6,20})\b", re.I)


def notes_text(p: Parcel) -> str:
    return " ".join(x for x in ("💷" if p.paid else "", "🤝" if p.handed else "", p.note) if x)


def card_reference(p: Parcel) -> str:
    """A 'Something for you' card / redelivery reference, if the tracking text mentions one."""
    texts = [p.rm_status or "", p.detail or ""] + [h.get("detail", "") for h in reversed(p.history or [])]
    for t in texts:
        m = CARD_REF_RE.search(t)
        if m and any(ch.isdigit() for ch in m[1]) and m[1].upper() != p.tracking:
            return m[1].upper()
    return ""


def rebook_text(p: Parcel) -> str:
    ref = card_reference(p)
    how = f"card reference **{ref}**" if ref else f"tracking number **{p.tracking}**"
    return f"[Rebook with Royal Mail]({REDELIVERY_URL}) using {how}, or collect from the delivery office on the card."


def customer_key(p: Parcel) -> str:
    """Parcels going to the same postcode count as one customer (names are often spelled differently)."""
    found = POSTCODE_RE.findall((p.address or "").upper())
    if found:
        pc = found[-1] if isinstance(found[-1], str) else found[-1][0]
        return re.sub(r"\s+", "", pc)
    return re.sub(r"\s+", " ", (p.name or "").strip().lower()) or p.tracking


CSV_COLUMNS = ["Tracking", "Order", "Fulfilment ID", "Name", "Address", "Items", "Stage",
               "Latest update", "Royal Mail status", "Shipped", "Updated", "Last checked", "Tracking link",
               "Paid", "Handed over", "Note"]


def csv_bytes(parcels) -> bytes:
    """All parcels as a CSV (UTF-8 with BOM so Excel opens it cleanly)."""
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(CSV_COLUMNS)
    for p in sorted(parcels, key=lambda p: p.shipped_at, reverse=True):
        w.writerow([p.tracking, p.order, p.fulfilment, p.name, p.address, p.items, p.stage, p.detail, p.rm_status,
                    local_time(p.shipped_at), local_time(p.updated_at), local_time(p.last_checked),
                    NARVAR_URL.format(carrier=p.carrier or "royalmail-is", tracking=p.tracking),
                    "Yes" if p.paid else "", "Yes" if p.handed else "", p.note])
    return buf.getvalue().encode("utf-8-sig")


def post_file(webhook: str, content: str, filename: str, data: bytes) -> None:
    payload = {"username": APP_NAME, "content": content}
    r = requests.post(webhook, data={"payload_json": json.dumps(payload)},
                      files={"files[0]": (filename, data, "text/csv")}, timeout=30)
    r.raise_for_status()


def post_webhook(webhook: str, payload: dict, picture: tuple[str, bytes] | None = None) -> None:
    payload = {"username": APP_NAME, **payload}
    if picture and payload.get("embeds"):
        name, data = picture
        payload["embeds"][0]["thumbnail"] = {"url": f"attachment://{name}"}
        r = requests.post(webhook, data={"payload_json": json.dumps(payload)},
                          files={"files[0]": (name, data)}, timeout=20)
    else:
        r = requests.post(webhook, json=payload, timeout=15)
    r.raise_for_status()


def send_discord(webhook: str, title: str, parcel: Parcel, detail: str, counts: dict, cfg: dict | None = None) -> None:
    """A new Discord message for each change (sent once per change)."""
    if not webhook:
        return
    cfg = cfg or {}
    payload = _discord_payload(title, parcel, detail, counts, cfg, ping=True)
    post_webhook(webhook, payload, discord_picture(parcel.stage, cfg))


def delivery_postcode(parcel) -> str:
    pcs = POSTCODE_RE.findall((parcel.address or "").upper())
    pc = (pcs[-1] if isinstance(pcs[-1], str) else pcs[-1][0]) if pcs else ""
    pc = re.sub(r"\s+", "", pc)
    return f"{pc[:-3]} {pc[-3:]}" if len(pc) > 4 else pc


RM_TRACK_URL = "https://www.royalmail.com/track-your-item#/tracking-results/{}"
PHOTO_TYPES = (".png", ".jpg", ".jpeg", ".webp")


def delivery_photo_file(tracking: str):
    """The saved delivery photo for this parcel, if there is one in the Delivery photos folder."""
    for ext in PHOTO_TYPES:
        f = PHOTOS_DIR / f"{tracking}{ext}"
        if f.is_file():
            return f
    return None


def send_delivered_with_photo(webhook: str, title: str, parcel, detail: str, counts: dict, cfg: dict, photo) -> None:
    """The normal Delivered alert, with the delivery photo shown big underneath."""
    payload = {"username": APP_NAME, **_discord_payload(title, parcel, detail, counts, cfg, ping=True)}
    files = {}
    pname = f"delivery{photo.suffix.lower()}"
    files["files[0]"] = (pname, photo.read_bytes())
    payload["embeds"][0]["image"] = {"url": f"attachment://{pname}"}
    pic = discord_picture(parcel.stage, cfg)
    if pic:
        files["files[1]"] = pic
        payload["embeds"][0]["thumbnail"] = {"url": f"attachment://{pic[0]}"}
    r = requests.post(webhook, data={"payload_json": json.dumps(payload)}, files=files, timeout=30)
    r.raise_for_status()


def send_delivery_photo(webhook: str, parcel, photo) -> None:
    """A new Discord message with the delivery photo as a big picture."""
    data = photo.read_bytes()
    name = f"delivery{photo.suffix.lower()}"
    when = next((h.get("at", "") for h in reversed(parcel.history) if h.get("stage") == "Delivered"), "")
    embed = {
        "title": f"📸 Delivery photo · {parcel.name or parcel.tracking}",
        "color": STAGE_COLOURS.get("Delivered", 0x2ECC71),
        "fields": [
            {"name": "Tracking", "value": f"[{parcel.tracking}]({RM_TRACK_URL.format(parcel.tracking)})", "inline": True},
            {"name": "📋 Copy", "value": f"```{parcel.tracking}```", "inline": True},
            {"name": "Postcode", "value": delivery_postcode(parcel) or "—", "inline": True},
        ],
        "image": {"url": f"attachment://{name}"},
    }
    if parcel.order:
        embed["fields"].append({"name": "Order", "value": parcel.order, "inline": True})
    if when:
        embed["footer"] = {"text": f"Delivered {local_time(when)}"}
    payload = {"username": APP_NAME, "embeds": [embed]}
    r = requests.post(webhook, data={"payload_json": json.dumps(payload)},
                      files={"files[0]": (name, data)}, timeout=30)
    r.raise_for_status()


def _discord_payload(title: str, parcel: Parcel, detail: str, counts: dict, cfg: dict, ping: bool) -> dict:
    embed = {
        "title": title,
        "color": STAGE_COLOURS.get(parcel.stage, 0x999999),
        "fields": [
            {"name": "Tracking", "value": f"[{parcel.tracking}](https://www.royalmail.com/track-your-item#/tracking-results/{parcel.tracking})", "inline": True},
            {"name": "📋 Copy", "value": f"```{parcel.tracking}```", "inline": True},
            {"name": "Stage", "value": nice_stage(parcel.stage), "inline": True},
            {"name": "Order", "value": parcel.order or "-", "inline": True},
            {"name": "Update", "value": detail[:1000] or "-", "inline": False},
        ],
        "footer": {"text": f"Shipped {counts['total']} · Awaiting scan {counts['waiting']} · At PC hub {counts['hub']} · "
                           f"Moving {counts['moving']} · Out for delivery {counts.get('ofd', 0)} · Delivered {counts['delivered']}"},
        "timestamp": now_iso(),
    }
    if parcel.name or parcel.address:
        embed["fields"].append({"name": "Ship to", "value": f"{parcel.name}\n{parcel.address}".strip()[:1000], "inline": False})
    if parcel.items:
        embed["fields"].append({"name": "Items", "value": parcel.items[:1000], "inline": False})
    marks = " · ".join(x for x in ("💷 Paid" if parcel.paid else "", "🤝 Handed over" if parcel.handed else "",
                                   parcel.note) if x)
    if marks:
        embed["fields"].append({"name": "Your notes", "value": marks[:1000], "inline": False})
    if parcel.stage == "Delivered" and delivery_photo_file(parcel.tracking):
        embed["fields"].append({"name": "📸 Delivery photo", "inline": False, "value": "Below ⬇️"})
    elif parcel.stage == "Delivered":
        pc = delivery_postcode(parcel)
        embed["fields"].append({"name": "📸 Delivery photo", "inline": False, "value": (
            f"[Open on Royal Mail](https://www.royalmail.com/track-your-item#/tracking-results/{parcel.tracking})"
            + (f" · it asks for the postcode: **{pc}**" if pc else " · it asks for the delivery postcode")
            + "\n(Royal Mail only shows a photo if the postie took one.)")})
    if parcel.stage == "Delivery attempted" and (cfg or {}).get("rebook", True):
        embed["fields"].append({"name": "📮 Rebook", "value": rebook_text(parcel)[:1000], "inline": False})
    payload = {"embeds": [embed]}
    who = (cfg or {}).get("ping", "").strip()
    if ping and who and parcel.stage == "Delivery attempted":
        payload["content"] = f"{who} 🔔 Delivery attempted for {parcel.name or parcel.tracking}! Check for a card or rebook."
        payload["allowed_mentions"] = {"parse": ["everyone", "users", "roles"]}
    return payload


# --------------------------------------------------------------------------
# Tracker engine (no GUI code, so it can be tested on its own)
# --------------------------------------------------------------------------

class Tracker:
    def __init__(self, notify=lambda kind, text: None):
        self.notify = notify
        raw = load_json(STATE_FILE, {})
        self.lock = threading.RLock()
        self.parcels: dict[str, Parcel] = {k: Parcel(**{f: v[f] for f in v if f in Parcel.__dataclass_fields__})
                                           for k, v in raw.items()}
        self.page_errors = 0
        self.first_run = not raw
        for p in self.parcels.values():  # older versions had a single "In transit" stage
            if p.stage == "In transit":
                scan = "" if (p.rm_status or "").startswith("No Royal Mail") else (p.rm_status or "")
                p.stage = stage_from_text(scan) if scan else "Shipped"
        self.quiet_once = False
        self.held = load_json(PHOTO_HOLD_FILE, {})   # tracking -> {title, detail, at}
        for p in self.parcels.values():  # v2.0-2.3 misread the tracking page: start those parcels again
            bad = p.rm_status and ("Show Full History" in p.rm_status or p.rm_status.startswith("Tracking Number:")
                                   or re.match(r"(?i)today \d", p.rm_status))
            if bad and not p.done and p.stage not in ("Out for delivery", "Delivery attempted"):
                p.sent = [k for k in p.sent if not (k.startswith("stage:") and k != "stage:Shipped") and not k.startswith("scan:")]
                p.stage, p.rm_status, p.detail = "Shipped", "", "Re-checking tracking page"
                self.quiet_once = True
        for p in self.parcels.values():  # re-sort earlier guesses with the current rules
            self._resort(p)
        for p in self.parcels.values():  # parcels saved by older versions: remember what was already alerted
            if not p.sent:
                p.sent = [f"stage:{h.get('stage')}" for h in p.history] + [f"stage:{p.stage}"]
                p.sent += [f"scan:{x}" for x in (p.rm_status, p.detail) if x]

    def counts(self) -> dict:
        ps = list(self.parcels.values())
        return {"total": len(ps),
                "waiting": sum(p.stage == "Shipped" for p in ps),
                "hub": sum(p.stage == "Dispatched" for p in ps),
                "moving": sum(p.stage in MOVING for p in ps),
                "ofd": sum(p.stage in ("Out for delivery", "Delivery attempted") for p in ps),
                "delivered": sum(p.done for p in ps)}

    def archive(self, parcels: list) -> None:
        with self.lock:
            arch = load_json(ARCHIVE_FILE, {})
            for p in parcels:
                arch[p.tracking] = asdict(p)
            save_json(ARCHIVE_FILE, arch)
        self.notify("info", f"Moved {len(parcels)} parcel(s) older than {KEEP_DAYS} days to History.")

    def history_parcels(self) -> list:
        out = []
        for v in load_json(ARCHIVE_FILE, {}).values():
            try:
                out.append(Parcel(**{k: v[k] for k in v if k in Parcel.__dataclass_fields__}))
            except TypeError:
                pass
        return out

    def save(self):
        with self.lock:
            data = {k: asdict(v) for k, v in list(self.parcels.items())}
            save_json(STATE_FILE, data)
        try:  # diagnostics copy next to the app
            save_json(Path(__file__).with_name("parcels_debug.json"), data)
        except Exception:
            pass

    def _resort(self, p: "Parcel", scan: str = "", location: str = "") -> bool:
        """Correct a parcel that an earlier version put too far along (e.g. 'awaiting
        carrier pickup' shown as 'At mail centre'). Quiet: no Discord alert. Also forgets
        the wrong alert so the real one still goes out later."""
        scan = scan or ("" if (p.rm_status or "").startswith("No Royal Mail") else (p.rm_status or ""))
        if not scan or p.stage not in MOVING:
            return False
        right = stage_from_text(scan.split(" - ")[0], location or (scan.split(" - ")[1].split(" (")[0] if " - " in scan else ""))
        if stage_rank(right) >= stage_rank(p.stage):
            return False
        wrong = [x for x in STAGES if stage_rank(x) > stage_rank(right)]
        p.sent = [k for k in p.sent if k not in {f"stage:{x}" for x in wrong}]
        p.history.append({"at": now_iso(), "stage": right, "detail": f"Corrected: {scan}", "source": "fix"})
        p.stage, p.detail = right, scan
        self.notify("info", f"{p.tracking}: corrected to {right} ({scan})")
        return True

    def groups(self) -> dict:
        out: dict = {}
        for p in self.parcels.values():
            out.setdefault(customer_key(p), []).append(p)
        return out

    def check_customers(self, cfg: dict) -> list:
        """One alert when every parcel for a customer (2 or more) has been delivered."""
        done = []
        for key, ps in self.groups().items():
            n = len(ps)
            if n < 2 or not all(p.done for p in ps):
                continue
            tag = f"alldone:{n}"
            if all(tag in p.sent for p in ps):
                continue
            for p in ps:
                if tag not in p.sent:
                    p.sent.append(tag)
            done.append(ps)
            if self.first_run or not cfg.get("customer_alerts", True):
                continue
            name = ps[0].name or ps[0].tracking
            self.notify("update", f"All {n} parcels for {name} delivered")
            self.notify("alert", f"All {n} parcels delivered\n{name}")
            if cfg.get("discord"):
                embed = {"title": f"🎉 All {n} parcels delivered for {name}", "color": STAGE_COLOURS["Delivered"],
                         "description": "\n".join(f"`{p.tracking}` · {p.order or '-'} · {local_time(p.updated_at)}"
                                                  for p in ps)[:4000],
                         "footer": {"text": ps[0].address[:200] or " "}, "timestamp": now_iso()}
                try:
                    post_webhook(cfg["discord"], {"embeds": [embed]}, discord_picture("Delivered", cfg))
                except Exception as e:
                    self.notify("error", f"Discord post failed: {e}")
        return done

    def check_stuck(self, cfg: dict) -> list:
        """Alert once (one combined Discord message) for parcels that stopped moving.
        A parcel alerts again only if it moves and then gets stuck again."""
        days = cfg.get("stuck_days", 3)
        fresh = []
        for p in self.parcels.values():
            if not is_stuck(p, days):
                continue
            key = f"stuck:{p.stage}:{int(last_moved(p))}"
            if key in p.sent:
                continue
            p.sent.append(key)
            fresh.append(p)
        if not fresh or self.first_run:
            return fresh
        names = ", ".join(p.name or p.tracking for p in fresh[:5]) + ("…" if len(fresh) > 5 else "")
        self.notify("update", f"{len(fresh)} parcel(s) haven't moved in {days}+ days: {names}")
        self.notify("alert", f"{len(fresh)} parcel(s) not moving\n{names}")
        if cfg.get("discord"):
            embed = {"title": f"⚠ {len(fresh)} parcel{'s' if len(fresh) > 1 else ''} not moved in {days}+ days",
                     "color": 0xD62828, "timestamp": now_iso(),
                     "description": "\n".join(f"`{p.tracking}` **{p.name or '?'}** · {nice_stage(p.stage)} · "
                                              f"last change {days_since(p)} days ago\n↳ {(p.rm_status or p.detail or '')[:120]}"
                                              for p in fresh[:20])[:4000]}
            try:
                post_webhook(cfg["discord"], {"embeds": [embed]}, discord_picture("Delivery attempted", cfg))
            except Exception as e:
                self.notify("error", f"Discord post failed: {e}")
        return fresh

    def _advance(self, p: Parcel, stage: str, detail: str, at: str, cfg: dict, source: str = "email") -> bool:
        """Record a change and alert Discord at most once per event.

        - A stage (Shipped / Out for delivery / Delivered) is alerted only once per
          parcel, whether it first arrives by email or from the tracking page.
        - While moving (With Royal Mail / mail centre / delivery office), each new scan from the tracking page (a new depot or
          mail centre) is alerted once.
        - A parcel never moves backwards, and an email never overwrites a newer
          tracking-page scan.
        """
        if source == "page" and stage_rank(stage) < stage_rank(p.stage) and p.stage in MOVING:
            p.rm_status = detail
            self._resort(p, detail)
            return False
        if stage_rank(stage) < stage_rank(p.stage):
            return False
        stage_key, scan_key = f"stage:{stage}", f"scan:{detail}"
        new_stage = stage_rank(stage) > stage_rank(p.stage) or stage_key not in p.sent
        new_scan = source == "page" and scan_key not in p.sent
        if source == "page":
            p.rm_status = detail
        if not (new_stage or new_scan):
            return False
        if stage == p.stage and source == "email":
            p.sent.append(stage_key)  # same stage already known from the tracking page
            return False

        changed_stage = stage != p.stage
        p.stage, p.detail, p.updated_at = stage, detail, at
        p.history.append({"at": at, "stage": stage, "detail": detail, "source": source})
        send = stage_key not in p.sent or (stage in MOVING and new_scan)
        for k in (stage_key, scan_key):
            if k not in p.sent:
                p.sent.append(k)
        if not send:
            return False
        self.notify("update", f"{p.tracking}: {stage} - {detail}")
        if not (self.first_run or self.quiet_once):
            nice = {"Shipped": "Awaiting scan", "Dispatched": "At Pokémon Center hub", "At mail centre": "At Royal Mail hub"}.get(stage, stage)
            title = f"📦 Parcel update: {nice}" if changed_stage or stage not in MOVING else "📍 Parcel moved"
            self.notify("alert", f"{title.split(' ', 1)[1]}\n{p.name or p.tracking}: {detail}")
            if stage == "Delivered" and cfg.get("discord") and not delivery_photo_file(p.tracking):
                # hold the Discord alert until the Royal Mail delivery photo is fetched (or PHOTO_WAIT_HOURS pass)
                with self.lock:
                    self.held[p.tracking] = {"title": title, "detail": detail, "at": now_iso()}
                    save_json(PHOTO_HOLD_FILE, self.held)
                self.notify("info", f"{p.tracking} delivered: Discord alert waits for the delivery photo (up to {PHOTO_WAIT_HOURS} h).")
                return True
            try:
                send_discord(cfg.get("discord", ""), title, p, detail, self.counts(), cfg)
            except Exception as e:
                self.notify("error", f"Discord post failed: {e}")
        return True

    def run_once(self, cfg: dict) -> None:
        # 1) Emails
        emails = list(fetch_pokemon_emails(cfg["imap_host"], cfg["email"], cfg["password"], KEEP_DAYS,
                                           log=lambda m: self.notify("info", m)))
        shipping = sum(1 for subj, b, d in emails if (classify(subj, b) or ("",))[0] == "Shipped")
        self.notify("info", f"{shipping} shipping emails, {len(emails) - shipping} other Pokémon Center emails")
        status_emails = []
        for subject, body, date_iso in emails:
            kind = classify(subject, body)
            if kind and kind[0] == "Shipped":
                found = parse_shipping_email(subject, body, date_iso)
                if not found:
                    self.notify("error", f"No tracking number found in '{subject}' ({local_time(date_iso)})")
                for p in found:
                    if not p.name:
                        self.notify("error", f"Couldn't read the shipping address in '{subject}' ({local_time(date_iso)})")
                    old = self.parcels.get(p.tracking)
                    if old and p.name and (old.name, old.address) != (p.name, p.address):
                        old.name, old.address = p.name, p.address
                        self.notify("info", f"{p.tracking}: ship to {p.name}")
                    if p.tracking not in self.parcels:
                        p.sent.append("stage:Shipped")
                        self.parcels[p.tracking] = p
                        self.notify("new", f"New shipment {p.tracking} (order {p.order or '?'})")
                        if not (self.first_run or self.quiet_once):
                            self.notify("alert", f"New Pokémon Center shipment\n{p.name or p.tracking} ({p.tracking})")
                            try:
                                send_discord(cfg.get("discord", ""), "🚚 New Pokémon Center shipment", p, p.detail, self.counts(), cfg)
                            except Exception as e:
                                self.notify("error", f"Discord post failed: {e}")
            elif kind:
                status_emails.append((kind, body, date_iso))

        # Narvar status emails: match by tracking number, else order/fulfilment id
        for (stage, detail), body, date_iso in status_emails:
            flat = unescape(body)
            hits = [t for t in TRACKING_RE.findall(flat) if t in self.parcels]
            if not hits:
                ids = set(re.findall(r"\b([A-Z]?\d{6,})\b", flat))
                hits = [t for t, p in self.parcels.items() if (p.order and p.order in ids) or (p.fulfilment and p.fulfilment in ids)]
            for t in hits:
                self._advance(self.parcels[t], stage, detail, date_iso, cfg)

        # Parcels that shipped more than KEEP_DAYS ago move to the History tab
        cutoff = time.time() - KEEP_DAYS * 86400
        old = []
        for t, p in list(self.parcels.items()):
            try:
                if datetime.fromisoformat(p.shipped_at).timestamp() < cutoff:
                    old.append(self.parcels.pop(t))
            except ValueError:
                pass
        if old:
            self.archive(old)

        # 2) Latest Royal Mail scan for parcels still moving
        cid, csec = cfg.get("rm_id", ""), cfg.get("rm_secret", "")
        live = errors = 0
        last_err = ""
        for p in list(self.parcels.values()):
            if p.done:
                continue
            live += 1
            p.last_checked = now_iso()
            try:
                if cid and csec:
                    res = royal_mail_status(p.tracking, cid, csec)
                elif cfg.get("ship24"):
                    res = ship24_status(p.tracking, cfg["ship24"])
                else:
                    res = narvar_status(p.tracking, p.carrier)
                if res:
                    self._advance(p, res[0], res[1], now_iso(), cfg, source="page")
                elif not p.rm_status:
                    p.rm_status = "No Royal Mail scans yet"
            except Exception as e:
                errors += 1
                last_err = str(e)
                self.notify("error", f"Tracking check failed for {p.tracking}: {e}")
            time.sleep(2)
        self.page_errors = errors if live and errors == live else 0

        self.check_stuck(cfg)
        self.check_customers(cfg)
        if self.quiet_once:
            self.notify("info", "Re-sorted all parcels with the fixed tracking-page reader (no Discord alerts for this).")
            self.quiet_once = False
        if self.first_run:
            c = self.counts()
            self.notify("info", f"First scan done: {c['total']} shipments found, {c['delivered']} delivered. "
                                "Discord alerts start from the next change.")
            self.first_run = False
        self.save()
        if self.page_errors:
            raise RuntimeError(f"Couldn't read the tracking page for any of {live} parcels ({last_err[:150]})")


# --------------------------------------------------------------------------
# Windows helpers: start with Windows, keep awake
# --------------------------------------------------------------------------

RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"


def set_autostart(on: bool) -> None:
    """Add/remove the app from Windows' 'start when I sign in' list (your user only)."""
    import winreg
    exe = Path(sys.executable)
    if exe.with_name("pythonw.exe").exists():
        exe = exe.with_name("pythonw.exe")  # no black console window
    cmd = f'"{exe}" "{Path(__file__).resolve()}" --autostart'
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
        if on:
            winreg.SetValueEx(k, "SIDsSortingCenter", 0, winreg.REG_SZ, cmd)
        else:
            try:
                winreg.DeleteValue(k, "SIDsSortingCenter")
            except FileNotFoundError:
                pass


def icon_file() -> Path:
    """The Poké Ball-style .ico, written to the data folder (used for the window, taskbar and shortcuts)."""
    p = DATA_DIR / "SIDs Sorting Center.ico"
    data = base64.b64decode(ICON_ICO)
    try:
        if not p.exists() or p.stat().st_size != len(data):
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
    except OSError:
        pass
    return p


def set_window_icon(win) -> None:
    """Window + taskbar icon. The .ico (classic bitmap format, which Tk can read) goes first,
    then the sharp 256 px picture on top for high-DPI screens."""
    import tkinter as tk
    if os.name == "nt":
        try:
            win.iconbitmap(default=str(icon_file()))
        except Exception as e:
            print(f"icon: iconbitmap failed: {e}", file=sys.stderr)
    try:
        big = tk.PhotoImage(data=ICON_PNG)
        win._icon_imgs = [big, big.subsample(4, 4), big.subsample(8, 8)]  # 256, 64, 32 px
        win.iconphoto(True, *win._icon_imgs)
    except Exception as e:
        print(f"icon: iconphoto failed: {e}", file=sys.stderr)
    if os.name == "nt":
        win.after(50, lambda: win32_set_icon(win))
        win.after(1500, lambda: win32_set_icon(win))  # again once the window is fully shown


def win32_set_icon(win) -> None:
    """Hand the .ico straight to Windows for the title bar and taskbar (most reliable way)."""
    try:
        import ctypes
        from ctypes import wintypes
        u32 = ctypes.windll.user32
        u32.LoadImageW.restype = ctypes.c_void_p
        u32.LoadImageW.argtypes = [wintypes.HINSTANCE, wintypes.LPCWSTR, wintypes.UINT, ctypes.c_int, ctypes.c_int, wintypes.UINT]
        u32.SendMessageW.restype = ctypes.c_void_p
        u32.SendMessageW.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, ctypes.c_void_p]
        u32.GetParent.restype = wintypes.HWND
        u32.GetParent.argtypes = [wintypes.HWND]
        win.update_idletasks()
        hwnd = int(win.wm_frame(), 16) or u32.GetParent(win.winfo_id())
        path = str(icon_file())
        LR_LOADFROMFILE, IMAGE_ICON, WM_SETICON = 0x10, 1, 0x80
        big = u32.LoadImageW(None, path, IMAGE_ICON, u32.GetSystemMetrics(11), u32.GetSystemMetrics(12), LR_LOADFROMFILE)
        small = u32.LoadImageW(None, path, IMAGE_ICON, u32.GetSystemMetrics(49), u32.GetSystemMetrics(50), LR_LOADFROMFILE)
        if not (big and small):
            print(f"icon: LoadImage failed ({ctypes.GetLastError()})", file=sys.stderr)
            return
        u32.SendMessageW(hwnd, WM_SETICON, 1, big)    # ICON_BIG: taskbar / Alt+Tab
        u32.SendMessageW(hwnd, WM_SETICON, 0, small)  # ICON_SMALL: title bar
        win._hicons = (big, small)
    except Exception as e:
        print(f"icon: win32 set failed: {e}", file=sys.stderr)


def make_shortcuts() -> list[str]:
    """Desktop + Start menu shortcuts with the Poké Ball icon (no console window)."""
    import subprocess
    exe = Path(sys.executable)
    if exe.with_name("pythonw.exe").exists():
        exe = exe.with_name("pythonw.exe")
    script = Path(__file__).resolve()
    q = lambda s: "'" + str(s).replace("'", "''") + "'"
    ps = (
        "$w = New-Object -ComObject WScript.Shell; $out = @(); "
        "foreach ($dir in @([Environment]::GetFolderPath('Desktop'), [Environment]::GetFolderPath('Programs'))) { "
        f"$l = $w.CreateShortcut((Join-Path $dir {q(APP_NAME + '.lnk')})); "
        f"$l.TargetPath = {q(exe)}; $l.Arguments = {q(chr(34) + str(script) + chr(34))}; "
        f"$l.WorkingDirectory = {q(script.parent)}; $l.IconLocation = {q(str(icon_file()) + ',0')}; "
        f"$l.Description = {q(APP_NAME)}; $l.Save(); $out += $l.FullName }}; $out"
    )
    r = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps], capture_output=True, text=True,
                       timeout=60, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    if r.returncode != 0:
        raise RuntimeError((r.stderr or r.stdout).strip()[:400])
    return [line for line in r.stdout.splitlines() if line.strip()]


def keep_awake(on: bool) -> None:
    """Stop Windows going to sleep while tracking (the screen can still turn off)."""
    try:
        import ctypes
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000000 | (0x00000001 if on else 0))
    except Exception:
        pass


# --------------------------------------------------------------------------
# GUI
# --------------------------------------------------------------------------

def run_gui():
    import tkinter as tk
    from tkinter import ttk, messagebox, filedialog
    import csv
    import webbrowser

    # ---- Palette: Poké Ball red / white with type-style colours per stage
    # ---- Palette: dark neon ("sorting center from the future")
    BG, PANEL, RAISED, DEEP, FIELD = "#05070F", "#0C1322", "#16223A", "#03050B", "#081020"
    TEXT, ON, MUTED, EDGE = "#E4EEFF", "#F4F8FF", "#7D8BA8", "#1E2C4A"
    NEON, PINK, RED, RED_DARK = "#00E5FF", "#FF2E97", "#FF3D57", "#7A1426"
    YELLOW, BLUE, YELLOW_DARK = "#FFD60A", "#4D7CFF", "#FFC300"
    LINE = EDGE

    def blend(c1, c2, t):
        a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
        b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
        return "#%02x%02x%02x" % tuple(int(x + (y - x) * t) for x, y in zip(a, b))

    _stage_neon = {
        "Shipped":            ("#4D8DFF", "📦 AWAITING SCAN"),
        "Dispatched":         ("#FF7A1A", "🏬 AT POKÉMON CENTER HUB"),
        "With Royal Mail":    ("#00E5D1", "📮 WITH ROYAL MAIL"),
        "At mail centre":     ("#FFB000", "🏭 AT ROYAL MAIL HUB"),
        "At delivery office": ("#FF4FA3", "🏤 AT DELIVERY OFFICE"),
        "Out for delivery":   ("#B266FF", "🛵 OUT FOR DELIVERY"),
        "Delivery attempted": ("#FFD60A", "🔔 DELIVERY ATTEMPTED"),
        "Delivered":          ("#39FF88", "✅ DELIVERED"),
    }
    STAGE_STYLE = {k: (c, blend(PANEL, c, 0.14), t) for k, (c, t) in _stage_neon.items()}  # colour, dark tint, badge
    FONT = "Segoe UI"

    settings = load_json(SETTINGS_FILE, {})
    try:
        import_pictures(settings)
    except Exception:
        traceback.print_exc()
    events: queue.Queue = queue.Queue()
    tracker = Tracker(notify=lambda kind, text: events.put((kind, text)))
    stop_flag = threading.Event()
    worker: dict = {"thread": None}

    # Only one copy at a time, so you never look at an old window by mistake
    import socket
    autostart = "--autostart" in sys.argv
    def vnum(v):
        try:
            return tuple(int(x) for x in v.split("."))
        except ValueError:
            return (0,)

    def grab_lock():
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            s.bind(("127.0.0.1", 47613))
            s.listen(2)
            return s
        except OSError:
            s.close()
            return None

    lock = grab_lock()
    if lock is None and "--restarted" in sys.argv:   # the old copy is just closing; wait for it
        for _ in range(60):
            time.sleep(0.25)
            lock = grab_lock()
            if lock:
                break
    if lock is None:
        # Another copy is running (maybe hidden in the tray). If it's an older version it closes itself
        # so this newer one takes over; otherwise it just comes to the front.
        reply = b""
        try:
            with socket.create_connection(("127.0.0.1", 47613), timeout=3) as c:
                c.sendall(f"show {VERSION}".encode())
                reply = c.recv(16)
        except OSError:
            pass
        if reply == b"ok":
            return
        if reply == b"bye":
            for _ in range(40):
                time.sleep(0.25)
                lock = grab_lock()
                if lock:
                    break
    if lock is None:
        if autostart:
            return
        r = tk.Tk(); r.withdraw()
        messagebox.showwarning(APP_NAME, "SID's Sorting Center is already open.\n\n"
                               "It may be hidden in the system tray (bottom-right, near the clock): right-click the ball icon › Quit, then open it again.")
        return

    try:  # own taskbar button + icon instead of Python's
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("SIDsSortingCenter.App")
    except Exception:
        pass
    root = tk.Tk()
    root._lock = lock
    try:  # a sleeker, techier built-in Windows font when available
        from tkinter import font as tkfont
        if "Bahnschrift" in tkfont.families(root):
            FONT = "Bahnschrift"
    except Exception:
        pass

    def lock_server():
        while True:
            try:
                c, _ = lock.accept()
                with c:
                    c.settimeout(2)
                    msg = c.recv(32).decode(errors="ignore").split()
                    if msg and msg[0] == "show":
                        if len(msg) > 1 and vnum(msg[1]) > vnum(VERSION):
                            c.sendall(b"bye")  # a newer version was started: hand over to it
                            try:
                                c.recv(16)  # let the other side hang up first, so the port frees at once
                            except OSError:
                                pass
                            events.put(("tray", "quit"))
                            continue
                        c.sendall(b"ok")
                        events.put(("tray", "show"))
                        try:
                            c.recv(16)  # let the other side hang up first, so the port stays free
                        except OSError:
                            pass
            except OSError:
                return
    threading.Thread(target=lock_server, daemon=True).start()
    root.title(f"{APP_NAME}  v{VERSION}")
    root.geometry(f"{min(1440, root.winfo_screenwidth() - 40)}x{min(980, root.winfo_screenheight() - 80)}+10+10")
    set_window_icon(root)
    root.minsize(1000, 640)
    root.configure(bg=BG)

    style = ttk.Style(root)
    style.theme_use("clam")
    style.configure(".", background=BG, foreground=TEXT, font=(FONT, 10))
    style.configure("Treeview", background=PANEL, fieldbackground=PANEL, foreground=TEXT, rowheight=34,
                    borderwidth=0, font=(FONT, 10))
    style.configure("Treeview.Heading", background=DEEP, foreground=ON, font=(FONT, 9, "bold"),
                    relief="flat", padding=(8, 7))
    style.map("Treeview.Heading", background=[("active", RAISED)])
    style.configure("Treeview.Heading", foreground=NEON)
    style.configure("TCheckbutton", background=PANEL, foreground=TEXT)
    style.configure("TNotebook", bordercolor=EDGE, lightcolor=EDGE, darkcolor=EDGE)
    style.configure("TNotebook.Tab", bordercolor=EDGE, lightcolor=PANEL, darkcolor=PANEL)
    style.configure("Treeview", bordercolor=EDGE, lightcolor=EDGE, darkcolor=EDGE)
    style.configure("Vertical.TScrollbar", bordercolor=EDGE, lightcolor=RAISED, darkcolor=RAISED, arrowcolor=NEON,
                    background=RAISED, troughcolor=DEEP)
    style.map("Vertical.TScrollbar", background=[("active", "#24406B")])
    style.configure("TEntry", lightcolor=EDGE, darkcolor=EDGE)
    style.map("Treeview", background=[("selected", "#0B4F63")], foreground=[("selected", NEON)])
    style.configure("TNotebook", background=BG, borderwidth=0, tabmargins=(16, 8, 16, 0))
    style.configure("TNotebook.Tab", background=PANEL, foreground=MUTED, padding=(22, 9),
                    font=(FONT, 10, "bold"), borderwidth=0)
    style.map("TNotebook.Tab", background=[("selected", RAISED)], foreground=[("selected", NEON)])
    style.configure("TEntry", fieldbackground=FIELD, foreground=TEXT, insertcolor=NEON, bordercolor=LINE,
                    lightcolor=LINE, darkcolor=LINE, padding=7)
    style.map("TEntry", bordercolor=[("focus", NEON)], lightcolor=[("focus", NEON)])
    style.configure("Vertical.TScrollbar", background=RAISED, troughcolor=BG, borderwidth=0, arrowsize=12)
    style.configure("TCombobox", fieldbackground=FIELD, background=RAISED, foreground=TEXT, arrowcolor=NEON,
                    bordercolor=EDGE, lightcolor=EDGE, darkcolor=EDGE, selectbackground=FIELD, selectforeground=TEXT)
    style.map("TCombobox", fieldbackground=[("readonly", FIELD)], foreground=[("readonly", TEXT)],
              selectbackground=[("readonly", FIELD)], selectforeground=[("readonly", TEXT)],
              bordercolor=[("focus", NEON)])
    root.option_add("*TCombobox*Listbox.background", FIELD)
    root.option_add("*TCombobox*Listbox.foreground", TEXT)
    root.option_add("*TCombobox*Listbox.selectBackground", "#0B4F63")
    root.option_add("*TCombobox*Listbox.selectForeground", NEON)

    def shade(hex_colour, factor=0.85):
        r, g, b = (int(hex_colour[i:i + 2], 16) for i in (1, 3, 5))
        return "#%02x%02x%02x" % (int(r * factor), int(g * factor), int(b * factor))

    def bright(c):
        r, g, b = (int(c[i:i + 2], 16) for i in (1, 3, 5))
        return 0.299 * r + 0.587 * g + 0.114 * b > 150

    def button(parent, text, bg, cmd=None, fg=ON, size=10, padx=16, pady=8):
        if fg == ON and bright(bg):
            fg = DEEP
        b = tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg, activebackground=shade(bg),
                      activeforeground=fg, relief="flat", bd=0, cursor="hand2",
                      font=(FONT, size, "bold"), padx=padx, pady=pady)
        b.bind("<Enter>", lambda e: b.configure(bg=shade(bg, 0.92)))
        b.bind("<Leave>", lambda e: b.configure(bg=bg))
        return b

    def card(parent, **kw):
        # dark glass panel with a thin glowing edge
        return tk.Frame(parent, bg=PANEL, highlightbackground="#22406E", highlightcolor="#22406E",
                        highlightthickness=1, **kw)

    def pokeball(cv, x, y, r, top=RED, outline=DEEP):
        """A simple red-and-white ball drawn from shapes."""
        w = max(2, r // 6)
        cv.create_oval(x - r, y - r, x + r, y + r, fill="#EAF2FF", outline=outline, width=w)
        cv.create_arc(x - r, y - r, x + r, y + r, start=0, extent=180, fill=top, outline=outline, width=w)
        cv.create_line(x - r, y, x + r, y, fill=outline, width=w)
        cv.create_oval(x - r * .32, y - r * .32, x + r * .32, y + r * .32, fill="#EAF2FF", outline=outline, width=w)
        cv.create_oval(x - r * .14, y - r * .14, x + r * .14, y + r * .14, fill="#EAF2FF", outline=outline, width=max(1, w // 2))

    # ---- Pictures: built-in mascots (original characters) + your own header picture
    images: dict = {}

    def mascot(stage, size=64):
        mine = (settings.get("stage_pics") or {}).get(stage) or ""
        if mine and mine not in ("mascot", "turns") and (PICS_DIR / mine).is_file():
            img = picture_fit(str(PICS_DIR / mine), size, size)
            if img:
                return img
        key = (stage, size)
        if key not in images:
            try:
                img = tk.PhotoImage(data=MASCOTS.get(stage) or MASCOTS["Shipped"])  # 128 px
                f = max(1, round(128 / size))
                images[key] = img.subsample(f, f) if f > 1 else img
            except Exception:
                images[key] = None
        return images[key]

    def picture_fit(path, max_h, max_w=420):
        """Load a PNG/GIF and shrink it (whole steps) to fit."""
        key = ("file", path, max_h)
        if key not in images:
            images[key] = None
            try:
                from PIL import Image, ImageTk
                with Image.open(path) as im:
                    im = im.convert("RGBA")
                    im.thumbnail((max_w, max_h))
                    images[key] = ImageTk.PhotoImage(im)
            except Exception:
                try:
                    img = tk.PhotoImage(file=path)
                    f = max(1, -(-img.height() // max_h), -(-img.width() // max_w))
                    images[key] = img.subsample(f, f) if f > 1 else img
                except Exception:
                    images[key] = None
        return images[key]

    look = {"header_image": settings.get("header_image", ""), "header_pic": settings.get("header_pic", "mascots")}

    def header_picture():
        """Your header picture: one from 'My pictures', a new one every 20 s ('turns'), or the old file pick."""
        pics = library_pictures() if look["header_pic"] not in ("", "mascots") else []
        if pics:
            if look["header_pic"] == "turns":
                return picture_fit(str(pics[int(time.time() // 20) % len(pics)]), 84)
            for p in pics:
                if p.name == look["header_pic"]:
                    return picture_fit(str(p), 84)
        return picture_fit(look["header_image"], 84) if look["header_image"] else None

    # ---- System tray icon (needs the pystray + pillow packages; skipped quietly if missing)
    tray = {"icon": None, "hint_shown": False}

    def start_tray():
        try:
            import pystray
            from PIL import Image
            import io
            img = Image.open(io.BytesIO(base64.b64decode(ICON_PNG)))
            menu = pystray.Menu(
                pystray.MenuItem("Open SID's Sorting Center", lambda *a: events.put(("tray", "show")), default=True),
                pystray.MenuItem("Check now", lambda *a: events.put(("tray", "check"))),
                pystray.MenuItem("Send daily summary now", lambda *a: events.put(("tray", "summary"))),
                pystray.MenuItem("Quit", lambda *a: events.put(("tray", "quit"))))
            icon = pystray.Icon("SIDsSortingCenter", img, APP_NAME, menu)
            threading.Thread(target=icon.run, daemon=True).start()
            tray["icon"] = icon
        except Exception as e:
            events.put(("info", f"Tray icon not available ({e.__class__.__name__}). Run the Start .bat once to install it."))

    def toast(text):
        if not settings.get("toasts", True) or not tray["icon"]:
            return
        title, _, body = text.partition("\n")
        try:
            tray["icon"].notify(body[:250] or " ", f"{APP_NAME}: {title}"[:63])
        except Exception:
            pass

    # ================= Header =================
    header = tk.Canvas(root, height=92, bg=DEEP, highlightthickness=0)
    header.pack(fill="x")
    status_var = tk.StringVar(value="● Stopped")
    phone = {"srv": None, "last": "", "status": "Stopped", "ip_link": "", "name_link": ""}   # what the phone page shows (plain values, thread-safe)

    import math
    anim = {"t": 0.0}

    def ball3d(cv, x, y, r, angle):
        """A spinning, shaded ball: rotating band + highlight so it reads as 3D."""
        cv.create_oval(x - r + 3, y - r + 5, x + r + 3, y + r + 5, fill="#000000", outline="")  # drop shadow
        cv.create_oval(x - r, y - r, x + r, y + r, fill="#DDE7FF", outline=DEEP, width=3)
        cv.create_arc(x - r, y - r, x + r, y + r, start=angle, extent=180, fill=RED, outline=DEEP, width=3)
        cv.create_oval(x - r * .82, y - r * .82, x + r * .2, y + r * .1, fill="", outline="#FFFFFF", width=0)
        dx, dy = math.cos(math.radians(angle)) * r, -math.sin(math.radians(angle)) * r
        cv.create_line(x - dx, y - dy, x + dx, y + dy, fill=DEEP, width=4)
        cv.create_oval(x - r * .3, y - r * .3, x + r * .3, y + r * .3, fill="#EAF2FF", outline=DEEP, width=3)
        g = 0.5 + 0.5 * math.sin(anim["t"] * 3)
        cv.create_oval(x - r * .13, y - r * .13, x + r * .13, y + r * .13, fill=blend("#9FEFFF", NEON, g), outline="")
        cv.create_oval(x - r * .62, y - r * .72, x - r * .22, y - r * .42, fill=blend(RED, "#FFFFFF", .55), outline="")

    def draw_header(_=None):
        header.delete("all")
        w = max(header.winfo_width(), 400)
        H = 92
        t = anim["t"]
        for i in range(23):  # deep-space gradient
            header.create_rectangle(0, i * 4, w, i * 4 + 4, outline="", fill=blend("#020410", "#0B1B3A", i / 22))
        # perspective "floor" grid that scrolls towards you
        hor, vx = 40, w * 0.62
        for k in range(-14, 15):
            header.create_line(vx + k * 18, hor, vx + k * 150, H, fill="#0E3355")
        for j in range(7):
            f = ((j + (t * 0.9) % 1) / 7) ** 2
            y = hor + f * (H - hor)
            header.create_line(0, y, w, y, fill=blend("#071628", NEON, 0.15 + 0.5 * f))
        header.create_line(0, hor, w, hor, fill=blend(NEON, PINK, 0.5 + 0.5 * math.sin(t)), width=2)
        # sweeping scan beam
        sx = (t * 160) % (w + 300) - 150
        for k, c in enumerate(("#0B2238", "#10385A", "#1A6A92", "#37C8EE")):
            header.create_line(sx - 9 + k * 3, hor, sx - 9 + k * 3 - 30, H - 6, fill=c, width=2)
        # mascot parade, bobbing up and down (or your own picture)
        own = header_picture()
        right = w - 200  # keep clear of the status badge, however wide it gets
        try:
            if status_pill.winfo_ismapped():
                right = min(right, status_pill.winfo_x() - 18)
        except NameError:
            pass
        if own:
            header.create_image(right, 84, image=own, anchor="se")
        else:
            parade = ["Delivered", "Out for delivery", "At delivery office", "At mail centre", "With Royal Mail",
                      "Dispatched", "Shipped"]
            x = right
            for i, st_name in enumerate(parade):
                if x < 520:
                    break
                img = mascot(st_name, 64)
                if img:
                    bob = 4 * math.sin(t * 2.6 + i * 0.9)
                    header.create_oval(x - 52, 80, x - 12, 86, fill="#01030A", outline="")  # shadow
                    header.create_image(x, 82 + bob, image=img, anchor="se")
                x -= 62
        # neon bar along the bottom, colours flowing left to right
        n = 24
        for i in range(n):
            ph = 0.5 + 0.5 * math.sin(t * 1.8 - i / n * 6.28)
            header.create_rectangle(i * w / n, H - 6, (i + 1) * w / n + 1, H, outline="", fill=blend(NEON, PINK, ph))
        ball3d(header, 50, 42, 28, (t * 70) % 360)
        # title with a pulsing glow (3D extruded look)
        glow = blend("#063A4A", NEON, 0.35 + 0.25 * math.sin(t * 2))
        for d in (4, 3, 2):
            header.create_text(94 + d, 30 + d, text="SID'S SORTING CENTER", anchor="w", fill=blend(DEEP, PINK, 0.25 + d * 0.05),
                               font=(FONT, 22, "bold"))
        for ox, oy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            header.create_text(94 + ox, 30 + oy, text="SID'S SORTING CENTER", anchor="w", fill=glow, font=(FONT, 22, "bold"))
        header.create_text(94, 30, text="SID'S SORTING CENTER", anchor="w", fill=ON, font=(FONT, 22, "bold"))
        header.create_text(96, 62, text=f"POKÉMON CENTER PARCEL TRACKER  //  v{VERSION}", anchor="w",
                           fill=NEON, font=(FONT, 9, "bold"))

    def animate():
        try:
            if root.state() in ("normal", "zoomed"):
                anim["t"] += 0.05
                draw_header()
                pulse_widgets()
        except tk.TclError:
            return
        root.after(50, animate)

    def pulse_widgets():
        t = anim["t"]
        g = 0.5 + 0.5 * math.sin(t * 3)
        running = worker["thread"] is not None and worker["thread"].is_alive()
        if running:
            status_pill.configure(bg=blend("#063D24", "#0FA958", g), fg=ON)
        else:
            status_pill.configure(bg=RAISED, fg=MUTED)
        for w_ in pulse_edges:
            try:
                sel = int(w_.cget("highlightthickness")) > 1   # the counter you clicked stays lit
                w_.configure(highlightbackground=NEON if sel else blend("#1B355E", NEON, 0.15 + 0.35 * g))
            except tk.TclError:
                pass
        p = current.get("p")
        if p and journey_pos.get("x") is not None:
            journey.delete("pulse")
            r = 12 + 10 * ((t * 1.2) % 1)
            col = blend(STAGE_STYLE.get(p.stage, (NEON,))[0], PANEL, (t * 1.2) % 1)
            journey.create_oval(journey_pos["x"] - r, 24 - r, journey_pos["x"] + r, 24 + r, outline=col, width=2, tags="pulse")
            journey.tag_lower("pulse")

    pulse_edges = []
    journey_pos = {"x": None}
    header.bind("<Configure>", draw_header)
    status_pill = tk.Label(header, textvariable=status_var, bg=RAISED, fg=MUTED, font=(FONT, 10, "bold"), padx=14, pady=6,
                           highlightthickness=1, highlightbackground=NEON)
    status_pill.place(relx=1.0, x=-24, y=28, anchor="ne")

    nb = ttk.Notebook(root)
    nb.pack(fill="both", expand=True, padx=16, pady=(10, 16))

    # ================= Dashboard =================
    dash = tk.Frame(nb, bg=BG)
    nb.add(dash, text="  🏠  Dashboard  ")

    # ---- Stat cards
    stats = tk.Frame(dash, bg=BG)
    stats.pack(fill="x", padx=4, pady=(12, 6))
    stat_vars = {}
    card_widgets = {}
    stat_defs = [("total", "Orders shipped", "📦", RED),
                 ("waiting", "Awaiting first scan", "⏳", STAGE_STYLE["Shipped"][0]),
                 ("hub", "At Pokémon Center hub", "🏬", STAGE_STYLE["Dispatched"][0]),
                 ("moving", "Moving with Royal Mail", "🚚", STAGE_STYLE["At mail centre"][0]),
                 ("ofd", "Out for delivery", "🛵", STAGE_STYLE["Out for delivery"][0]),
                 ("delivered", "Delivered", "✅", STAGE_STYLE["Delivered"][0]),
                 ("last", "Last check", "⏱", BLUE)]
    for col, (key, label, icon, colour) in enumerate(stat_defs):
        c = card(stats)
        pulse_edges.append(c)
        c.grid(row=0, column=col, sticky="nsew", padx=6)
        stats.columnconfigure(col, weight=1)
        tk.Frame(c, bg=colour, height=6).pack(fill="x")
        inner = tk.Frame(c, bg=PANEL, padx=12, pady=6)
        inner.pack(fill="both", expand=True)
        tk.Label(inner, text=icon, bg=PANEL, fg=colour, font=("Segoe UI Emoji", 18)).pack(side="left", padx=(0, 10))
        txt = tk.Frame(inner, bg=PANEL)
        txt.pack(side="left", fill="x")
        v = tk.StringVar(value="—" if key == "last" else "0")
        stat_vars[key] = v
        tk.Label(txt, textvariable=v, bg=PANEL, fg=colour,
                 font=(FONT, 15 if key == "last" else 26, "bold")).pack(anchor="w")
        tk.Label(txt, text=label.upper(), bg=PANEL, fg=MUTED, font=(FONT, 8, "bold")).pack(anchor="w")
        if key != "last":
            card_widgets[key] = c
            for w in [c, inner, txt, *inner.winfo_children(), *txt.winfo_children()]:
                w.configure(cursor="hand2")
                w.bind("<Button-1>", lambda e, k=key: card_click(k))

    # ---- Toolbar
    bar = tk.Frame(dash, bg=BG)
    bar.pack(fill="x", padx=10, pady=(8, 6))
    start_btn = button(bar, "▶  Start tracking", RED)
    start_btn.pack(side="left")
    check_btn = button(bar, "⟳  Check now", BLUE)
    check_btn.pack(side="left", padx=8)
    export_btn = button(bar, "⬇  Export CSV", YELLOW, fg=DEEP)
    export_btn.pack(side="left")

    search_var = tk.StringVar()
    sbox = tk.Frame(bar, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
    sbox.pack(side="right")
    tk.Label(sbox, text="🔍", bg=PANEL, fg=MUTED).pack(side="left", padx=(8, 0))
    tk.Entry(sbox, textvariable=search_var, relief="flat", bg=PANEL, fg=TEXT, width=26,
             font=(FONT, 10), insertbackground=TEXT).pack(side="left", ipady=6, padx=6)
    search_var.trace_add("write", lambda *a: refresh_table())
    group_var = tk.BooleanVar(value=settings.get("group_by_customer", False))

    def toggle_group():
        group_var.set(not group_var.get())
        group_btn.configure(text=("🏠  Grouped by address" if group_var.get() else "🏠  Group by address"),
                            bg=RAISED if group_var.get() else PANEL, fg=NEON if group_var.get() else TEXT)
        s = load_json(SETTINGS_FILE, {})
        s["group_by_customer"] = group_var.get()
        save_json(SETTINGS_FILE, s)
        settings["group_by_customer"] = group_var.get()
        refresh_table()
    group_btn = tk.Button(bar, text="🏠  Group by address", command=lambda: toggle_group(), relief="flat", bd=0, cursor="hand2",
                          bg=PANEL, fg=TEXT, font=(FONT, 10, "bold"), padx=14, pady=7,
                          highlightthickness=1, highlightbackground=EDGE)
    group_btn.pack(side="right", padx=8)
    if group_var.get():
        group_btn.configure(text="🏠  Grouped by address", bg=RAISED, fg=ON)

    filter_var = tk.StringVar(value="All")
    chips = tk.Frame(dash, bg=BG)
    chips.pack(fill="x", padx=10, pady=(2, 8))
    chip_widgets = {}

    # The big counters at the top work as filters too (click again to show everything)
    CARD_FILTERS = {"moving": lambda p: p.stage in MOVING,
                    "ofd": lambda p: p.stage in ("Out for delivery", "Delivery attempted"),
                    "delivered": lambda p: p.done}
    card_filter = {"total": "All", "waiting": "Shipped", "hub": "Dispatched", "moving": "moving",
                   "ofd": "ofd", "delivered": "delivered"}

    def card_click(key):
        want = card_filter[key]
        set_filter("All" if filter_var.get() == want else want)
        nb.select(dash)

    def show_card_selection():
        for key, c in card_widgets.items():
            on = filter_var.get() == card_filter[key] and key != "total"
            c.configure(highlightbackground=NEON if on else "#22406E", highlightthickness=2 if on else 1)

    def set_filter(name):
        filter_var.set(name)
        show_card_selection()
        for n, w in chip_widgets.items():
            colour = STAGE_STYLE.get(n, ("#D62828" if n == "Stuck" else NEON,))[0]
            on = n == name
            w.configure(bg=colour if on else PANEL, fg=DEEP if on else colour,
                        activebackground=colour, activeforeground=ON)
        refresh_table()

    chip_labels = {"All": "All", "Shipped": "📦 Awaiting scan", "Dispatched": "🏬 PC hub",
                   "With Royal Mail": "📮 With Royal Mail", "At mail centre": "🏭 RM hub", "At delivery office": "🏤 Delivery office",
                   "Out for delivery": "🛵 Out for delivery", "Delivery attempted": "🔔 Attempted",
                   "Delivered": "✅ Delivered", "Stuck": "⚠ Stuck"}
    for name in ["All"] + STAGES + ["Stuck"]:
        colour = STAGE_STYLE.get(name, ("#D62828" if name == "Stuck" else NEON,))[0]
        w = tk.Button(chips, text=chip_labels[name],
                      relief="flat", bd=0, cursor="hand2", bg=PANEL, fg=colour, font=(FONT, 9, "bold"),
                      padx=10, pady=5, highlightthickness=1, highlightbackground=colour,
                      command=lambda n=name: set_filter(n))
        w.pack(side="left", padx=(0, 6))
        chip_widgets[name] = w
    chip_count = tk.Label(chips, text="", bg=BG, fg=MUTED, font=(FONT, 9))
    chip_count.pack(side="right")

    # ---- Activity log
    log_card = card(dash)
    log_card.pack(side="bottom", fill="x", padx=10, pady=(10, 10))
    tk.Label(log_card, text="  ⚡ ACTIVITY", bg=PANEL, fg=RED, font=(FONT, 8, "bold"), anchor="w").pack(fill="x", pady=(6, 0))
    log = tk.Text(log_card, height=3, bg=PANEL, fg=TEXT, relief="flat", font=("Consolas", 9), wrap="word",
                  padx=10, pady=4, highlightthickness=0)
    log.pack(fill="x")
    log.tag_configure("time", foreground=MUTED)
    log.tag_configure("error", foreground="#D62828")
    log.tag_configure("new", foreground=STAGE_STYLE["Shipped"][0])
    log.tag_configure("update", foreground=STAGE_STYLE["Out for delivery"][0])
    log.tag_configure("info", foreground=TEXT)

    # ---- Main area: table (left) + parcel card (right)
    main = tk.PanedWindow(dash, orient="horizontal", bg=BG, sashwidth=8, bd=0)
    main.pack(fill="both", expand=True, padx=10)

    table_card = card(main)
    cols = ("stage", "tracking", "name", "notes", "address", "rm", "shipped", "updated")
    table = ttk.Treeview(table_card, columns=cols, show="headings", selectmode="browse")
    for c, w, t, stretch in [("stage", 230, "STATUS", False), ("tracking", 140, "TRACKING", False),
                             ("name", 130, "NAME", False), ("notes", 80, "NOTES", False), ("address", 180, "ADDRESS", True),
                             ("rm", 230, "LATEST ROYAL MAIL UPDATE", True),
                             ("shipped", 105, "SHIPPED", False), ("updated", 105, "UPDATED", False)]:
        table.heading(c, text=t, anchor="w")
        table.column(c, width=w, anchor="w", stretch=stretch)
    for stage, (colour, soft, _) in STAGE_STYLE.items():
        table.tag_configure(stage, background=soft, foreground=TEXT)
    table.tag_configure("group", background=RAISED, foreground=NEON, font=(FONT, 10, "bold"))
    table.tag_configure("groupdone", background=STAGE_STYLE["Delivered"][0], foreground=DEEP, font=(FONT, 10, "bold"))
    table.column("#0", width=34, stretch=False, anchor="w")
    sb = ttk.Scrollbar(table_card, orient="vertical", command=table.yview)
    table.configure(yscrollcommand=sb.set)
    sb.pack(side="right", fill="y")
    table.pack(fill="both", expand=True)
    main.add(table_card, stretch="always", minsize=500)

    # ---- Parcel detail card
    detail = card(main)
    main.add(detail, minsize=400, width=430)
    d_head = tk.Canvas(detail, height=64, bg=RAISED, highlightthickness=0)
    d_head.pack(fill="x")
    d_body = tk.Frame(detail, bg=PANEL, padx=18, pady=12)
    d_body.pack(fill="both", expand=True)
    d_vars = {k: tk.StringVar() for k in ("tracking", "name", "address", "order", "items", "status")}
    tk.Label(d_body, textvariable=d_vars["name"], bg=PANEL, fg=TEXT, font=(FONT, 13, "bold"), anchor="w",
             justify="left", wraplength=350).pack(fill="x")
    tk.Label(d_body, textvariable=d_vars["address"], bg=PANEL, fg=MUTED, font=(FONT, 10), anchor="w",
             justify="left", wraplength=350).pack(fill="x", pady=(0, 8))
    for key, label in [("status", "Latest update"), ("journey", ""), ("items", "Order & items")]:
        if key == "journey":
            journey = tk.Canvas(d_body, height=66, bg=PANEL, highlightthickness=0)
            journey.pack(fill="x", pady=(6, 2))
            continue
        tk.Label(d_body, text=label.upper(), bg=PANEL, fg=MUTED, font=(FONT, 8, "bold"), anchor="w").pack(fill="x", pady=(4, 0))
        tk.Label(d_body, textvariable=d_vars[key], bg=PANEL, fg=TEXT, font=(FONT, 10), anchor="w",
                 justify="left", wraplength=350).pack(fill="x")
    tk.Label(d_body, text="JOURNEY", bg=PANEL, fg=MUTED, font=(FONT, 8, "bold"), anchor="w").pack(fill="x", pady=(10, 2))
    hist = tk.Text(d_body, height=5, bg=FIELD, fg=TEXT, relief="flat", font=(FONT, 9), wrap="word",
                   padx=8, pady=6, highlightthickness=0)
    hist.pack(fill="both", expand=True)
    hist.tag_configure("when", foreground=MUTED, font=(FONT, 8))
    for stage, (colour, _, _) in STAGE_STYLE.items():
        hist.tag_configure(stage, foreground=colour, font=(FONT, 9, "bold"))
    d_btns = tk.Frame(d_body, bg=PANEL)
    d_btns.pack(side="bottom", fill="x", pady=(10, 0), before=d_body.winfo_children()[0])  # always visible
    open_btn = button(d_btns, "🔗  Open tracking page", RED, size=9, pady=6)
    open_btn.pack(side="left")
    copy_btn = button(d_btns, "⧉  Copy number", RAISED, size=9, pady=6)
    copy_btn.pack(side="left", padx=6)
    notes_row = tk.Frame(d_body, bg=PANEL)
    notes_row.pack(side="bottom", fill="x", pady=(8, 0), before=d_btns)
    paid_var, handed_var, note_var = tk.BooleanVar(), tk.BooleanVar(), tk.StringVar()

    def save_notes(*_):
        p = current["p"]
        if not p or notes_loading["on"]:
            return
        p.paid, p.handed, p.note = paid_var.get(), handed_var.get(), note_var.get().strip()
        tracker.save()
        if table.exists(p.tracking):
            table.set(p.tracking, "notes", notes_text(p))
    notes_loading = {"on": False}
    for text, var in (("💷 Paid", paid_var), ("🤝 Handed over", handed_var)):
        tk.Checkbutton(notes_row, selectcolor=FIELD, text=text, variable=var, command=save_notes, bg=PANEL, activebackground=PANEL,
                       fg=TEXT, font=(FONT, 9, "bold"), highlightthickness=0, bd=0).pack(side="left", padx=(0, 8))
    note_entry = ttk.Entry(notes_row, textvariable=note_var, font=(FONT, 9))
    note_entry.pack(side="left", fill="x", expand=True)
    note_entry.bind("<Return>", save_notes)
    note_entry.bind("<FocusOut>", save_notes)
    note_hint = tk.Label(notes_row, text="note", bg=PANEL, fg=MUTED, font=(FONT, 8))
    note_hint.pack(side="left", padx=(4, 0))

    rebook_row = tk.Frame(d_body, bg=PANEL)
    rebook_row.pack(side="bottom", fill="x", pady=(8, 0), before=d_btns)
    rebook_btn = button(rebook_row, "📮  Rebook missed delivery (copies the number)", STAGE_STYLE["Delivery attempted"][0], size=9, pady=6)
    photo_btn = button(rebook_row, "📸  Delivery photo (copies the postcode)", STAGE_STYLE["Delivered"][0], size=9, pady=6)
    photo_thumb = tk.Label(rebook_row, bg=PANEL, cursor="hand2", bd=0)

    def draw_journey(stage):
        journey.delete("all")
        journey_pos["x"] = None
        w = max(journey.winfo_width(), 300)
        n = len(JOURNEY)
        xs = [34 + i * (w - 68) / (n - 1) for i in range(n)]
        attempted = stage == "Delivery attempted"
        node = "Out for delivery" if attempted else stage
        reached = JOURNEY.index(node) if node in JOURNEY else -1
        here = STAGE_STYLE.get(stage, (RED,))[0]
        journey.create_line(xs[0], 24, xs[-1], 24, fill=LINE, width=6, capstyle="round")
        if reached > 0:
            journey.create_line(xs[0], 24, xs[reached], 24, fill=here, width=6, capstyle="round")
        names = {"Shipped": "Shipped", "Dispatched": "PC\nhub", "With Royal Mail": "With\nRoyal Mail", "At mail centre": "RM\nhub",
                 "At delivery office": "Delivery\noffice", "Out for delivery": "Out for\ndelivery", "Delivered": "Delivered"}
        for i, (x, st) in enumerate(zip(xs, JOURNEY)):
            colour = STAGE_STYLE[st][0]
            if i == reached:
                journey_pos["x"] = x
                pokeball(journey, x, 24, 12, top=here, outline=DEEP)
            elif i < reached:
                journey.create_oval(x - 8, 16, x + 8, 32, fill=here, outline=PANEL, width=3)
            else:
                journey.create_oval(x - 8, 16, x + 8, 32, fill=PANEL, outline=LINE, width=3)
            label = "Attempted" if (attempted and st == "Out for delivery") else names[st]
            journey.create_text(x, 50, text=label, fill=(here if i == reached else colour) if i <= reached else MUTED,
                                font=(FONT, 7, "bold"), justify="center")

    current = {"p": None}
    d_head.bind("<Configure>", lambda e: show_parcel(current["p"]))
    journey.bind("<Configure>", lambda e: draw_journey(current["p"].stage if current["p"] else ""))

    def show_parcel(p):
        if current.get("p") is not None and current["p"] is not p and note_var.get().strip() != (current["p"].note or ""):
            save_notes()  # keep a half-typed note when switching parcels
        current["p"] = p
        notes_loading["on"] = True
        paid_var.set(bool(p and p.paid))
        handed_var.set(bool(p and p.handed))
        note_var.set(p.note if p else "")
        notes_loading["on"] = False
        state = "normal" if p else "disabled"
        for w in notes_row.winfo_children():
            try:
                w.configure(state=state)
            except tk.TclError:
                pass
        d_head.delete("all")
        w = max(d_head.winfo_width(), 340)
        colour = STAGE_STYLE.get(p.stage, (RED,))[0] if p else RED
        for i in range(16):  # glassy gradient tinted with the stage colour
            d_head.create_rectangle(0, i * 4, w, i * 4 + 4, outline="",
                                    fill=blend(blend(PANEL, colour, 0.42), DEEP, i / 18))
        d_head.create_rectangle(0, 61, w, 64, fill=colour, outline="")
        face = mascot(p.stage if p else "Shipped", 64)
        if face:
            d_head.create_oval(w - 66, 2, w - 6, 62, fill=RAISED, outline=colour, width=2)
            d_head.create_image(w - 36, 33, image=face)
        else:
            pokeball(d_head, w - 34, 32, 20, top=ON if p else RED, outline=DEEP)
        if not p:
            rebook_btn.pack_forget()
            photo_btn.pack_forget()
            d_head.create_text(18, 32, text="Pick a parcel", anchor="w", fill=ON, font=(FONT, 14, "bold"))
            for v in d_vars.values():
                v.set("")
            d_vars["name"].set("No parcel selected")
            d_vars["address"].set("Click a row in the table to see its details and journey.")
            draw_journey("")
            hist.delete("1.0", "end")
            return
        d_head.create_text(18, 22, text=STAGE_STYLE.get(p.stage, ("", "", p.stage))[2], anchor="w",
                           fill=colour, font=(FONT, 9, "bold"))
        d_head.create_text(18, 44, text=p.tracking, anchor="w", fill=ON, font=(FONT, 15, "bold"))
        d_vars["name"].set(p.name or "Name not found")
        d_vars["address"].set(p.address or "")
        d_vars["order"].set(p.order or "—")
        d_vars["items"].set(f"{p.order or '—'}  ·  {p.items or 'items not listed'}")
        status = p.rm_status or p.detail or "—"
        if p.stage == "Delivery attempted":
            ref = card_reference(p)
            if ref:
                status += f"\nCard ref: {ref}"
            if settings.get("rebook", True):
                rebook_btn.pack(side="left", fill="x", expand=True)
        else:
            rebook_btn.pack_forget()
        photo_thumb.pack_forget()
        if p.stage == "Delivered":
            pf = delivery_photo_file(p.tracking)
            if pf:
                thumb = picture_fit(str(pf), 96, 96)
                if thumb:
                    photo_thumb.configure(image=thumb)
                    photo_thumb.pack(side="left", padx=(0, 8))
                photo_btn.configure(text="📸  Open delivery photo")
            else:
                photo_btn.configure(text="📸  Delivery photo (copies the postcode)")
            photo_btn.pack(side="left", fill="x", expand=True)
        else:
            photo_btn.pack_forget()
        d_vars["status"].set(status)
        root.after(10, lambda: draw_journey(p.stage))
        hist.delete("1.0", "end")
        for h in reversed(p.history):
            hist.insert("end", f"{h.get('stage', '')}\n", h.get("stage", ""))
            hist.insert("end", f"{h.get('detail', '')}\n")
            hist.insert("end", f"{local_time(h.get('at', ''))}\n\n", "when")

    def selected():
        sel = table.selection()
        return tracker.parcels.get(sel[0]) if sel else None

    table.bind("<<TreeviewSelect>>", lambda e: show_parcel(selected()))
    table.bind("<Double-1>", lambda e: open_tracking())

    def open_tracking():
        p = selected()
        if p:
            webbrowser.open(NARVAR_URL.format(carrier=p.carrier or "royalmail-is", tracking=p.tracking))

    def copy_number():
        p = selected()
        if p:
            root.clipboard_clear()
            root.clipboard_append(p.tracking)
            add_log("info", f"Copied {p.tracking}")

    def rebook():
        p = selected()
        if p:
            ref = card_reference(p) or p.tracking
            root.clipboard_clear()
            root.clipboard_append(ref)
            add_log("info", f"Copied {ref}. Paste it on the Royal Mail redelivery page.")
            webbrowser.open(REDELIVERY_URL)

    def delivery_photo():
        p = selected()
        if p:
            pf = delivery_photo_file(p.tracking)
            if pf:
                try:
                    os.startfile(str(pf))
                except Exception:
                    webbrowser.open(pf.as_uri())
                return
            pc = delivery_postcode(p)
            if pc:
                root.clipboard_clear()
                root.clipboard_append(pc)
            add_log("info", f"Royal Mail asks for the delivery postcode{': ' + pc + ' (copied)' if pc else ''}. "
                            "The photo only shows if the postie took one.")
            webbrowser.open(RM_TRACK_URL.format(p.tracking))

    photo_btn.configure(command=delivery_photo)
    photo_thumb.bind("<Button-1>", lambda e: delivery_photo())
    rebook_btn.configure(command=rebook)
    open_btn.configure(command=open_tracking)
    copy_btn.configure(command=copy_number)

    def add_log(kind, text):
        log.insert("end", f"{datetime.now().strftime('%H:%M:%S')}  ", "time")
        log.insert("end", f"{text}\n", kind)
        log.see("end")

    def refresh_table():
        keep = table.selection()
        table.delete(*table.get_children())
        q = search_var.get().strip().lower()
        f = filter_var.get()
        shown = 0
        grouped = group_var.get()
        table.configure(show=("tree", "headings") if grouped else "headings")
        rows = []
        for p in sorted(tracker.parcels.values(), key=lambda p: p.shipped_at, reverse=True):
            stuck = is_stuck(p, settings.get("stuck_days", 3))
            if f == "Stuck":
                if not stuck:
                    continue
            elif f in CARD_FILTERS:
                if not CARD_FILTERS[f](p):
                    continue
            elif f != "All" and p.stage != f:
                continue
            if q and q not in " ".join([p.tracking, p.order, p.name, p.address, p.items, p.note]).lower():
                continue
            badge = STAGE_STYLE.get(p.stage, ("", "", p.stage))[2]
            if stuck:
                badge = f"⚠ STUCK {days_since(p)}d · " + chip_labels.get(p.stage, p.stage).split(" ", 1)[-1].upper()
            rows.append((p, (badge, p.tracking, p.name, notes_text(p), p.address,
                                 p.rm_status or p.detail, local_time(p.shipped_at), local_time(p.updated_at))))
            shown += 1
        if grouped:
            by: dict = {}
            for p, vals in rows:
                by.setdefault(customer_key(p), []).append((p, vals))
            all_groups = tracker.groups()
            for key, items in sorted(by.items(), key=lambda kv: (len(all_groups.get(kv[0], [])) < 2,
                                                                  (kv[1][0][0].name or "~").lower())):
                everyone = all_groups.get(key, [x[0] for x in items])
                n, d = len(everyone), sum(x.done for x in everyone)
                if n < 2:  # only one parcel to this address: no group row needed
                    for p, vals in items:
                        table.insert("", "end", iid=p.tracking, tags=(p.stage,), values=vals)
                    continue
                first = items[0][0]
                summary = "✅ ALL DELIVERED" if d == n else f"{d} of {n} delivered"
                names = list(dict.fromkeys(x.name for x in everyone if x.name))
                who = names[0] + (f" (+{len(names) - 1} more)" if len(names) > 1 else "") if names else "(no name)"
                gid = f"grp:{key}"
                table.insert("", "end", iid=gid, text="", open=True, tags=("groupdone" if d == n else "group",),
                             values=(f"👤 {summary}", f"{n} parcel{'s' if n > 1 else ''}", who, "",
                                     first.address, f"📍 {key}", "", ""))
                for p, vals in items:
                    table.insert(gid, "end", iid=p.tracking, tags=(p.stage,), values=vals)
        else:
            for p, vals in rows:
                table.insert("", "end", iid=p.tracking, tags=(p.stage,), values=vals)
        ps = list(tracker.parcels.values())
        stat_vars["total"].set(str(len(ps)))
        c = tracker.counts()
        for k in ("waiting", "hub", "moving", "ofd", "delivered"):
            stat_vars[k].set(str(c[k]))
        chip_count.configure(text=f"Showing {shown} of {len(ps)} parcels")
        if keep and table.exists(keep[0]):
            table.selection_set(keep[0])
        else:
            show_parcel(None)

    def export_csv():
        if not tracker.parcels:
            messagebox.showinfo(APP_NAME, "There are no parcels to export yet.")
            return
        path = filedialog.asksaveasfilename(
            title="Save parcels as CSV", defaultextension=".csv",
            initialfile=f"SIDs Sorting Center {datetime.now():%Y-%m-%d %H%M}.csv",
            filetypes=[("CSV file", "*.csv")])
        if not path:
            return
        try:
            with open(path, "wb") as f:
                f.write(csv_bytes(tracker.parcels.values()))
            add_log("info", f"Exported {len(tracker.parcels)} parcels to {path}")
            if messagebox.askyesno(APP_NAME, f"Saved {len(tracker.parcels)} parcels.\n\nOpen the file now?"):
                os.startfile(path)
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Couldn't save the CSV:\n{e}")

    export_btn.configure(command=export_csv)

    # ================= History =================
    hist_tab = tk.Frame(nb, bg=BG)
    nb.add(hist_tab, text="  📚  History  ")
    h_bar = tk.Frame(hist_tab, bg=BG)
    h_bar.pack(fill="x", padx=10, pady=(12, 6))
    tk.Label(h_bar, text=f"Parcels older than {KEEP_DAYS} days move here, so you can still look them up.",
             bg=BG, fg=MUTED, font=(FONT, 10)).pack(side="left")
    h_search = tk.StringVar()
    h_box = tk.Frame(h_bar, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
    h_box.pack(side="right")
    tk.Label(h_box, text="🔍", bg=PANEL, fg=MUTED).pack(side="left", padx=(8, 0))
    tk.Entry(h_box, textvariable=h_search, relief="flat", bg=PANEL, fg=TEXT, width=30, font=(FONT, 10),
             insertbackground=TEXT).pack(side="left", ipady=6, padx=6)
    h_card = card(hist_tab)
    h_card.pack(fill="both", expand=True, padx=10, pady=(0, 10))
    h_cols = ("stage", "tracking", "name", "notes", "address", "items", "shipped", "updated")
    h_table = ttk.Treeview(h_card, columns=h_cols, show="headings", selectmode="browse")
    for c, w, t, stretch in [("stage", 170, "STATUS", False), ("tracking", 140, "TRACKING", False),
                             ("name", 150, "NAME", False), ("notes", 90, "NOTES", False),
                             ("address", 260, "ADDRESS", True), ("items", 220, "ITEMS", True),
                             ("shipped", 105, "SHIPPED", False), ("updated", 105, "LAST UPDATE", False)]:
        h_table.heading(c, text=t, anchor="w")
        h_table.column(c, width=w, anchor="w", stretch=stretch)
    for stage, (colour, soft, _) in STAGE_STYLE.items():
        h_table.tag_configure(stage, background=soft, foreground=TEXT)
    h_sb = ttk.Scrollbar(h_card, orient="vertical", command=h_table.yview)
    h_table.configure(yscrollcommand=h_sb.set)
    h_sb.pack(side="right", fill="y")
    h_table.pack(fill="both", expand=True)
    h_empty = tk.Label(h_card, text="Nothing here yet. Parcels appear here once they're more than "
                                    f"{KEEP_DAYS} days old.", bg=PANEL, fg=MUTED, font=(FONT, 11))
    h_data = {}

    def refresh_history(*_):
        h_table.delete(*h_table.get_children())
        q = h_search.get().strip().lower()
        h_data.clear()
        ps = sorted(tracker.history_parcels(), key=lambda p: p.shipped_at, reverse=True)
        for p in ps:
            if q and q not in " ".join([p.tracking, p.order, p.name, p.address, p.items, p.note]).lower():
                continue
            h_data[p.tracking] = p
            h_table.insert("", "end", iid=p.tracking, tags=(p.stage,),
                           values=(STAGE_STYLE.get(p.stage, ("", "", p.stage))[2], p.tracking, p.name, notes_text(p),
                                   p.address, p.items, local_time(p.shipped_at), local_time(p.updated_at)))
        if ps:
            h_empty.place_forget()
        else:
            h_empty.place(relx=0.5, rely=0.4, anchor="center")
    h_search.trace_add("write", refresh_history)
    h_table.bind("<Double-1>", lambda e: h_table.selection() and webbrowser.open(
        NARVAR_URL.format(carrier=h_data[h_table.selection()[0]].carrier or "royalmail-is", tracking=h_table.selection()[0])))

    # ================= Logs =================
    logs_tab = tk.Frame(nb, bg=BG)
    nb.add(logs_tab, text="  📜  Logs  ")
    l_bar = tk.Frame(logs_tab, bg=BG)
    l_bar.pack(fill="x", padx=10, pady=(12, 6))
    tk.Label(l_bar, text="Every movement of every parcel, newest first: where it was and where it went.", bg=BG, fg=MUTED,
             font=(FONT, 10)).pack(side="left")
    l_period = tk.StringVar(value="7")
    l_search = tk.StringVar()
    l_box = tk.Frame(l_bar, bg=PANEL, highlightbackground=LINE, highlightthickness=1)
    l_box.pack(side="right")
    tk.Label(l_box, text="🔍", bg=PANEL, fg=MUTED).pack(side="left", padx=(8, 0))
    tk.Entry(l_box, textvariable=l_search, relief="flat", bg=PANEL, fg=TEXT, width=26, font=(FONT, 10),
             insertbackground=TEXT).pack(side="left", ipady=6, padx=6)
    l_count = tk.Label(l_bar, text="", bg=BG, fg=MUTED, font=(FONT, 10))
    l_count.pack(side="right", padx=12)
    for val, label in [("all", "All time"), ("30", "30 days"), ("7", "7 days"), ("1", "24 hours")]:
        tk.Radiobutton(l_bar, text=label, value=val, variable=l_period, indicatoron=0, relief="flat", bd=0,
                       bg=PANEL, fg=TEXT, selectcolor=NEON, activebackground=RAISED, activeforeground=ON,
                       font=(FONT, 9, "bold"), padx=10, pady=4, cursor="hand2",
                       highlightthickness=1, highlightbackground=EDGE,
                       command=lambda: refresh_logs()).pack(side="right", padx=2)
    l_card = card(logs_tab)
    l_card.pack(fill="both", expand=True, padx=10, pady=(0, 10))
    l_cols = ("when", "change", "tracking", "name", "from", "to", "was", "now", "source")
    l_table = ttk.Treeview(l_card, columns=l_cols, show="headings", selectmode="browse")
    for c, w, t, stretch in [("when", 98, "WHEN", False), ("change", 112, "CHANGE", False),
                             ("tracking", 126, "TRACKING", False), ("name", 115, "NAME", False),
                             ("from", 165, "FROM", False), ("to", 165, "→  TO", False),
                             ("was", 220, "WAS AT", True), ("now", 280, "NOW AT", True),
                             ("source", 78, "VIA", False)]:
        l_table.heading(c, text=t, anchor="w")
        l_table.column(c, width=w, anchor="w", stretch=stretch)
    for stage, (colour, soft, _) in STAGE_STYLE.items():
        l_table.tag_configure(stage, background=soft, foreground=TEXT)
    l_sb = ttk.Scrollbar(l_card, orient="vertical", command=l_table.yview)
    l_table.configure(yscrollcommand=l_sb.set)
    l_sb.pack(side="right", fill="y")
    l_table.pack(fill="both", expand=True)
    l_empty = tk.Label(l_card, text="No movements in this period yet.", bg=PANEL, fg=MUTED, font=(FONT, 11))
    l_rows = {}
    L_KIND = {"new": "✨ New parcel", "stage": "⏩ New stage", "moved": "📍 Moved"}
    L_SRC = {"page": "Tracking", "email": "Email", "fix": "Correction"}

    def stage_label(st):
        lab = STAGE_STYLE.get(st, ("", "", st))[2]
        icon, _, words = lab.partition(" ")
        return f"{icon} {words.title().replace('Pokémon Center', 'PC')}" if words else lab

    def place(text):   # drop the "(Wed 18 Nov 14:42)" scan time from where it was
        return SCAN_TIME_RE.sub("", text or "").strip() or "—"

    def refresh_logs(*_):
        l_table.delete(*l_table.get_children())
        l_rows.clear()
        q = l_search.get().strip().lower()
        per = l_period.get()
        cutoff = 0 if per == "all" else time.time() - int(per) * 86400
        allp = list(tracker.parcels.values()) + tracker.history_parcels()
        n = 0
        for i, e in enumerate(log_entries(allp)):
            if e["ts"] and e["ts"] < cutoff:
                break
            if q and q not in " ".join([e["tracking"], e["name"], e["stage"], e["detail"],
                                         e["prev_stage"], e["prev_detail"]]).lower():
                continue
            iid = f"l{i}"
            l_rows[iid] = e
            l_table.insert("", "end", iid=iid, tags=(e["stage"],),
                           values=(local_time(e["at"]), L_KIND[e["kind"]], e["tracking"], e["name"],
                                   stage_label(e["prev_stage"]) if e["prev_stage"] else "—",
                                   stage_label(e["stage"]),
                                   place(e["prev_detail"]), e["detail"],
                                   L_SRC.get(e["source"], e["source"])))
            n += 1
        l_count.configure(text=f"{n} change{'s' if n != 1 else ''}")
        if n:
            l_empty.place_forget()
        else:
            l_empty.place(relx=0.5, rely=0.4, anchor="center")
    l_search.trace_add("write", refresh_logs)
    l_table.bind("<Double-1>", lambda e: l_table.selection() and webbrowser.open(NARVAR_URL.format(
        carrier=l_rows[l_table.selection()[0]]["carrier"] or "royalmail-is",
        tracking=l_rows[l_table.selection()[0]]["tracking"])))

    # ================= Stats =================
    stats_tab = tk.Frame(nb, bg=BG)
    nb.add(stats_tab, text="  📊  Stats  ")
    tk.Label(stats_tab, text="How long parcels take, from your parcels (current + history).",
             bg=BG, fg=MUTED, font=(FONT, 10), anchor="w").pack(fill="x", padx=14, pady=(12, 6))
    stats_body = tk.Frame(stats_tab, bg=BG)
    stats_body.pack(fill="both", expand=True, padx=10)

    def fmt_days(d):
        if d is None:
            return "—"
        return f"{d * 24:.0f} h" if d < 1 else f"{d:.1f} days"

    def refresh_stats(*_):
        for w in stats_body.winfo_children():
            w.destroy()
        allp = list(tracker.parcels.values()) + tracker.history_parcels()
        colours = [BLUE, STAGE_STYLE["Dispatched"][0], STAGE_STYLE["With Royal Mail"][0],
                   STAGE_STYLE["Out for delivery"][0], "#D62828"]
        for i, (label, n, avg, lo, hi) in enumerate(delivery_stats(allp)):
            c = card(stats_body)
            c.grid(row=i // 2, column=i % 2, sticky="nsew", padx=6, pady=6)
            tk.Frame(c, bg=colours[i % len(colours)], height=5).pack(fill="x")
            inner = tk.Frame(c, bg=PANEL, padx=16, pady=12)
            inner.pack(fill="both", expand=True)
            tk.Label(inner, text=label, bg=PANEL, fg=MUTED, font=(FONT, 9, "bold"), anchor="w").pack(fill="x")
            tk.Label(inner, text=fmt_days(avg) if n else "Not enough data yet", bg=PANEL,
                     fg=colours[i % len(colours)] if n else MUTED, font=(FONT, 22 if n else 13, "bold"),
                     anchor="w").pack(fill="x", pady=(4, 0))
            tk.Label(inner, text=(f"average of {n} parcel{'s' if n != 1 else ''} · fastest {fmt_days(lo)} · "
                                  f"slowest {fmt_days(hi)}") if n else "Fills in as parcels reach this point.",
                     bg=PANEL, fg=MUTED, font=(FONT, 9), anchor="w").pack(fill="x")
        stats_body.columnconfigure(0, weight=1)
        stats_body.columnconfigure(1, weight=1)

    def on_tab(_=None):
        sel = nb.select()
        if sel == str(hist_tab):
            refresh_history()
        elif sel == str(logs_tab):
            refresh_logs()
        elif sel == str(stats_tab):
            refresh_stats()
    nb.bind("<<NotebookTabChanged>>", on_tab)

    # ================= Settings =================
    st_outer = tk.Frame(nb, bg=BG)
    nb.add(st_outer, text="  ⚙  Settings  ")
    st_canvas = tk.Canvas(st_outer, bg=BG, highlightthickness=0)
    st_scroll = ttk.Scrollbar(st_outer, orient="vertical", command=st_canvas.yview)
    st = tk.Frame(st_canvas, bg=BG)
    st.bind("<Configure>", lambda e: st_canvas.configure(scrollregion=st_canvas.bbox("all")))
    st_win = st_canvas.create_window((0, 0), window=st, anchor="nw")
    st_canvas.bind("<Configure>", lambda e: st_canvas.itemconfigure(st_win, width=e.width))
    st_canvas.configure(yscrollcommand=st_scroll.set)
    st_scroll.pack(side="right", fill="y")
    st_canvas.pack(fill="both", expand=True)
    st_canvas.bind_all("<MouseWheel>", lambda e: st_canvas.yview_scroll(int(-e.delta / 120), "units")
                       if nb.select() == str(st_outer) else None)

    fields = {}

    def section(title, colour, icon, subtitle):
        c = card(st)
        c.pack(fill="x", padx=12, pady=(14, 0))
        tk.Frame(c, bg=colour, width=6).pack(side="left", fill="y")
        body = tk.Frame(c, bg=PANEL, padx=18, pady=14)
        body.pack(side="left", fill="both", expand=True)
        tk.Label(body, text=f"{icon}  {title}", bg=PANEL, fg=colour, font=(FONT, 13, "bold"), anchor="w").grid(
            row=0, column=0, columnspan=2, sticky="w")
        tk.Label(body, text=subtitle, bg=PANEL, fg=MUTED, font=(FONT, 9), anchor="w").grid(
            row=1, column=0, columnspan=2, sticky="w", pady=(0, 6))
        body.columnconfigure(1, weight=1)
        body._row = 2
        return body

    def row(body, label, key, value, show=None, hint=""):
        r = body._row
        tk.Label(body, text=label, bg=PANEL, fg=TEXT, font=(FONT, 10, "bold"), anchor="w").grid(
            row=r, column=0, sticky="w", pady=(8, 0), padx=(0, 16))
        var = tk.StringVar(value=value)
        ttk.Entry(body, textvariable=var, show=show or "", font=(FONT, 10)).grid(row=r, column=1, sticky="we", pady=(8, 0))
        if hint:
            tk.Label(body, text=hint, bg=PANEL, fg=MUTED, font=(FONT, 8), anchor="w").grid(row=r + 1, column=1, sticky="w")
        body._row = r + 2
        fields[key] = var

    def btn_row(body):
        f = tk.Frame(body, bg=PANEL)
        f.grid(row=body._row, column=0, columnspan=2, sticky="w", pady=(12, 0))
        body._row += 1
        return f

    s_mail = section("Email (IMAP)", RED, "📧", "Where your Pokémon Center emails arrive. Read-only: nothing is moved or marked read.")
    row(s_mail, "IMAP email", "email", settings.get("email", ""), hint="The email address that gets your Pokémon Center emails")
    row(s_mail, "App password", "password", get_secret("imap_password"), show="•",
        hint="Google app password (myaccount.google.com/apppasswords). Saved in Windows Credential Manager.")
    row(s_mail, "IMAP server", "imap_host", settings.get("imap_host", "imap.gmail.com"),
        hint="Filled in for you from the email address (Gmail, Outlook/Hotmail, Yahoo, iCloud).")

    def fill_server(*_):
        addr = fields["email"].get()
        known = set(IMAP_SERVERS.values())
        if "@" in addr and (not fields["imap_host"].get().strip() or fields["imap_host"].get().strip() in known):
            fields["imap_host"].set(imap_server_for(addr))
    fields["email"].trace_add("write", fill_server)
    row(s_mail, "Check every (minutes)", "interval", str(settings.get("interval", 20)))
    mail_btns = btn_row(s_mail)

    s_disc = section("Discord alerts", "#5865F2", "🔔", "New shipments and every stage change, sent once each.")
    row(s_disc, "Webhook URL", "discord", get_secret("discord_webhook"), show="•",
        hint="Server Settings › Integrations › Webhooks › Copy URL. Leave blank to turn off.")
    disc_btns = btn_row(s_disc)

    s_bg = section("Running in the background", NEON, "🖥",
                   "Keep an eye on parcels without keeping the window open.")
    toggles = {}

    def toggle(body, key, text, default, hint=""):
        var = tk.BooleanVar(value=settings.get(key, default))
        tk.Checkbutton(body, selectcolor=FIELD, text=text, variable=var, bg=PANEL, activebackground=PANEL, fg=TEXT,
                       font=(FONT, 10), anchor="w", highlightthickness=0, bd=0).grid(
            row=body._row, column=0, columnspan=2, sticky="w", pady=(6, 0))
        body._row += 1
        if hint:
            tk.Label(body, text=hint, bg=PANEL, fg=MUTED, font=(FONT, 8), anchor="w").grid(
                row=body._row, column=0, columnspan=2, sticky="w", padx=(26, 0))
            body._row += 1
        toggles[key] = var

    toggle(s_bg, "autostart", "Start with Windows and start tracking automatically", False,
           "Opens hidden in the system tray when you sign in to Windows.")
    toggle(s_bg, "tray", "Closing the window keeps tracking in the system tray", True,
           "Right-click the tray icon (bottom-right, near the clock) to open it again or quit.")
    toggle(s_bg, "keep_awake", "Keep the PC from going to sleep while tracking", False,
           "The screen can still turn off. Handy if the PC is left on overnight.")
    toggle(s_bg, "toasts", "Windows pop-up notifications for each alert", True,
           "Shown alongside Discord, for the same alerts (never repeated).")

    toggle(s_bg, "phone_view", "Phone view: see your parcels on your phone (same Wi-Fi)", True,
           "Copy the link, open it on your phone (same Wi-Fi), then Share › Add to Home Screen: it opens like an app with no address showing.")
    toggle(s_bg, "backups", "Back up parcels and settings every day (keeps 14 days)", True,
           f"Saved in {BACKUP_DIR}. Passwords are never included.")
    phone_link = tk.StringVar(value="")
    pl = tk.Frame(s_bg, bg=PANEL)
    pl.grid(row=s_bg._row, column=0, columnspan=2, sticky="w", pady=(8, 0))
    s_bg._row += 1
    tk.Label(pl, text="📱 Phone link:", bg=PANEL, fg=NEON, font=(FONT, 10, "bold")).pack(side="left")
    tk.Entry(pl, textvariable=phone_link, state="readonly", readonlybackground=FIELD, fg=TEXT, relief="flat",
             width=52, font=(FONT, 10)).pack(side="left", padx=8, ipady=4)

    def copy_phone_link():
        root.clipboard_clear()
        root.clipboard_append(phone["ip_link"])
        add_log("info", "Phone link copied. Open it on your phone, then 'Add to Home Screen' so it opens like an app with no address bar.")
    button(pl, "Copy", RAISED, copy_phone_link, size=9, pady=4, padx=10).pack(side="left")

    bg_btns = btn_row(s_bg)

    def shortcuts():
        try:
            made = make_shortcuts()
            messagebox.showinfo(APP_NAME, "Shortcuts made with the Poké Ball icon:\n\n" + "\n".join(made) +
                                "\n\nPin it to the taskbar by right-clicking the desktop shortcut.")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Couldn't make the shortcuts:\n{e}")
    button(bg_btns, "🖱  Create desktop & Start menu shortcut", RAISED, shortcuts, size=9, pady=6).pack(side="left")

    def backup_now():
        try:
            d = backup_data(force=True)
            add_log("info", f"Backup saved to {d}")
            os.startfile(str(BACKUP_DIR))
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Backup failed:\n{e}")
    button(bg_btns, "💾  Back up now", RAISED, backup_now, size=9, pady=6).pack(side="left", padx=(8, 0))

    s_smart = section("Smart alerts", "#D62828", "🚨", "Extra Discord messages to catch problems early.")
    row(s_smart, "Problem alert after (minutes)", "health_minutes", str(settings.get("health_minutes", 60)),
        hint="One Discord alert if checks keep failing this long (e.g. Gmail password changed, no internet). 0 = off.")
    row(s_smart, "Stuck after (days)", "stuck_days", str(settings.get("stuck_days", 3)),
        hint="One alert when a parcel hasn't moved for this many days. 0 = off.")
    row(s_smart, "Daily summary at", "summary_time", settings.get("summary_time", "09:00"),
        hint="24-hour time, e.g. 09:00. Sent once a day while tracking. Blank = off.")
    row(s_smart, "Ping on Delivery attempted", "ping", settings.get("ping", "@everyone"),
        hint="@everyone, @here, or <@your Discord user ID>. Blank = no ping.")
    row(s_smart, "Weekly CSV to Discord on", "csv_day", settings.get("csv_day", "Monday"),
        hint="Day of the week (e.g. Monday). Sent at the daily summary time (or 09:00). Blank = off.")
    toggle(s_smart, "customer_alerts", "Alert when every parcel for the same address (postcode) has been delivered", True)
    toggle(s_smart, "rebook", "Show rebooking help on missed deliveries (app and Discord)", True)
    smart_btns = btn_row(s_smart)

    s_upd = section("Updates", NEON, "⬆", f"You have version {VERSION}. New versions come from github.com/{UPDATE_REPO}.")
    toggle(s_upd, "auto_update", "Check for updates every day and install them automatically", True,
           "Your settings, parcels, pictures and passwords are kept. The app restarts itself after updating.")
    upd_btns = btn_row(s_upd)

    def update_now(quiet=False):
        def work():
            try:
                found = check_update()
            except Exception as e:
                if not quiet:
                    events.put(("error", f"Couldn't check for updates: {e}"))
                return
            if not found:
                if not quiet:
                    events.put(("info", f"You're on the latest version ({VERSION})."))
                return
            ver, code = found
            try:
                install_update(code)
                events.put(("alert", f"Updating to version {ver}\nThe app will restart in a few seconds."))
                events.put(("info", f"Installed version {ver}; restarting."))
            except Exception as e:
                events.put(("error", f"Update to {ver} failed: {e}"))
        threading.Thread(target=work, daemon=True).start()
    button(upd_btns, "⬆  Check for updates now", NEON, lambda: update_now(False), size=9, pady=6).pack(side="left")

    def auto_update_timer():
        if settings.get("auto_update", True):
            update_now(True)
        root.after(24 * 3_600_000, auto_update_timer)
    root.after(120_000, auto_update_timer)

    s_look = section("Look & pictures", YELLOW_DARK, "🎨",
                     "Add your own pictures once, then choose where they show. A picture picked for a stage is used everywhere for that stage.")

    def picker_row(body, label, key, value, types, hint):
        r = body._row
        tk.Label(body, text=label, bg=PANEL, fg=TEXT, font=(FONT, 10, "bold"), anchor="w").grid(
            row=r, column=0, sticky="w", pady=(8, 0), padx=(0, 16))
        f = tk.Frame(body, bg=PANEL)
        f.grid(row=r, column=1, sticky="we", pady=(8, 0))
        var = tk.StringVar(value=value)
        ttk.Entry(f, textvariable=var, font=(FONT, 10)).pack(side="left", fill="x", expand=True)

        def browse():
            path = filedialog.askopenfilename(title=label, filetypes=types)
            if path:
                var.set(path)
        button(f, "Browse…", RAISED, browse, size=9, pady=4, padx=10).pack(side="left", padx=(6, 0))
        button(f, "Clear", MUTED, lambda: var.set(""), size=9, pady=4, padx=10).pack(side="left", padx=(6, 0))
        tk.Label(body, text=hint, bg=PANEL, fg=MUTED, font=(FONT, 8), anchor="w").grid(row=r + 1, column=1, sticky="w")
        body._row = r + 2
        fields[key] = var

    # Your picture library: add pictures once, then choose where each is used.
    tk.Label(s_look, text="My pictures", bg=PANEL, fg=TEXT, font=(FONT, 10, "bold"), anchor="w").grid(
        row=s_look._row, column=0, sticky="nw", pady=(8, 0), padx=(0, 16))
    lib_box = tk.Frame(s_look, bg=PANEL)
    lib_box.grid(row=s_look._row, column=1, sticky="we", pady=(8, 0))
    s_look._row += 1
    lib_btns = tk.Frame(lib_box, bg=PANEL)
    lib_btns.pack(fill="x")
    lib_strip = tk.Frame(lib_box, bg=FIELD, highlightbackground=EDGE, highlightthickness=1)
    lib_strip.pack(fill="x", pady=(8, 0))
    tk.Label(lib_box, text="PNG, JPG, GIF or WebP. Add as many as you like, or drop them straight into the folder "
                           "(Open folder), then press Refresh.", bg=PANEL, fg=MUTED, font=(FONT, 8),
             anchor="w").pack(fill="x", pady=(4, 0))
    pic_choice = {"header": tk.StringVar(), "*": tk.StringVar()}
    stage_pics = dict(settings.get("stage_pics") or {})
    for st_name in STAGES:
        pic_choice[st_name] = tk.StringVar()
    NICE = {"mascots": "Stage pictures (parade)", "mascot": "Built-in mascot", "turns": "Take turns (all my pictures)",
            "": "Same as 'All alerts'"}

    def label_of(v):
        return NICE.get(v, v)

    def value_of(label):
        for k, t in NICE.items():
            if t == label:
                return k
        return label

    combos = []

    def add_pictures():
        paths = filedialog.askopenfilenames(title="Add pictures", filetypes=[
            ("Pictures", "*.png *.jpg *.jpeg *.gif *.webp"), ("All files", "*.*")])
        if not paths:
            return
        PICS_DIR.mkdir(parents=True, exist_ok=True)
        added, skipped = 0, []
        for src in paths:
            src = Path(src)
            if src.suffix.lower() not in PIC_TYPES:
                skipped.append(f"{src.name} (not a picture)")
                continue
            if src.stat().st_size >= 8_000_000:
                skipped.append(f"{src.name} (over 8 MB, too big for Discord)")
                continue
            dest = PICS_DIR / src.name
            n = 2
            while dest.exists():
                dest = PICS_DIR / f"{src.stem} ({n}){src.suffix}"
                n += 1
            shutil.copy2(src, dest)
            added += 1
        refresh_library()
        add_log("info", f"Added {added} picture{'s' if added != 1 else ''} to My pictures.")
        if skipped:
            messagebox.showwarning(APP_NAME, "Skipped:\n" + "\n".join(skipped))

    def open_folder():
        PICS_DIR.mkdir(parents=True, exist_ok=True)
        try:
            os.startfile(str(PICS_DIR))
        except Exception as e:
            messagebox.showinfo(APP_NAME, f"Your pictures folder is:\n{PICS_DIR}\n\n({e})")

    def remove_picture(p):
        if not messagebox.askyesno(APP_NAME, f"Remove {p.name} from My pictures?\n(Your original file is not touched.)"):
            return
        try:
            p.unlink()
        except OSError as e:
            messagebox.showerror(APP_NAME, str(e))
        refresh_library()

    def refresh_library():
        for w in lib_strip.winfo_children():
            w.destroy()
        for k in [k for k in images if k[0] == "file"]:
            images.pop(k, None)   # pick up edited pictures
        pics = library_pictures()
        if not pics:
            tk.Label(lib_strip, text="No pictures yet. Press 'Add pictures…' to pick some from your PC.",
                     bg=FIELD, fg=MUTED, font=(FONT, 9), pady=18).pack(fill="x")
        for i, p in enumerate(pics):
            cell = tk.Frame(lib_strip, bg=FIELD, padx=6, pady=6)
            cell.grid(row=i // 8, column=i % 8, sticky="n")
            img = picture_fit(str(p), 64, 80)
            tk.Label(cell, image=img, bg=FIELD, width=80, height=64).pack() if img else \
                tk.Label(cell, text="?", bg=FIELD, fg=MUTED, width=10, height=4).pack()
            tk.Label(cell, text=p.name if len(p.name) <= 14 else p.name[:12] + "…", bg=FIELD, fg=TEXT,
                     font=(FONT, 7)).pack()
            tk.Button(cell, text="✕ remove", command=lambda p=p: remove_picture(p), relief="flat", bd=0, bg=FIELD,
                      fg=RED, activebackground=RAISED, activeforeground=RED, font=(FONT, 7), cursor="hand2").pack()
        names = [p.name for p in pics]
        for combo, var, extra in combos:
            combo.configure(values=[label_of(v) for v in extra + (["turns"] if names else [])] + names)
            if value_of(var.get()) not in extra + ["turns"] + names:
                var.set(label_of(extra[0]))
        draw_header()

    button(lib_btns, "＋  Add pictures…", NEON, add_pictures, size=9, pady=4, padx=12).pack(side="left")
    button(lib_btns, "📂  Open folder", RAISED, open_folder, size=9, pady=4, padx=12).pack(side="left", padx=(6, 0))
    button(lib_btns, "⟳  Refresh", RAISED, lambda: refresh_library(), size=9, pady=4, padx=12).pack(side="left", padx=(6, 0))

    def choice_row(label, var, extra, value, hint=""):
        r = s_look._row
        tk.Label(s_look, text=label, bg=PANEL, fg=TEXT, font=(FONT, 10, "bold"), anchor="w").grid(
            row=r, column=0, sticky="w", pady=(6, 0), padx=(0, 16))
        f = tk.Frame(s_look, bg=PANEL)
        f.grid(row=r, column=1, sticky="w", pady=(6, 0))
        cb = ttk.Combobox(f, textvariable=var, state="readonly", width=34, font=(FONT, 10))
        cb.pack(side="left")
        if hint:
            tk.Label(f, text=hint, bg=PANEL, fg=MUTED, font=(FONT, 8)).pack(side="left", padx=(8, 0))
        var.set(label_of(value))
        combos.append((cb, var, extra))
        s_look._row += 1

    choice_row("Header shows", pic_choice["header"], ["mascots"], settings.get("header_pic", "mascots"),
               "'Take turns' changes picture every 20 seconds")
    choice_row("All Discord alerts", pic_choice["*"], ["mascot"], stage_pics.get("*", "mascot"),
               "'Take turns' uses the next picture on each alert")
    tk.Label(s_look, text="Or pick a picture per stage:", bg=PANEL, fg=MUTED, font=(FONT, 9, "bold"),
             anchor="w").grid(row=s_look._row, column=0, columnspan=2, sticky="w", pady=(10, 0))
    s_look._row += 1
    for st_name in STAGES:
        choice_row("   " + STAGE_STYLE[st_name][2].split(" ", 1)[1].title(), pic_choice[st_name], ["", "mascot"],
                   stage_pics.get(st_name, ""))
    # Older versions picked one file each; copy those into My pictures so they show up here.
    fields["header_image"] = tk.StringVar(value="")
    fields["discord_image"] = tk.StringVar(value="")
    for old_key, var in (("header_image", pic_choice["header"]), ("discord_image", pic_choice["*"])):
        src = Path(settings.get(old_key) or "")
        if settings.get(old_key) and src.is_file() and src.suffix.lower() in PIC_TYPES:
            try:
                PICS_DIR.mkdir(parents=True, exist_ok=True)
                dest = PICS_DIR / src.name
                if not dest.exists():
                    shutil.copy2(src, dest)
                var.set(dest.name)
            except OSError:
                fields[old_key].set(settings.get(old_key))
        elif settings.get(old_key):
            fields[old_key].set(settings.get(old_key))
    mascots_var = tk.BooleanVar(value=settings.get("discord_mascots", True))
    tk.Checkbutton(s_look, selectcolor=FIELD, text="Show the stage mascots on Discord alerts", variable=mascots_var, bg=PANEL,
                   activebackground=PANEL, fg=TEXT, font=(FONT, 10), anchor="w").grid(
        row=s_look._row, column=1, sticky="w", pady=(8, 0))
    s_look._row += 1
    strip = tk.Frame(s_look, bg=PANEL)
    strip.grid(row=s_look._row, column=0, columnspan=2, sticky="w", pady=(10, 0))
    s_look._row += 1
    for st_name in STAGES:
        cell = tk.Frame(strip, bg=PANEL)
        cell.pack(side="left", padx=(0, 10))
        tk.Label(cell, image=mascot(st_name, 64), bg=PANEL).pack()
        tk.Label(cell, text=STAGE_STYLE[st_name][2].split(" ", 1)[1].title(), bg=PANEL, fg=STAGE_STYLE[st_name][0],
                 font=(FONT, 7, "bold"), wraplength=80, justify="center").pack()

    refresh_library()

    s_trk = section("Extra tracking sources (optional)", STAGE_STYLE["Delivered"][0], "📮",
                    "Without these, the Pokémon Center tracking page is used. Add a key for more detailed Royal Mail scans.")
    row(s_trk, "Ship24 API key", "ship24", get_secret("ship24_key"), show="•",
        hint="Free at ship24.com (10 new parcels a month).")
    row(s_trk, "Royal Mail client ID", "rm_id", settings.get("rm_id", ""),
        hint="Royal Mail Tracking API (needs a Royal Mail business account).")
    row(s_trk, "Royal Mail client secret", "rm_secret", get_secret("rm_secret"), show="•")
    trk_btns = btn_row(s_trk)

    save_bar = tk.Frame(st, bg=BG)
    save_bar.pack(fill="x", padx=12, pady=16)

    def current_cfg():
        try:
            interval = max(5, int(fields["interval"].get() or 20))
        except ValueError:
            interval = 20
        try:
            stuck_days = max(0, int(float(fields["stuck_days"].get() or 0)))
        except ValueError:
            stuck_days = 3
        m = re.match(r"^\s*(\d{1,2})[:.](\d{2})\s*$", fields["summary_time"].get())
        summary_time = f"{int(m[1]):02d}:{m[2]}" if m and int(m[1]) < 24 and int(m[2]) < 60 else ""
        try:
            health_minutes = max(0, int(float(fields["health_minutes"].get() or 0)))
        except ValueError:
            health_minutes = 60
        day = fields["csv_day"].get().strip().lower()[:3]
        csv_day = next((d for d in ("Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday")
                        if day and d.lower().startswith(day)), "")
        return {
            "email": fields["email"].get().strip(),
            "password": fields["password"].get().replace(" ", "").strip(),
            "imap_host": fields["imap_host"].get().strip() or imap_server_for(fields["email"].get()),
            "interval": interval,
            "discord": fields["discord"].get().strip(),
            "rm_id": fields["rm_id"].get().strip(),
            "rm_secret": fields["rm_secret"].get().strip(),
            "ship24": fields["ship24"].get().strip(),
            "header_image": fields["header_image"].get().strip().strip('"'),
            "discord_image": fields["discord_image"].get().strip().strip('"'),
            "discord_mascots": bool(mascots_var.get()),
            "phone_key": settings.get("phone_key", ""),
            "header_pic": value_of(pic_choice["header"].get()) or "mascots",
            "stage_pics": {k: value_of(v.get()) for k, v in pic_choice.items() if k != "header" and value_of(v.get())},
            "stuck_days": stuck_days,
            "summary_time": summary_time,
            "ping": fields["ping"].get().strip(),
            "csv_day": csv_day,
            "health_minutes": health_minutes,
            **{k: bool(v.get()) for k, v in toggles.items()},
        }

    def save_settings():
        cfg = current_cfg()
        try:
            set_secret("imap_password", cfg["password"])
            set_secret("discord_webhook", cfg["discord"])
            set_secret("rm_secret", cfg["rm_secret"])
            set_secret("ship24_key", cfg["ship24"])
        except Exception as e:
            messagebox.showerror(APP_NAME, str(e))
            return False
        if cfg["header_image"] and not picture_fit(cfg["header_image"], 84):
            messagebox.showwarning(APP_NAME, "That header picture couldn't be opened. Use a PNG or GIF file.")
            cfg["header_image"] = ""
            fields["header_image"].set("")
        keys = ("email", "imap_host", "interval", "rm_id", "header_image", "discord_image", "discord_mascots",
                "header_pic", "stage_pics", "phone_key",
                "stuck_days", "summary_time", "ping", "csv_day", "group_by_customer", "health_minutes", *toggles)
        if cfg["autostart"] != settings.get("autostart", False):
            try:
                set_autostart(cfg["autostart"])
            except Exception as e:
                messagebox.showwarning(APP_NAME, f"Couldn't change 'Start with Windows':\n{e}")
                cfg["autostart"] = False
                toggles["autostart"].set(False)
        fields["stuck_days"].set(str(cfg["stuck_days"]))
        fields["summary_time"].set(cfg["summary_time"])
        fields["csv_day"].set(cfg["csv_day"])
        cfg["group_by_customer"] = group_var.get()
        save_json(SETTINGS_FILE, {k: cfg[k] for k in keys})
        try:
            stamps["settings"] = Path(SETTINGS_FILE).stat().st_mtime   # our own save: no restart
        except (OSError, NameError):
            pass
        settings.clear()
        settings.update({k: cfg[k] for k in keys})
        if worker["thread"] and worker["thread"].is_alive():
            keep_awake(cfg["keep_awake"])
        refresh_table()
        look["header_image"] = cfg["header_image"]
        look["header_pic"] = cfg["header_pic"]
        draw_header()
        add_log("info", "Settings saved.")
        return True

    def test_imap():
        cfg = current_cfg()
        try:
            with imaplib.IMAP4_SSL(cfg["imap_host"], 993, timeout=20) as M:
                M.login(cfg["email"], cfg["password"])
            messagebox.showinfo(APP_NAME, "IMAP login worked ✔")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"IMAP login failed:\n{e}")

    def test_discord():
        cfg = current_cfg()
        if not cfg["discord"]:
            messagebox.showinfo(APP_NAME, "Paste a Discord webhook URL first.")
            return
        try:
            post_webhook(cfg["discord"], {"embeds": [{"title": "✅ SID's Sorting Center is connected",
                                                      "description": "Parcel alerts will look like this.",
                                                      "color": STAGE_COLOURS["Delivered"]}]},
                         discord_picture("Delivered", cfg))
            messagebox.showinfo(APP_NAME, "Test message sent to Discord ✔")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Discord test failed:\n{e}")

    def test_ship24():
        cfg = current_cfg()
        if not cfg["ship24"]:
            messagebox.showinfo(APP_NAME, "Paste your Ship24 API key first.")
            return
        live = [t for t, p in tracker.parcels.items() if not p.done]
        if not live:
            messagebox.showinfo(APP_NAME, "No parcels in transit to test with right now (testing uses up one of your free parcels).")
            return
        try:
            res = ship24_status(live[0], cfg["ship24"])
            messagebox.showinfo(APP_NAME, f"Ship24 works ✔\n\n{live[0]}: {res[1] if res else 'no scans yet'}")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Ship24 test failed:\n{e}")

    def test_rm():
        cfg = current_cfg()
        if not (cfg["rm_id"] and cfg["rm_secret"]):
            messagebox.showinfo(APP_NAME, "Paste your Royal Mail API client ID and secret first.")
            return
        sample = next(iter(tracker.parcels), "FE827634825GB")
        try:
            res = royal_mail_status(sample, cfg["rm_id"], cfg["rm_secret"])
            messagebox.showinfo(APP_NAME, f"Royal Mail API works ✔\n\n{sample}: {res[1] if res else 'no scans found'}")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Royal Mail API test failed:\n{e}")

    def send_summary(manual=False):
        cfg = current_cfg()
        if not cfg["discord"]:
            if manual:
                messagebox.showinfo(APP_NAME, "Paste a Discord webhook URL first.")
            return
        parcels = list(tracker.parcels.values())

        def go():
            try:
                post_webhook(cfg["discord"], {"embeds": [summary_embed(parcels, cfg)]}, discord_picture("Out for delivery", cfg))
                events.put(("info", "Daily summary sent to Discord."))
            except Exception as e:
                events.put(("error", f"Daily summary failed: {e}"))
        threading.Thread(target=go, daemon=True).start()

    def send_csv(manual=False):
        cfg = current_cfg()
        if not cfg["discord"]:
            if manual:
                messagebox.showinfo(APP_NAME, "Paste a Discord webhook URL first.")
            return
        parcels = list(tracker.parcels.values())
        c = tracker.counts()

        def go():
            try:
                post_file(cfg["discord"], f"📊 Weekly parcel export: {c['total']} parcels, {c['delivered']} delivered, "
                                          f"{c['moving']} moving with Royal Mail.",
                          f"SIDs Sorting Center {datetime.now():%Y-%m-%d}.csv", csv_bytes(parcels))
                events.put(("info", "Weekly CSV sent to Discord."))
            except Exception as e:
                events.put(("error", f"Weekly CSV failed: {e}"))
        threading.Thread(target=go, daemon=True).start()

    def summary_timer():
        """Once a minute: send the daily summary if it's time and it hasn't gone out today."""
        try:
            t = settings.get("summary_time", "09:00")
            running = worker["thread"] and worker["thread"].is_alive()
            now = datetime.now()
            if t and running and now.strftime("%H:%M") >= t:
                today = now.strftime("%Y-%m-%d")
                sent = load_json(SUMMARY_FILE, {})
                if sent.get("last") != today:
                    sent["last"] = today
                    save_json(SUMMARY_FILE, sent)
                    send_summary()
            day, at = settings.get("csv_day", "Monday"), settings.get("summary_time") or "09:00"
            if day and running and now.strftime("%A") == day and now.strftime("%H:%M") >= at:
                week = now.strftime("%G-W%V")
                sent = load_json(SUMMARY_FILE, {})
                if sent.get("csv_week") != week:
                    sent["csv_week"] = week
                    save_json(SUMMARY_FILE, sent)
                    send_csv()
        except Exception as e:
            add_log("error", f"Summary timer: {e}")
        root.after(60_000, summary_timer)

    button(smart_btns, "Send summary now", "#D62828", lambda: send_summary(True), size=9, pady=6).pack(side="left")
    button(smart_btns, "Send CSV now", "#D62828", lambda: send_csv(True), size=9, pady=6).pack(side="left", padx=8)
    button(mail_btns, "Test IMAP login", RED, test_imap, size=9, pady=6).pack(side="left")
    button(disc_btns, "Send Discord test", "#5865F2", test_discord, size=9, pady=6).pack(side="left")
    button(trk_btns, "Test Ship24", STAGE_STYLE["Delivered"][0], test_ship24, size=9, pady=6).pack(side="left")
    button(trk_btns, "Test Royal Mail API", STAGE_STYLE["Delivered"][0], test_rm, size=9, pady=6).pack(side="left", padx=8)
    button(save_bar, "💾  Save settings", RED, save_settings, size=11, padx=24, pady=10).pack(side="left")
    tk.Label(save_bar, text=f"Data folder: {DATA_DIR}", bg=BG, fg=MUTED, font=(FONT, 8)).pack(side="left", padx=14)

    # ================= Worker =================
    health = {"since": None, "alerted": False}

    def health_update(cfg, problem: str = ""):
        """One Discord alert when checks keep failing, and one when they work again."""
        hook = cfg.get("discord", "")
        mins = cfg.get("health_minutes", 60)
        if not problem:
            if health["alerted"] and hook:
                try:
                    post_webhook(hook, {"embeds": [{"title": "✅ Tracker is working again", "color": STAGE_COLOURS["Delivered"],
                                                    "description": "Checks are going through normally.",
                                                    "timestamp": now_iso()}]}, discord_picture("Delivered", cfg))
                except Exception:
                    pass
                events.put(("alert", "Tracker is working again\nChecks are going through normally."))
            health.update(since=None, alerted=False)
            return
        if health["since"] is None:
            health["since"] = time.time()
        if mins and not health["alerted"] and time.time() - health["since"] >= mins * 60:
            health["alerted"] = True
            hint = ("Your Gmail app password may have changed: open Settings and click Test IMAP login."
                    if "IMAP" in problem or "LOGIN" in problem.upper() else
                    "Check the PC is online. If it keeps happening, the tracking page may have changed.")
            events.put(("alert", f"Tracker problem\n{problem[:150]}"))
            if hook:
                try:
                    post_webhook(hook, {"embeds": [{
                        "title": "🚨 Tracker problem: checks are failing", "color": 0xD62828,
                        "description": f"Failing since {datetime.fromtimestamp(health['since']):%H:%M}.\n"
                                       f"**Error:** {problem[:500]}\n\n{hint}",
                        "timestamp": now_iso()}]}, discord_picture("Delivery attempted", cfg))
                except Exception:
                    pass

    def loop(cfg, once=False):
        while not stop_flag.is_set():
            events.put(("status", "● Checking…"))
            try:
                tracker.run_once(cfg)
                events.put(("checked", now_iso()))
                health_update(cfg)
            except imaplib.IMAP4.error as e:
                events.put(("error", f"IMAP login/search failed: {e}"))
                health_update(cfg, f"Gmail (IMAP) login/search failed: {e}")
            except RuntimeError as e:
                events.put(("checked", now_iso()))
                events.put(("error", str(e)))
                health_update(cfg, str(e))
            except Exception as e:
                events.put(("error", f"Check failed: {e}"))
                traceback.print_exc()
                health_update(cfg, f"{e.__class__.__name__}: {e}")
            if once:
                events.put(("status", "● Tracking" if (worker["thread"] and worker["thread"].is_alive()) else "● Stopped"))
                break
            nxt = datetime.now().timestamp() + cfg["interval"] * 60
            events.put(("status", f"● Tracking · next check {datetime.fromtimestamp(nxt):%H:%M}"))
            wake.clear()
            end = time.time() + cfg["interval"] * 60
            while not stop_flag.is_set() and not wake.is_set() and time.time() < end:
                wake.wait(min(5, max(0.1, end - time.time())))
        events.put(("stopped", ""))

    def set_running(on):
        keep_awake(bool(on and settings.get("keep_awake")))
        if on:
            start_btn.configure(text="■  Stop tracking", bg=RAISED, activebackground=shade(RAISED))
            start_btn.bind("<Leave>", lambda e: start_btn.configure(bg=RAISED))
            status_pill.configure(bg=STAGE_STYLE["Delivered"][0])
        else:
            start_btn.configure(text="▶  Start tracking", bg=RED, activebackground=shade(RED))
            start_btn.bind("<Leave>", lambda e: start_btn.configure(bg=RED))
            status_pill.configure(bg=RAISED)

    def start_stop():
        if worker["thread"] and worker["thread"].is_alive():
            stop_flag.set()
            set_running(False)
            status_var.set("● Stopping…")
            return
        cfg = current_cfg()
        if not cfg["email"] or not cfg["password"]:
            nb.select(st_outer)
            messagebox.showinfo(APP_NAME, "Enter your IMAP email and app password in Settings first.")
            return
        if not save_settings():
            return
        stop_flag.clear()
        worker["cfg"] = cfg
        worker["thread"] = threading.Thread(target=loop, args=(cfg,), daemon=True)
        worker["thread"].start()
        set_running(True)

    def check_now():
        if worker["thread"] and worker["thread"].is_alive():
            add_log("info", "Already tracking; it checks on its own schedule.")
            return
        cfg = current_cfg()
        if not cfg["email"] or not cfg["password"]:
            nb.select(st_outer)
            return
        stop_flag.clear()
        threading.Thread(target=loop, args=(cfg, True), daemon=True).start()

    start_btn.configure(command=start_stop)
    check_btn.configure(command=check_now)

    def pump():
        try:
            while True:
                kind, text = events.get_nowait()
                if kind == "status":
                    status_var.set(text)
                    phone["status"] = text.strip("● ")
                elif kind == "checked":
                    stat_vars["last"].set(local_time(text))
                    phone["last"] = local_time(text)
                    refresh_table()
                    if nb.select() == str(logs_tab):
                        refresh_logs()
                elif kind == "stopped":
                    if stop_flag.is_set():
                        status_var.set("● Stopped")
                elif kind == "alert":
                    toast(text)
                elif kind == "tray":
                    if text == "show":
                        root.deiconify()
                        root.lift()
                        root.focus_force()
                    elif text == "check":
                        check_now()
                    elif text == "summary":
                        send_summary(True)
                    elif text == "quit":
                        quit_app()
                else:
                    add_log(kind, text)
                    if kind in ("new", "update"):
                        refresh_table()
        except queue.Empty:
            pass
        root.after(400, pump)

    def file_stamp(path):
        try:
            return Path(path).stat().st_mtime
        except OSError:
            return None
    stamps = {"code": file_stamp(__file__), "settings": file_stamp(SETTINGS_FILE)}

    def restart_self(why):
        """Close and reopen with the new program/settings, keeping tracking on (no need to do it by hand)."""
        flags = ["--restarted"]
        if root.state() == "withdrawn":
            flags.append("--hidden")
        try:
            sys.stderr.flush()
        except Exception:
            pass
        quit_app()
        import subprocess
        here = Path(__file__).resolve()
        subprocess.Popen([sys.executable, str(here), *flags], cwd=str(here.parent),
                         creationflags=getattr(subprocess, "DETACHED_PROCESS", 0) | getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0),
                         close_fds=True)

    def watch_files():
        code, sett = file_stamp(__file__), file_stamp(SETTINGS_FILE)
        if code and stamps["code"] and code != stamps["code"]:
            stamps["code"] = code
            root.after(3000, lambda: restart_self("program updated"))   # let the copy finish
            return
        if sett and sett == OWN_WRITES.get(str(SETTINGS_FILE)):
            stamps["settings"] = sett
        if sett and stamps["settings"] and sett != stamps["settings"]:
            stamps["settings"] = sett
            root.after(1500, lambda: restart_self("settings changed"))
            return
        root.after(5000, watch_files)

    wake = threading.Event()
    quitting = threading.Event()

    def mail_watch():
        """Every 2 minutes, a quick look for new Pokémon Center emails; a new one triggers a full check
        straight away, so new parcels appear within minutes instead of at the next scheduled check."""
        seen = None
        while not quitting.wait(120):
            cfg = worker.get("cfg")
            if not cfg or not (worker["thread"] and worker["thread"].is_alive()):
                continue
            try:
                ids = new_mail_ids(cfg["imap_host"], cfg["email"], cfg["password"])
            except Exception:
                continue
            if seen is not None and ids - seen:
                events.put(("info", f"New Pokémon Center email ({len(ids - seen)}): checking now."))
                wake.set()
            seen = ids if seen is None else seen | ids

    def phone_server():
        if not settings.get("phone_view", True):
            return
        from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
        from urllib.parse import urlparse, parse_qs
        if not settings.get("phone_key"):
            import secrets
            s2 = load_json(SETTINGS_FILE, {})
            s2["phone_key"] = settings["phone_key"] = secrets.token_urlsafe(9)
            save_json(SETTINGS_FILE, s2)
        key = settings["phone_key"]

        class Handler(BaseHTTPRequestHandler):
            def send(self, body, ctype):
                self.send_response(200)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def do_GET(self):
                u = urlparse(self.path)
                q = parse_qs(u.query)
                if u.path == "/icon.png":
                    return self.send(base64.b64decode(ICON_PNG), "image/png")
                if u.path == "/manifest.json" and q.get("key", [""])[0] == key:
                    return self.send(json.dumps({
                        "name": "SID's Sorting Center", "short_name": "Sorting Center", "display": "standalone",
                        "start_url": f"/?key={key}", "scope": "/", "background_color": "#05070F",
                        "theme_color": "#05070F", "icons": [{"src": "/icon.png", "sizes": "256x256", "type": "image/png"}],
                    }).encode(), "application/manifest+json")
                if q.get("key", [""])[0] != key:
                    self.send_response(403)
                    self.end_headers()
                    self.wfile.write(b"Wrong link. Copy the phone link from the app's Settings.")
                    return
                with tracker.lock:
                    ps = [Parcel(**asdict(p)) for p in tracker.parcels.values()]
                body = phone_page(ps, phone["last"], phone["status"], key).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *a):
                pass
        try:
            srv = ThreadingHTTPServer(("0.0.0.0", PHONE_PORT), Handler)
        except OSError as e:
            events.put(("error", f"Phone view couldn't start (port {PHONE_PORT} busy?): {e}"))
            return
        srv.daemon_threads = True
        phone["srv"] = srv
        # The link that works on every phone uses the PC's home-network number; it's never shown, only copied.
        import socket
        name = re.sub(r"[^a-z0-9-]", "", socket.gethostname().lower()) or "localhost"
        phone["ip_link"] = f"http://{lan_ip()}:{PHONE_PORT}/?key={key}"
        phone["name_link"] = f"http://{name}.local:{PHONE_PORT}/?key={key}"
        phone_link.set("http://•••.•••.•.•••:8765/?key=•••••••  (hidden, press Copy)")
        threading.Thread(target=srv.serve_forever, daemon=True).start()
    phone.update({"srv": None})

    photo_job = {"busy": False}

    def photo_timer():
        """Every minute: post any new delivery photo (in the Delivery photos folder) to Discord, once each."""
        try:
            cfg = current_cfg()
            if cfg["discord"] and not photo_job["busy"]:
                sent = set(load_json(PHOTOS_SENT_FILE, []))
                todo = []
                with tracker.lock:
                    held = dict(tracker.held)
                for t, h in held.items():
                    p = tracker.parcels.get(t)
                    f = delivery_photo_file(t)
                    try:
                        waited = (datetime.now(timezone.utc) - datetime.fromisoformat(h["at"])).total_seconds() / 3600
                    except Exception:
                        waited = PHOTO_WAIT_HOURS
                    if p is None or f or waited >= PHOTO_WAIT_HOURS:
                        todo.append((p, f, h))
                if PHOTOS_DIR.is_dir():
                    for f in sorted(PHOTOS_DIR.iterdir()):
                        t = f.stem.upper()
                        if f.suffix.lower() in PHOTO_TYPES and t not in sent and t in tracker.parcels and t not in held:
                            todo.append((tracker.parcels[t], f, None))
                if todo:
                    photo_job["busy"] = True

                    def go():
                        done = 0
                        try:
                            for parcel, f, h in todo:
                                if quitting.is_set():
                                    break
                                if parcel is None:   # parcel gone: just drop the hold
                                    with tracker.lock:
                                        tracker.held = {k: v for k, v in tracker.held.items() if v is not h}
                                        save_json(PHOTO_HOLD_FILE, tracker.held)
                                    continue
                                try:
                                    if h and f:
                                        send_delivered_with_photo(cfg["discord"], h["title"], parcel, h["detail"], tracker.counts(), cfg, f)
                                    elif h:
                                        send_discord(cfg["discord"], h["title"], parcel, h["detail"], tracker.counts(), cfg)
                                    else:
                                        send_delivery_photo(cfg["discord"], parcel, f)
                                except Exception as e:
                                    events.put(("error", f"Delivery alert/photo for {parcel.tracking} not sent: {e}"))
                                    break
                                if h:
                                    with tracker.lock:
                                        tracker.held.pop(parcel.tracking, None)
                                        save_json(PHOTO_HOLD_FILE, tracker.held)
                                    if not f:
                                        time.sleep(2.5)
                                        continue   # the photo, if it comes later, is posted on its own
                                sent.add(parcel.tracking)
                                save_json(PHOTOS_SENT_FILE, sorted(sent))
                                done += 1
                                time.sleep(2.5)   # stay well under Discord's rate limit
                        finally:
                            photo_job["busy"] = False
                            if done:
                                events.put(("info", f"Sent {done} delivery photo{'s' if done != 1 else ''} to Discord."))
                    threading.Thread(target=go, daemon=True).start()
        except Exception as e:
            add_log("error", f"Delivery photos: {e}")
        root.after(60_000, photo_timer)

    def daily_backup():
        if settings.get("backups", True):
            try:
                d = backup_data()
                if d:
                    add_log("info", f"Daily backup saved ({d.name}).")
            except Exception as e:
                add_log("error", f"Backup failed: {e}")
        root.after(3_600_000, daily_backup)

    def quit_app():
        stop_flag.set()
        wake.set()
        quitting.set()
        if phone["srv"]:
            try:
                phone["srv"].shutdown()
                phone["srv"].server_close()
            except Exception:
                pass
        try:
            lock.close()
        except OSError:
            pass
        keep_awake(False)
        if tray["icon"]:
            try:
                tray["icon"].stop()
            except Exception:
                pass
        root.destroy()

    def on_close():
        if tray["icon"] and settings.get("tray", True) and worker["thread"] and worker["thread"].is_alive():
            root.withdraw()
            if not tray["hint_shown"]:
                tray["hint_shown"] = True
                toast("Still tracking\nSID's Sorting Center is in the system tray. Right-click it to open or quit.")
            return
        quit_app()

    root.protocol("WM_DELETE_WINDOW", on_close)
    root.after(200, animate)
    start_tray()
    root.after(5000, summary_timer)
    root.after(10_000, watch_files)
    phone_server()
    threading.Thread(target=mail_watch, daemon=True).start()
    root.after(20_000, daily_backup)
    root.after(25_000, photo_timer)
    if autostart or "--hidden" in sys.argv:
        if tray["icon"]:
            root.withdraw()
        else:
            root.iconify()
    ready = bool(settings.get("email") and get_secret("imap_password"))
    if ready:
        # Always tracking: start straight away (the first round is an immediate check).
        # After Windows sign-in, give Wi-Fi a moment first.
        root.after(45_000 if autostart else 1500, lambda: None if (worker["thread"] and worker["thread"].is_alive())
                   else start_stop())

    set_filter("All")
    add_log("info", "Ready. Tracking starts on its own and checks now, then every few minutes." if ready else
            "Ready. Enter your email and app password in Settings, then press Start tracking.")
    if keyring is None:
        add_log("error", "The 'keyring' package is missing, so passwords can't be saved. Run: pip install keyring")
    if not settings.get("email"):
        nb.select(st_outer)
    pump()
    root.mainloop()


# App icon: an original red-and-white ball, drawn for this app (.ico and 256 px PNG).
ICON_ICO = "AAABAAcAEBAAAAAAIAAoBAAAdgAAABQUAAAAACAAaAYAAJ4EAAAYGAAAAAAgACgJAAAGCwAAICAAAAAAIAAoEAAALhQAACgoAAAAACAAKBkAAFYkAAAwMAAAAAAgACgkAAB+PQAAQEAAAAAAIAAoQAAApmEAACgAAAAQAAAAIAAAAAEAIAAAAAAAAAQAAMQOAADEDgAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAABAE46Og0XBwNCEQUAZREFAGYXBwNCTjo6DQAAAQAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAIAAAAAf39/CBwQCnwpHBjdTUI+/2phXf9rYV3/TUM//yodGN4cEAp+cXFxCQAAAAAAAAACAAAAAAAAAAIAAAAASj81GCAUDcllWlb/y8jG//v6+v7////9/////fv7+/7Mycf/ZlxY/yEUD8tEOjoaAAAAAAAAAAIAAAACf39/CCAUDcuEe3j/////+f////79/f3/+/r6//v6+v/9/f3//////v////mHfnv/IRMOznFxcQkAAAACAAEBABsOCHljWVT/////+f7+/v/7+/v///////////////////////v7+//9/f3/////+WZcV/8cDgp9AAEBAFxFRQslGBTizMnI/f39/f349/f//////8XBwP9oX1v/Z15a/8O/vv//////+Pf3//39/P3PzMv9JxoV5E46Og0PAwBAUEZC//////7//////////8nGxv8fEgz/NSol/zYqJv8dEAv/xsPD/////////////////lNJRv8SAwBEIRYUZEk9Nf+PhHT8i4Bx/4+EdP9LPzb/OS4r//Tz8v/29fX/OzAt/0k9Nf+PhHT/ioBx/46Ec/xKPjb+IhYTaDMmFGQqJDL/EBxs/BIcZv8RHnD/Ih0z/0I2K//s7O//7u7x/0Q3Lf8iHTL/ER5w/xIcZv8QHGz8KiQ0/jMkE2g0IAA/LCg+/w459P4POvP/Djz//xk0tv8tHQ//QTMk/0I0Jf8tHQ7/GDOz/ww6//8OOvL/Djr1/iwoQf81IgBDLi5FCzEjFeEYMrL9CTPr/Qcu2f8HMur/GDKx/yElV/8hJVb/GDKv/ws16/8PNdv/CzXr/RcytP0xIxbkJyc6DQAAAQA1JAx3KihM/xpD8/lUdfX/LE/m/wcy6/8NOPD/DDfw/ws27P8ONd7/DTXk/wo28PksK0//MyMMewAAAQB/AAACSEhtBywdDclBRXL/dpb/+Tth/f0HL9//Dzbf/w413/8NNeH/Czbu/go28PkmLW3/MyMQzB8fXwh/AAACAAAAAgAAAAAuLjkWMCEPxjAuT/8VMbT/DTXh/ws27f0LNu39DTXi/xcytf8sK0//NCMQyCoqNRgAAAAAAAAAAgAAAAAAAAABAAAAACoqfwYzIgx4MyQX2ywnOf8pKlX/KSpV/ywnOv8zIxfcNCMMeiQkbQcAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAEAAAAAAAAAADMzTAo1JQQ+NyIAYTciAmE4JAQ/Li5FCwAAAAAAAAAAAAAAAgAAAAAAAAAAKAAAABQAAAAoAAAAAQAgAAAAAABABgAAxA4AAMQOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAAAAAAAD///8EQTQ0Jy8jH0AvIx9BPzMzKP///wQAAAAAAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAABKQTkfKRwWhh8TDdMmGRT2LyMe/y8jHv8mGRT3IBMN1CkcFohFPTYhAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAANSkkaSMWEfBHOzb/joeE/8K/vf/b2dj/29nY/8O/vv+PiIX/SD04/yIWEPIzKCNsAAAAAAAAAAMAAAAAAAAAAAAAAABVAAADAAAAADEkIIYqHRf/iYKA//Py8vv////9/////v///////////////v////309PP7jIWC/yseGP8wIx+KAAAAAFUAAAMAAAAAVQAAAwAAAAA0KCNmKh0X/6umpPr////+//////z7+//7+/v/+vr6//r6+f/7+/v//Pv7///////////+rqqo+isdGP8yJiFqAAAAAFVVAAMAAAABS0JCGyIUD/SKg4D9/////fv6+v/+/v7//f39///////////////////////9/f3//v7+//r6+v/////+joiF/CIVD/ZMOzseAAAAAQAAAAAoGheFRTo1//f29vv9/f3//v7+//79/f//////5eTj/62pp/+tqKb/5OLi///////+/f3//v7+//39/f/5+Pj7SDw4/yYZFooAAAAA////BB0RC9WMhYL+/////fr5+f/7+/v//////7i0sv8yJiH/FggD/xYIAv8xJCD/tbCv///////7+vr/+vn5//////2QiYb+HhEL2KqqqgZGODEkJRcS98vJyf/////+///////////s6+z/Myci/ycaFf95cW7/e3Nw/ygbFv8wJR//6ejp/////////////////8/Nzv8lGRT5PzMzKDElID4vIx7/ZFhL/3FlVv9vY1X/cWZW/1xRRv8fEw//dGxp////////////eHBt/x8SDv9bUEX/cmZX/29jVf9xZVb/ZVlM/jAkH/8xJh5DMiUhPTElHv8dHkf/GB1T/xkdT/8YHVT/IyJC/yYZD/9waGf///////////9zbGv/JhgP/yQiQf8YHVX/GR1P/xgdU/8dHkf+MSUf/zImHkIqIzEkMSMU9xgztf8MOv3+Dznt/w069/8SNtf/MCUj/y0fFP9waWr/cmtr/y4gFf8wJCD/EjbU/w059/8POe3/DDr8/xg0uf8yIhX5LCYsKAA/vwQyIw7TIy11/go28P0PNd3/DjXe/ww27P8YMKX/MCUk/yYWBf8mFgX/MCUi/xkwov8LNuz/DjXe/w413f8KNvD9Ii15/jMiDtczM8wFAAAAADAjF4MxKDH/DjTc+wky5P8LM+H/CTHg/wo17f8RNM//HTGa/x0xmv8RM87/Czbt/w014f8NNeL/DTXl/w003vsxKTT/MiMWiAAAAAAAAAABMSc6GjQjEfIeKHD9H0r7/WF/9v9JavP/DjXh/ww15/8LNvH/Czbx/ww16P8NNeH/DTXi/w413/8JNvb9ISx2/DMjEfQtJDYcAAAAAVVVAAMAAAAANCkkYi8gFv9EUpz7e53//WeG//8SOOH/DTTf/w413v8ONd7/DjXf/w413/8NNeX/Cjb0/hstk/o2Jhn/LyUiZwAAAABVVQADAAAAAFUAAAMAAAAALyMfgjUlGP86QXj/GT7f+wg08f0LNu7+Czbr/ww26/8LNu7+Cjby/Q003fsiLHT/NSYY/y8kIIYAAAAAVQAAAwAAAAAAAAAAAAAAAFUAAAMAAAAALyMjZS8fEO4uJjH/Iy13/xgwqv8TMr//EzLA/xgwqv8iLXj/MSgz/zQkEu8uJCJoAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAAANi0/HDQlGYIzIw7PMiMU9DEkHf8xJB3/MiMU9DQjDtE0JBeEKiI7HgAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAAAAAAAAD//wErJDMjLyYiOy4mIjwxIzEkAH//AgAAAAAAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAAoAAAAGAAAADAAAAABACAAAAAAAAAJAADEDgAAxA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVQAAAwAAAAAAAAAAAAEBAF9fTxBPPz8gTT09IV9fTxAAAQEAAAAAAAAAAABVAAADAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAEQ3MSk0KCR/KBsWwSIWEOUhEw7zIRMO9CIWEOUoGxbDMycjgUE1LysAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVQAAAwAAAAA8MDAVNCkkmiUYE/osHxn/TkM+/3JqZv+Jgn//iYJ//3NrZ/9PRD//LR8a/yUYEvszKCOdNywsFwAAAABVAAADAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAADkrKzUvIh3eKRwW/2xjYP/Kx8b7+vr6/P////7////+/////v////77+/v8zMnH+25mYv8qHBf/LiIc4TUsKDkAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAIAAAAANy0oMy0gG/A1KCP/tbGv+v////////////////39/P/8/Pz//Pz8//38/P////////////////+4tLP6Niol/y0gG/I3Lik3AAAAAH8AAAIAAAAAAAAAAQAAAAI4OCoSLiIc4TQnIv/Qzcz7//////z8/P/9/fz//v7+///+/v/9/f3//f39///+/v/+/v7//f39//z8+///////0tDP/DYpJP8tIRvkPDAwFQAAAAIAAAACVVUAAwAAAAAzKCOZKRsV/7i0svr/////+vr6/////////////f39///////////////////////9/f3////////////6+vr//////7u4tvspHBb/MychoAAAAABVVQADAAAAAD84MSQkGBL7a2Jf/f////77+/v////////////9/f3////////////j4eH/4+Hg/////////////f39////////////+/v7//////5vZ2P9JBgS/D85MygAAAAAAAAAADMoIn0rHRj/zMnI+/7+/v/8/Pz///////39/f//////xcLB/1VLR/82KiX/Niol/1NJRf/Cv77///////39/f///////Pz8//7+/v/Qzs37LB8Z/zImI4MAAAAAAQEBACgbFsFMQTz/+/v7/P/////+/v7//fz8///////IxMP/KR0Y/yMWEP8kFxL/JBcS/yMWEf8oGxb/xMG////////9/Pz////+//7+/v/9/f38UEVA/ycbFcYBAQEAf2pqDCIVD+NyaWf//////v7///////////////7+//9YTkr/IhUQ/0Y8N/+yrqz/tLCu/0g+Of8jFhH/VEpG//39//////////////7////////+dm5r/yIUD+dfX18QOyoiHi0gHfFAMyz/V0s+/lZKPv9WSj7/V0s//1NHPP80KCP/IxcR/7Ktq////////////7aysf8kFxL/Myci/1NHPP9XSz//Vko+/1ZKPv9XSz/+QTQs/ywhHfU6KyQjMyIiHjEjHfErIiv/IB8//iEfPP8hHz3/IR8+/yIfOv8zJyP/IxYR/7Crqf///////////7Wwrv8jFxL/Mycj/yIfOf8hHz7/IR89/yEfPP8gHz/+KiIs/zEkHfQtJR4iKipVDDIiEeMnK1//DDjz/g435v8ON+n/Djfo/w047f8qKUf/LiAR/z41Nf+tqaf/r6up/0E3N/8uHxL/KyhD/w436/8ON+n/Djfo/w435v8MOPT+Jitj/zIiEecfH08QAAABADEkGL8uKDj+DTTg/A014/8NNeL/DjXg/ww27P8VMbT/MiUb/y8gEf8kFhD/JBcR/y4fEf8yJBn/FjCw/ws27P8ONeD/DTXi/w014/8NNOL8Lig8/zEjF8QAAAEAAAAAAC8lI3s1Jhn/FTCx+ws27v8ONuD/CzTj/ww04P8MN+3/FTG0/yooR/8yJyf/Micn/yooRv8WMLH/Czbt/w014f8NNeP/DTXg/ws27f8VMLX7NSYa/y8jIYEAAAAAAAAAAC0lNCIzIxT6JilV/Qs27v4JMd//Ezrk/xE45P8KMuD/DDbs/ww16P8RM8z/ETPM/ww15/8LNu3/DTXh/w014/8NNeP/DjXg/ws27/4mKVn9MiMU+y4oLiYAAAAAVVUAAwAAAAAvIyKWNycX/xQqm/ooUf3/aYb5/2OC+/8gRun/CjLg/w424v8MNej/DDXp/w014v8NNeH/DTXj/w014/8ONd7/Cjb0/xguofo2Jhf/LyMinAAAAABVAAADAAAAAQAAAAIvHy8QMiUd3isfH/9MYsb7eZv//3yY//81WOz/Bi/h/w824/8NNeL/DTXi/w014/8NNeP/DTXg/w414P8KNvT/FDG5+zImI/8xJB3iNSgoEwAAAAIAAAACAAAAAAAAAAIAAAAAMCUrLzEjG+42KSP/SVmo+jRb+v4MNu7/DTXk/w414f8ONeD/DjXg/w014f8NNeT/Czbt/ws27/4YLqD6MiYj/zMlG/AtIygzAAAAAAAAAAIAAAAAAAAAAAAAAABVAAADAAAAAC4kKTExJB3aLyAV/yAjU/8VMLH7DTTh/As27f4KNvD+Cjbw/gs27v4NNOH8FTCz+yYpWP81Jhf/MSQe3SshJjUAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAVQAAAwAAAAAqKioSMycjlTQlFPc1Jhn/Lig5/ycqXP8iLHD/Iixw/yYqXf8uKDr/NSYZ/zMjFPkwJCOYJiYmFAAAAABVAAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAADApMCUwJSN6MiQYvDMjEuEzIxHwMyMR8DMjEuExJBi9MSUifC0nLScAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVQAAAwAAAAAAAAAAAAAAACoqVQwtJD8cLSQ/HCoqagwAAAAAAAAAAAAAAABVAAADAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAKAAAACAAAABAAAAAAQAgAAAAAAAAEAAAxA4AAMQOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAJVAAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAACAAAAAAAAAAAxKSAfNiolWTYpJow1KSStNSkkvzQpJL82KiSuNSkljjUqJFs3Jx8gAAAAAAAAAAAAAAABAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAAAAAAAAxJh9INSkjsjMmIfUtIBv/JxkT/yQWEf8kFxH/JBcR/yQWEf8nGRP/LSAb/zImIfc1KiS1MyUiSwAAAAAAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz8ABAAAAAAwIhslNSgisjMnIv8mGRT/KBsW/0g+Ovx1bWr7lpCN/Kijofyoo6H8lpGO/HZua/tKPzv8KRwX/yYZE/8zJyH/NSgjtislHykAAAAAPwAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/AAQAAAAALiIfUjUoJO4sHhn/KR0Y/XFoZfzFwsH++Pf3//////////////////////////////////n4+P/IxMP+c2xo/CoeGfwrHhj/NCkj8S4iHFgAAAAAPwAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/AAAEAAAAADAkHmM2KST/JBcS/01DPvvIxcP//////////////////fz8//z7+//8/Pv//Pz7//z7+//8/Pz/////////////////y8jH/1FHQ/sjFhH/Niok/zEkH2gAAAAAPz8ABAAAAAAAAAAAAAAAAAAAAAAAAAAAVQAAAwAAAAAwIx1PNikk/yMWEP1rY1/99PPz///////8/Pz//f38//7+/v/////////////////////////////////+/v7//f39//z8/P//////9vb1/3BoZP0iFRD8Niok/y8jHVYAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAIAAAABLx8fIDUoJPAlFxL9amJe/f7+/v///////Pz8//////////////////////////////////////////////////////////////////z8/P///////////3BoZf0kFxH9NSgj9DAiGyUAAAABAAAAAgAAAAAAAAAAfwAAAgAAAAAzJiKzLB8Z/0tBPPv19PT//v7+//39/f///////////////////////v7+//z8/P/8+/v//Pv7//z8/P/+/v7///////////////////////39/f/+/v7/9/f3/09FQfwrHhn/MiciuwAAAAB/AAACAAAAAFVVAAMAAAAALycfQTQnIv8oHBb8y8jH///////8/Pz///////////////////////39/f/////////////////////////////////9/f3///////////////////////z8/P//////0c7N/ykdGPw0JyL/MSYfSAAAAABVVQADVQAAAwAAAAAzKCSxJxkU/m9nY/v//////Pz8///////////////////////9/f3///////v7+//Cvr3/m5WT/5qVkv/AvLv/+vn5///////9/f3///////////////////////z8/P//////dW1q/CYYE/40JyO5AAAAAH8AAAIAAAAAMygeGTMmIfUnGhX/xsPB/v7+/v/8/Pz//////////////////f39///////Mycf/TEI9/yUYE/8kFxL/JBcS/yQYE/9KPzv/yMTD///////9/f3//////////////////Pz8//7+/v/Mycj+KBwW/zIlIPkzIiIeAAAAAAAAAAAzKiRULiEb/0U7Nvz29vb//f39//39/f/9/f3//f39//v7+//+/v7/zsvK/y0hHP8nGxb/NCgj/ykdF/8pHBf/NCgj/ygcF/8rHhn/ycbE///////7+/v//f39//39/f/9/f3//f39//n4+P9KQDv8LSAa/zQpJFwAAAAAAAAAADQpJYcnGRP/dW1q+/////////////////////////////////7+/v9PRUH/JxsV/zQoJP8tIRz/Y1pX/2VcWP8uIh3/NCgj/ygcF/9KQDv//Pv7/////////////////////////////////3t0cfsmGBL/NSoljwAAAAAAAAAANCgkqicZE/+Benf84N7e/9za2f/e3dz/393c/9zb2v/g397/sq6s/ygbFv80KCP/LSAb/7eysf///////////7y4tv8uIh3/NCgj/ycaFf+tqaf/4N/e/9za2v/f3dz/3t3c/9za2f/g3t7/hoB9/CYZE/8zKCSxAAAAAAAAAAAvIx+6MyYh/zAlH/wxJR//MSQe/zEkHv8xJB7/MCQe/zElH/8uIh3/Mici/yYaFP9gV1P///////z8/P/8+/v//////2Zd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FPsmGRT7IxYR+yEUD/wjFhH/Kx8a/zUoI/81KST/MiYg1jIkH2ozMzMFAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFVAAADAAAAADEjHzkxJB/INikk/zImIP8jFxH9JhoV+0c8OP10bGn+nZeV/7ezsv/FwsD/xcLB/7i0sv+emZb/d25r/kk+Ov0nGxX8IxYR/TElIP82KiT/MiUgzDElID4AAAAAVQAAAwAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFVAAADAAAAADAkIG8xJSD6NSkk/yQYE/stIRv9cWlm/8PAvv/29fX////////////////////////////////////////////39/f/xsLB/3Vtaf8uIx39JBgS+zUpJP8yJiH9MSQedgAAAAAAAAACAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFVAAADAAAAADAjHo41KCP/MSUg/iEVEPxhWFT/0c/N//////////////////38/P/8/Pv//Pz8//z8/P/8/Pz//Pz8//z8+//8/Pz/////////////////1dLR/2ZdWf8iFRD8MCQf/TUpI/8vIx6VAAAAAFUAAAMAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/PwAEAAAAADAjHo42KSP/LiId+igcF/6alJH////////////9/Pz//fz8//7+/v////////////////////////////////////////////7+/v/9/fz//Pz8////////////n5qX/yoeGf4tIRv6Nikk/y8jHpUAAAAAPz8ABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAAC8jHmw1KCP/LiId+i0hHP66trT///////39/f/9/f3////////////////////////////////////////////////////////////////////////////9/f3//f39///////AvLv/MCQf/ywhHPo2KSP/LyUedQAAAABVVQADAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAADMjHjIxJSD7MSUg/CcbFv66trX///////v7+//////////////////////////////////////////////////////////////////////////////////////////////////7+vr//////8G+vP8pHRj+MCQf+zImIf0wIx46AAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAlUAVQMvJB7KNikk/yEUD/yblJL///////v6+v////////////////////////////////////////////////////////////////////////////////////////////////////////////v6+v//////op2b/yIVD/w1KST/MCQf0yoqKgYAAAACAAAAAQAAAAAAAAAAPz8ABAAAAAAwIyBeNikk/yUYE/tfVlL///////z8+//+/v7//////////////////////////////////v7+//z8/P/9/f3////////////9/f3//Pz8//7+/v///////////////////////////////////////Pv7//////9mXVn/JBgS+zYqJP8xJSBnAAAAAD8AAAQAAAAAAAAAAAAAAAE/PwAEMCQf1DMmIf4rHxn91NLR///////9/fz//////////////////////////////////f39/////////////////////////////////////////////f39//////////////////////////////////39/f//////29jY/y4iHf0yJSD+MCUf3CQkJAcAAAABAAAAAVUAAAMAAAAAMCUeRDUpI/8jFxH9b2dj///////9/Pz//////////////////////////////////f39///////49/f/q6ak/2xkYP9SSET/UkhE/2tiX/+oo6H/9fX1///////9/f3//////////////////////////////////fz8//////93b2v/IhYQ/DYpJP8xJCFNAAAAAD8/AAQ/PwAEAAAAAC8kH5s2KST+JRgT+8K+vf/+/v7//Pz8/////////////////////////////f39///////Sz8//S0E9/yEUD/8kGBL/KRwX/ykcF/8lGBP/IBQO/0g9OP/Oy8n///////39/f////////////////////////////z8/P/+/v7/ycfF/ycaFfs1KCP+MCUfpAAAAABVVQADAAAAAD8/PwQxJSDaLSAb/0Q5Nf329fX///////7+/v///////////////////////f39///////U0tH/Myci/yYaFf80KST/Niol/zImIf8yJiH/Niol/zQpJP8nGxb/LyMe/87Myv///////f39///////////////////////+/v7///////n5+f9KPzv9Kx8Z/zEmIOI/Hx8IAAAAAAAAAAAxIxwkMyci+yQXEv9uZmP+/f38//r5+f/8/Pz//Pz7//z8+//8/Pv/+/v7//v6+v/29vb/T0VA/yYZFP81KST/Mici/yQXEv8tIRz/LiIc/yQXEv8yJiH/NSkk/ycbFf9JPjr/8/Pz//v7+v/7+/v//Pz7//z8+//8/Pv//Pz8//n5+f/8/Pz/dm5q/yMWEf80JyL+LyMdKwAAAAAAAAAAMCQhRTYqJP8gEw79oZuZ////////////////////////////////////////////trKw/yATDv80KST/MiYh/ysfGv+GgH3/19TT/9jW1f+LhYL/LSAb/zImIf81KST/IBMN/62pp////////////////////////////////////////////6qlov8gEw78Niol/zEjHU4AAAAAAAAAADAkHmM1KSP/JxsW+3tzcP+tqKb/qaSh/6qlo/+qpaP/qqWj/6qlo/+ppKH/rKel/1tSTv8oHBf/NSkl/yQXEv+DfHn//////////////////////4uFgv8kFxL/NSkk/ykcF/9XTUn/rKel/6mkov+qpaP/qqWj/6qlo/+qpaP/qaSi/6yopv9/eHX/JxsW+zUpI/8xIx5tAAAAAAAAAAAwJB1vNCch/zAkH/snGxf/IRUT/yEVE/8hFRL/IRUS/yEVEv8hFRL/IRUT/yEVE/8rHxv/MSUg/zElIP8qHhn/1tPS//39/P/7+/r/+/v7//z8/P/c2tn/LiIc/zAkH/8xJSD/Kx8b/yEVE/8hFRP/IRUS/yEVEv8hFRL/IRUS/yEVE/8hFRP/JhoX/zAkH/s0JyH/MCMfeQAAAAAAAAAAMCQdbzQnIf8vIx/7MyUZ/zYmFf81Jhb/NiYW/zYmFv82Jhb/NiYW/zUmFv82JhX/MiUc/zAkIP8xJSD/Kh4Z/9TS0f/9/f3/+/r6//v6+v/9/f3/29nY/y0hHP8wJB//MCQg/zIlHP82JhX/NSYW/zYmFv82Jhb/NiYW/zYmFv81Jhb/NiYV/zMlGf8vIx/7NCch/zAjH3kAAAAAAAAAADEkH2IzJyP/MSIW+yIqa/8YL6P/Gi+Z/xovm/8aL5v/Gi+b/xovm/8aL5n/GC+j/ygoTP8xIxf/Mygk/yQYEv9/d3T//////////////////////4Z/fP8kFxL/Myck/zEjGP8pKEj/GC+i/xovmf8aL5v/Gi+b/xovm/8aL5v/Gi+Z/xkvo/8hK3D/MSIX+zMnI/8xIx5sAAAAAAAAAAAwJR5EMiYk/zIiD/0dLYr/CDf//ww27f8LNvD/Czbw/ws28P8LNvD/Czbt/wg3/f8ZL6H/MyMR/y8kI/8zJyL/Kx4Z/394dP/Qzs3/0s/O/4R8ef8rHxr/Mych/y8kI/8zIxD/Gi+Z/wg3/v8LNu3/Czbw/ws28P8LNvD/Czbw/ww27f8IN///HC6S/zIiEPwyJyT/MSQdTQAAAAAAAAAANCUeIi8kIfsyIxP/JSla/gw26/8ONd7/DjXg/w414P8ONeD/DjXg/w014P8NNeD/DTXi/yonQf8yIxT/MCUk/zMnIv8kGBL/Kx4Z/ysfGf8kFxL/Myci/zAlJP8yIxX/KyY6/w414P8NNeH/DTXg/w414P8ONeD/DjXg/w414P8ONd3/Czbs/yQqYf8yIxL/MCUi/jAkHioAAAAAAAAAAD8/PwQwJCHYMiUc/ywlMf0PNNr/DTXl/w014v8NNeP/DTXj/w014/8NNeP/DTXh/ww26/8TMsP/LyUm/zIjFP8vJCP/Mygl/zElIv8xJSL/Mygl/y8kI/8yIxX/MCQi/xQyvv8LNuz/DTXh/w014/8NNeP/DTXj/w014/8NNeP/DTXk/w413/8rJjb9MiQa/y8kIeAkJCQHAAAAAD8/AAQAAAAAMCQfmDMnI/4xIhT7FzCo/ws27/8NNeD/DTXj/w014/8NNeP/DTXj/w014/8NNeD/Czbt/xIyw/8qJ0D/MyMR/zIjE/8yIxf/MiMX/zIjE/8zIxH/Kyc9/xQyv/8LNu7/DjXg/w014/8NNeP/DTXj/w014/8NNeP/DTXh/ws27v8WMK//MSMW+zMnI/4xJB+hAAAAAD8/AARVAAADAAAAAC8jH0AxJiP/MiMT/SYpWP8LNu7/DjXg/w014/8NNeP/Djbj/w424/8ONuP/Djbk/w014P8MNuv/DTXj/xkvnv8kKmH/KSdG/yknRf8lKl//Gi+b/w014f8MNuz/DTXg/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w414P8LNvD/JCpg/zIjEv0yJiP/MCUfSgAAAAA/AAAEAAAAAAAAAAFVAAADMCQf0TImIf4xIxn8FTG4/ws27f8ONeD/CzTj/wYv4f8JMeL/Bi/h/wsz4v8ONuP/DTXh/w014/8LNvD/Czbv/ww15/8MNef/Czbv/ws28P8NNeT/DTXh/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014P8LNuz/FDK+/zAkHP0xJSD+MCQf2CoqKgYAAAABAAAAAQAAAABVVQADAAAAADAlH1kzJyP/MSIV/CkoSP8MNun/CzPi/xI55P9DZfL/V3f3/0Zo8/8VPOX/CjPi/w424/8NNeP/DjXg/w014P8NNeL/DTXi/w014P8ONeD/DTXi/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeH/Czbr/ygoT/8xIhT7Myck/zEkH2IAAAAAPz8ABAAAAAAAAAAAAAAAAAAAAAIAAAACLyQfxTImJP8yIhH8Hy1//wg18/9Uc/P/eZb//3GP//94lf//Wnr5/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8ONd7/Cjb0/x4thv8yIhH8MiYk/zAjHs4/PwAEAAAAAgAAAAAAAAAAAAAAAAAAAABVAAADAAAAADMnIi0xJSD4MCUh/DAhFf4gNaD/aYz//26L+/9qif7/bIr+/3CO//8ZQOf/CjLi/w424/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8ONd//Cjb0/xgwpf8xIxj+MCQg/DElIPwwJiE1AAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAALyMeZTMnI/8wJB76LSAY/lNksP91l///dJH//3mV/v9PcPb/CzPi/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014P8NNeL/Cjb0/xgwpP8wJB3+LyMd+jQnI/8wJR5uAAAAAFVVAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz8ABAAAAAAvJB6GNCcj/y8jHfswIhf+Q02I/0Zp9f8zWfj/DjXh/wwz4P8ONeL/DTXj/w014/8NNeP/DTXj/w014/8NNeP/DTXj/w014/8NNeL/DTXg/w014P8LNuz/DDbr/x4thP8xIxf+MCMd+zQnI/8wIx6OAAAAAD8/AAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAAC8kHoUzJyP/MCQg/ywdD/wiIUf/Diu2/ws27v8LNu//DDXl/w014f8ONeD/DjXg/w014P8NNeD/DjXg/w414P8NNeH/DTXl/ws27v8LNu//FDK7/ygoTP8yIhH8MCQg/jMnI/8wJR6NAAAAAFUAAAMAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAAMSUgZzElIfczJyT/MiQW/DIkGf0mKVn/FzCo/w802v8LNu7/Cjbx/ws28P8LNu//Czbv/ws28P8KNvH/Czbu/w403P8XMKv/JSlc/zAjGv0xIhX7MiYk/zEkIPkxJR5tAAAAAFUAAAMAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVVUAAwAAAAAuJB8xMSUfwDMnI/8yJSH/MiMT/TEjFPssJTH9JSlb/h8tgf8aL5r/GDCn/xgwp/8aL5v/Hi2D/yUpXf4sJTP9MSMU+zIjE/0yJSH/MyYk/zElIMUuJSA3AAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAAAAAAAAxJB5cMiQgyzImI/8zJyT/MiUc/zIjE/8yIhD9MiIS/DEiFPsxIxT7MiIS/DIiEP0yIxP/MiUb/zMnI/8yJiP/MSQgzzEkH2EAAAABAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAABAAAAAAAAAAAxJh5DMSUgljElINUvJCH6MiYk/zMnJP8zJyT/Myck/zMnJP8yJiT/LyQh+zAkIdcyJB+ZMyQgRgAAAAIAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAACNCUeIjAlHkQxJiBdLiMebTEjIG0wJSBeMCQdRTMkHSNVAAADAAAAAAAAAAAAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVUAAAM/PwAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/AARVAAADAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACgAAAAwAAAAYAAAAAEAIAAAAAAAACQAAMQOAADEDgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVUAAAM/Pz8EVQAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVQAAAz8/PwRVAAADAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAE/PwAEAAAAAAAAAAAAAAAAAAAAAFUAAAM5IiIWLiEhJjQkHzE0JB8xLSAgJzcsIRc/Pz8EAAAAAAAAAAAAAAAAAAAAAD8/AAQAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVQAAAwAAAAAAAAAAAAAAATMlITYxJiB3MCUfsTAkH9kwJB/wMCQf/jIlIP8yJSD/MCQf/jAlH/ExJB/aMCUgszElH3sxKB85VQAAAwAAAAAAAAAAVQAAAwAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAAAAAAADUqHxgxJCB2MSQgzzElIP81KCP/Nikk/zUpJP8zJyL/MSUg/y8jHv8vIx7/MSUg/zMnIv81KSP/Nikk/zUoI/8xJSD/MSQf0zElH3stJBscAAAAAAAAAABVAAADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVQAAAwAAAAAzIiIPMyUfgTElH+o0JyL/NSgj/zImIf8qHhn7IxYR/CEUD/0lGRT+LCAb/jElIP8xJSH/LCAb/iYZFP4hFQ/9IhYR/CoeGfsyJiH+NCgj/zQnIv8xJSDuMyUghzUoGhMAAAAAVQAAAwAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAABAAAAADAjIE8yJSDbNCch/zQoI/8vIx77IxcS/SYaFf9FOzb/dGxo/6Gbmf/Bvrz/1NLR/9/d3P/f3d3/1dPR/8O/vv+inZv/dm5r/0c9OP8nGhX/IxYR/S4jHvszKCP/NCch/zIlH+AyJiBWAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAABMSQfizImIP8zJyH/MSYh+yQXEv4vIx7/cWll/8C8u//09PP///////////////////////////////////////////////////////b29f/DwL7/dWxp/zElIP8jFxH+MSUh+zMnIv8yJiD/MiQhkj8/AAQAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACAAAAADMzGQowJR+yNCYh/zInIvwsIBr9JhkU/25mY//X1NP//////////////////fz8//z8/P/8/Pz//f39//39/f/9/f3//f39//z8/P/8/Pz//Pz8/////////////////9rY1/9za2j/JxoV/yseGf0yJyL8Mych/zEkH7s6JycNAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAABMxkZCjAkH7wzJiH/NCci+iYaFP87MCv/t7Ox/////////////f39//38/P/+/v7///////////////////////////////////////////////////////7+/v/9/Pz//fz8////////////vbm4/z80MP8lGRP/Myci+jMmIf8xJB/DJycnDQAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVUAAAMAAAABMCUfszMmIf80JyL6IxcR/1VLR//j4eD///////z8/P/9/f3///////////////////////////////////////////////////////////////////////////////////////39/f/8/Pz//////+jm5v9bUU3/IxYQ/zQnIvozJiH/MSQfuz8/PwRVAAADAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVVUAAwAAAAAwIx+JNCch/zQnIvokFxH/YFdT//X09P//////+/v7/////////////////////////////////////////////////////////////////////////////////////////////////////////////Pz8///////4+Pj/aF9c/yMWEf80JyL6MyYh/zAkH5QAAAAAPwAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVAAADAAAAADEjH0gyJiD/Mici+yYaFf9USUb/9PT0///////9/Pz///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////39/f//////+Pj4/1tRTf8lGRP/Myci+zMmIf8xJR9SAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAAAACLi4uCzAkH90zJyH+LCAb/TkuKf/k4+L///////38/P/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////9/f3//////+rp6P8/My//Kx8a/TMmIv4wJB/lLR4eEQAAAAIAAAABAAAAAAAAAAAAAAAAAAAAAFVVAAMAAAAALyUfezMnIf8xJiH7JBgT/7m0s////////Pz7/////////////////////////////////////////////////////////////f39//38/P/9/Pz//f39///+/v///////////////////////////////////////////////////////Pz8///////Bvr3/JhoU/zElIfszJyH/MSMehwAAAABVVQADAAAAAAAAAAAAAAAAAAAAAQAAAAA1KBoTMCQf7DMoI/4kFxL+bGNg///////8/Pz//////////////////////////////////////////////////v7+//z8/P/////////////////////////////////8/Pz//v7+//////////////////////////////////////////////////z8+///////dW1p/yMWEf4zKCP9MCQf8jMoHhkAAAAAAAAAAgAAAAAAAAAAPz8ABAAAAAAwJCBvNCci/zAkH/wtIRv/2NbV///////9/f3////////////////////////////////////////////9/f3/////////////////4N7d/8vIxv/Kx8b/3tzc//39/f////////////39/f////////////////////////////////////////////39/f/+/v7/4N7d/zElIP8vIx77NCci/y8lH3sAAAAAPz8ABAAAAAAAAAAAAAAAAQAAAAIwIx7ONSgj/iMXEvxuZWL///////39/f////////////////////////////////////////////39/f//////9/f2/52Xlf9SR0P/MSUh/ygcF/8oHBb/MSUg/09FQf+Zk5D/9PTz///////9/f3////////////////////////////////////////////9/fz//////3Zva/8iFhH9NSgj/jAjINczMzMFAAAAAQAAAAEAAAADAAAAADMnIi0xJSD9MiYh/iQYEv++urj//v7+//z8/P///////////////////////////////////////f39///////Z19b/TkQ//yATDv8pHBf/LyMe/zImIf8yJiH/MCQf/ykdGP8gEw7/ST46/9TR0P///////f39///////////////////////////////////////8/Pz//v7+/8fEwv8nGhX/MiYh/jElIP8zJSA3AAAAAFUAAAM/Pz8EAAAAAC8kH3A0KCL/Kx8a+0E2Mv/z8vL///////7+/v/////////////////////////////////9/f3//////9vZ2P85Lin/JRkU/zUpJP8yJiH/MiYh/zMoI/8zKCP/MiYh/zEmIf80KST/JxoV/zUpJP/U0tH///////39/f/////////////////////////////////+/v7///////j39/9IPjn/KR0Y+zUoI/8xJR58AAAAAD8/PwRVAAADAAAAAC8jH6s2KST/IxcR+25mY////////f39//////////////////////////////////7+/v/+/v7/9/f3/1FHQ/8lGBP/NCkk/zAkH/80KCP/Kh4Z/yIVEP8iFQ//Kh4Y/zQoI/8wJB//NCgj/ycaFf9KQDv/9PPz//7+/v/+/v7//////////////////////////////////fz8//////94cG3/IhUQ/DYpJP8xJB61AAAAAAAAAAIAAAAAAAAAATAkH9M1KST/IRQP/ZmTkP/8/Pz/+fn5//38/P/9/Pz//fz8//38/P/9/Pz//fz8//n5+f/9/f3/pqCe/x8SDf81KST/MCQf/zcrJ/8mGRT/TEE9/4Z/fP+IgX7/T0VB/yUZE/82Kyb/MCQf/zUpJP8gEw3/m5aT//7+/v/5+fn//fz8//38/P/9/Pz//fz8//38/P/9/Pz/+fn5//z8/P+inJr/IRQP/TUpI/8wIx/cMzMABQAAAAAAAAAALx8fEDAkH+s0KCP/JBcS/sPAvv//////////////////////////////////////////////////////V05K/ygbFv8yJiH/NCgj/yYZFP95cW7/9/b2////////////+fn5/4F6d/8mGRT/NCgj/zElIf8pHRj/UEVB///////////////////////////////////////////////////////Nysn/JhkU/jMnIv8wJB/yNyEhFwAAAAAAAAAAMSMcJC8kH/wxJSD/LSEc/mFXVP9za2f/cGhk/3FpZf9xaWX/cWll/3FpZf9xaWX/cGhl/3JqZv9sZGD/Myci/y8jHv8yJiH/Kx8a/0g9OP/6+vr///////v7+//7+/v///////7+/v9PRED/Kh4Z/zImIf8wJB//MSYh/2phXv9yamb/cGhl/3FpZf9xaWX/cWll/3FpZf9xaWX/cGhl/3NrZ/9jWlb/LiId/zAkH/8xJSD+MyIcLQAAAAAAAAAALScgJzAkH/8wJB//MSUf/iYaF/8jFxT/IxcU/yMXFP8jFxT/IxcU/yMXFP8jFxT/IxcU/yMXFP8kGBX/MCQf/zAkH/8zJyP/IhUP/4B6dv//////+/v7////////////+/v7//7+/v+Kg4D/IRQP/zMoI/8wJB//MCQf/yQYFv8jFxT/IxcU/yMXFP8jFxT/IxcU/yMXFP8jFxT/IxcU/yMXFP8mGhb/MCQf/zAkH/8xJSD/MyMeMgAAAAAAAAAALCYfKDAkH/8wJB//MCQf/jQlF/81JhT/NSYV/zUmFf81JhX/NSYV/zUmFf81JhX/NSYV/zUmFf81Jhb/MCQf/zAkH/8zJyL/IhUQ/394df//////+/v7////////////+/v7//////+IgX7/IRUP/zMoI/8wJB//MCQf/zUmFv81JhX/NSYV/zUmFf81JhX/NSYV/zUmFf81JhX/NSYV/zUmFf80JRf/MCQf/zAkH/8xJSD/MyMeMgAAAAAAAAAAMyQdIy8kH/swJCD/MCQc/iYoVP8jKmn/Iypl/yMqZf8jKmX/Iypl/yMqZf8jKmX/Iypl/yMqZ/8lKmD/LyQj/zAkHv8xJiH/LCAb/0Q6Nf/49/f///////v7+//7+/v///////z8/P9LQTz/Kx4Z/zIm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Hv8zJyL/MCQf/S8jH/wyJiH/MSUg+zIlH4kqKioGAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/AAQAAAAAMSkgHzElIL00JiL/MCQf/y8jHvwzJyL/MCQf/yMWEf8wJCD/bmZi/7q2tP/w7+///////////////////////////////////////////v/////////////////////////////////z8vL/vrq5/3NraP8zJyL/IhUQ/y8jHv8zJyL/LyMf/DAkH/4zJyH/MiUgxi4hISYAAAAAPz8ABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8AAAQAAAAALiIdPDIlIOMzJiH/LyMe+zElIP4zJyP/JhkU/y4iHf9+dnP/2tjX//////////////////39/P/8/Pz//f39//7+/v/+/v7////+///////////////+//7+/v/+/v7//f39//z8/P/8/Pz/////////////////393c/4R+e/8xJSD/JRgT/zMnIv8xJSD+LyMe+zImIf8yJSDqLyQgRgAAAAA/PwAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/AAQAAAAAMSMfSDElIPYxJSD/LyMe+zImIf8wIx7/IhYQ/2JZVf/U0dD////////////9/f3//Pz8//7+/v////////////////////////////////////////////////////////////////////////////7+/v/8/Pz//f38////////////2dfW/2lhXP8jFxH/LyId/zMnIv8vIx78MSUg/zElIPsxJR9SAAAAAD8/AAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAAMSMfSDElH/gxJSD/LyMe/DMnI/8qHhn/LiId/6Gbmf////////////z8/P/9/f3////////////////////////////////////////////////////////////////////////////////////////////////////////////+/f3//Pz8////////////qqWj/zImIf8pHRf/Mygj/y8jHv0wJCD/MSUg/TElH1IAAAAAPwAABAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFUAAAMAAAAAMiQfODElIPUxJB//LyMe/TQoI/8mGhT/QTYy/83Kyf///////f39//39/f/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////9/f3//f39///////W09L/SD05/yUYE/80KCP/LyMe/TAkH/4xJSD6MCUeRAAAAABVVQADAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAAAABMScdGjEkIOQxJSD/LyMe/DMoI/8lGRP/T0VB/+Xk4///////+/v7///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////7+/v//////+vq6f9YT0v/JBcS/zQoI/8vIx79MSUg/zEkIO0xIyMkAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFVAAADfwAAAjAkH7wzJiH/LyMe/DMnIv8mGhX/T0RA/+3s7P///////Pz8//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////z8/P//////8/Py/1hPS/8lGBP/NCgj/y8jHvwyJiH/MCQfyUgkJAdVAAADAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABVVQADAAAAADAjH3k0JyH/LyMe+zImIf8qHhn/QDQw/+Xk4////////Pz8/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////f38///////t7Oz/Rz04/ykdF/8zJyL/LyMe+zMnIf8wIx+JAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB/AAACAAAAATMmHygxJSD3MCQf/DAlIP4wJB//LCAb/87Myv///////Pz7///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////8/Pz//////9nW1f8xJSD/LiId/zElIP4wJB/8MSUg/DEnHTQAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfwAAAgAAAAAwIx+zMyYh/y8jHvwzKCP/IhUQ/6Cbmf//////+/v7//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////z7+///////raim/yMWEf8zJyL/LyMf/DMmIf8wJB/BAAAAAX8AAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVQAAAwAAAAAzJx9BMiYh/y8jH/wzJyL/JhoU/15VUf/+/v7//Pz8/////////////////////////////////////////////////////////////////////////////////////////////v7+//7+/v/+/v7//v7+/////////////////////////////////////////////////////////////////////////////////////////////Pz7//////9qYV3/JBgS/zMnIv8vJB/8MyYh/zMjH1AAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH8AAAIAAAAALyQfuzImIf8wJB/8MSUg/ysgGv/V0tH///////39/f////////////////////////////////////////////////////////////////////////////7+/v/8/Pz//f39///////////////////////9/f3//Pz8//7+/v////////////////////////////////////////////////////////////////////////////39/f//////3tzb/zEkH/8vIx7/MCQf/DImIP4wJB/JAAAAAgAAAAEAAAAAAAAAAAAAAAAAAAAAAAAAAH8AAAIAAAAAMiMeMzElIP0wJB/+Mycj/yIWEP96cm////////39/P///////////////////////////////////////////////////////////////////////v7+//z8/P/////////////////6+vr/8fDw//Hw7//6+fn//////////////////Pz8//7+/v///////////////////////////////////////////////////////////////////////Pz8//////+HgH3/IhUQ/zMnIv8wJB/9MiUg/y8jH0AAAAAAVQAAAwAAAAAAAAAAAAAAAAAAAABVAAADAAAAADAkH5MzJyH/LyQf+zAkIP8uIhz/2tfX//7+/v/9/f3//////////////////////////////////////////////////////////////////v7+////////////6unp/6eioP9sZGD/TEE9/z80L/8+My//S0A8/2phXf+jnpv/5+Xl/////////////f39//////////////////////////////////////////////////////////////////39/f/+/v7/4+Lh/zMnIv8vIx7/MCQf+zMmIf8wIx+jAAAAAFUAAAMAAAAAAAAAAAAAAAAAAAABAAAAAC4uLgswIx/jMSUg/zImIf0lGBP/aWBd///////9/f3//////////////////////////////////////////////////////////////////f39///////6+vr/lY+M/zkuKf8iFQ//JBgS/yodGP8sIBv/LCAb/yoeGP8lGBP/IRUP/zYrJv+Nh4T/9vb2///////9/f3//////////////////////////////////////////////////////////////////f39//////91bWn/IxYR/zMnIv4xJR//MCQf7TUoGhMAAAAAAAAAAQAAAAAAAAAAVQAAAwAAAAAwJSFEMiYg/zAkH/0zJyL/IxYR/7Wxr//+/v7//Pz8/////////////////////////////////////////////////////////////f39///////m5eX/WE5K/x8TDf8uIh3/NCgj/zMnIv8xJiH/MSUg/zElIP8xJiH/Myci/zQoI/8uIh3/HxMN/1BGQv/h39////////39/f////////////////////////////////////////////////////////////z8/P/+/v7/wr68/yUZFP8yJiH/MCQf/DMmIf8xJB5TAAAAAFUAAAMAAAAAAAAAAD8/AAQAAAAAMCUfiTMnIf8wJSD7LSEc/zwxLP/u7e3///////7+/v///////////////////////////////////////////////////////v7+///////o5ub/ST46/yMWEf81KST/MSUg/zAkH/8wJB//MCQf/zAkH/8wJB//MCQf/zAkH/8wJB//MSUg/zUpJP8lGBL/QTYx/+Hf3v///////f39///////////////////////////////////////////////////////+/v7///////X09P9EOjX/Kx8a/zAlIPszJyH+MCQfmQAAAAA/PwAEAAAAAAAAAAAAAAABAAAAADEkH8MyJiH/MiYh/CUYE/9qYV7///////39/f///////////////////////////////////////////////////////v7+//39/f/6+fn/XFJO/yMWEf81KSX/MCQf/zAkHv8wJB//MiYh/zQoI/8zJyL/Myci/zQoI/8yJiH/MCQf/y8jHv8wJB//NCgk/yQYEv9RR0P/9fX0//39/f/+/v7///////////////////////////////////////////////////////39/P//////dm5q/yMWEf8zJyL9MiUg/zEkH9B/AAACAAAAAQAAAAAAAAABAAAAADwtHhEvIx/rMSUf/zMnI/4hFA//mpSS///////8+/v///////////////////////////////////////////////////////38/P//////nJeV/x8SDf81KST/MCQf/zAkH/8yJiH/NCgj/zAkH/8jFhH/IhUQ/yIVEP8jFhH/LyMe/zQoI/8yJiH/MCQf/zAkH/81KST/HxMN/5CJh////////Pz8///////////////////////////////////////////////////////8/Pv//////6eioP8iFRD/Myci/jAkH/8wJB/0LyUcGwAAAAAAAAACfwAAAgAAAAA0JB8xMSQf/TAkH/8yJiH/JhoU/8G+vP/9/Pz/+vr6//38/P/9/Pz//fz8//38/P/9/Pz//fz8//38/P/9/Pz//fz8//z7+//8/Pz/7+7u/z4zLv8tIBv/MSUg/zAkH/8yJiD/OS4p/ykdF/8xJSD/d29s/6iioP+ppKH/fHRx/zQoJP8oGxb/OS0p/zImIf8wJB//MSUg/y4iHf83Kyb/6Ofm//38/P/7+/v//fz8//38/P/9/Pz//fz8//38/P/9/Pz//fz8//38/P/9/Pz/+vr6//38/P/Mycj/KR0Y/zElIP8wJB/+MiYg/zElID4AAAAAVQAAAz8/AAQAAAAAMSQdTTMmIf8wJB/9LyMe/zImIf/o5+b//////////////////////////////////////////////////////////////////////7Svrf8iFRD/Mygj/zAkH/8wJB//NCgj/ykdGP9FOzb/09HQ///////////////////////a2Nf/TEI+/ygbFv80KCP/MCQf/zAkH/8zKCP/IRQP/6ahnv//////////////////////////////////////////////////////////////////////8vHx/zktKf8tIRz/MCQf/DMmIf8xJB5cAAAAAD8/AAQ/Pz8EAAAAADIjIWszJiH/MCQf+y4iHP85Lin/vLm3/8rHxf/IxcP/ycbE/8nGxP/JxsT/ycbE/8nGxP/JxsT/ycbE/8nGxP/JxsT/x8PC/8vJx/9nXlr/JhoU/zImIf8wJB//MSUh/zAlIP8uIh3/1dLS///////7+vr//Pz8//z8/P/7+vr//////9/d3P80KCP/LyMe/zImIf8wJB//MiYh/ycbFv9eVVD/y8jH/8fEwv/JxsT/ycbE/8nGxP/JxsT/ycbE/8nGxP/JxsT/ycbE/8nGxP/IxcP/ycbF/8K/vf8/NC//LCAb/zAkIPszJyH/MiUfegAAAAA/Pz8EPz8/BAAAAAAvIx+CNCch/y8jHvswJB//MCQf/ygcFv8nGxb/JxsW/ycbFv8nGxb/JxsW/ycbFv8nGxb/JxsW/ycbFv8nGxb/JxsW/ycbFv8oGxb/LCAb/zElIP8wJB//MCQf/zMoI/8kFxL/cWhl///////7+/v///////////////////////v6+v//////fnZz/yIWEP80KCP/MCQf/zAkH/8xJSD/LSEb/ycbFv8nGxb/JxsW/ycbFv8nGxb/JxsW/ycbFv8nGxb/JxsW/ycbFv8nGxb/JxsW/ycbFv8oGxb/LyMe/zAkH/8vIx/7Mych/zEkH5EAAAAAPz8/BD8/PwQAAAAALyMfgDQnIf8vIx77MCQf/zAkH/8yJiH/MiYh/zImIf8yJiH/MiYh/zImIf8yJiH/MiYh/zImIf8yJiH/MiYh/zImIf8yJiH/MiYh/zElIP8wJB//MCQf/zAkH/8zKCP/IRQP/5+Zl//+/v7//Pz7///////////////////////8/Pz//v7+/6qmo/8iFRD/Myci/zAkH/8wJB//MCQf/zElIP8yJiH/MiYh/zImIf8yJiH/MiYh/zImIf8yJiH/MiYh/zImIf8yJiH/MiYh/zImIf8yJiH/MiYh/zAkH/8wJB//LyMf+zMnIf8xJR+QAAAAAD8/PwQ/Pz8EAAAAAC8jH4A0JyH/LyMe+zAkH/8wJB//MCQg/zAkIP8wJCD/MCQg/zAkIP8wJCD/MCQg/zAkIP8wJCD/MCQg/zAk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"
ICON_PNG = "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAABZz0lEQVR4nO2deZwdVZX4v+feekvvnYWEQPY0WyAEDOBug4io467tzs9lRnBwXEYddwXcRh0d91Ecx2VcEKOOOyoiNooiGElCCAkJCQkh+9br26ru+f1RVa87ISHd773e6/v5PCWv36uqV3XPuWe750JCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQsIkQ8b6AhJGleE8bx2xq0gYNyQKYOIj4atDANrb9wpAJ0Bnpxv0OWV4Qm0G/rNDysftnBUdY+Xg4yXKYoKSKICJgwCG9nZpJxbElY5hCN/8ZcumSbdRVXfM5y5iVJubZPs9f+oGgmFcm6W9PTzmwHUxnGtLGBsSBTA+EcC0t7fLiQR9wfLlrV6v3+R72TYXBJ6IPFac8xRpQVhePqBqIyJtj3pWBURQdbsR2S2gIiLO6TYjPKgignOr8bwunNtNffOui06f1bNy5crjKIsO296+94S/IWHsSBTA+ECgw4TC0ukAd/QH5i970jRX6G2zTs5BWKBOl4nIPNA20Iwxtj6U38gjQI8QN0VR1RM+cAUEiY4z+Aqjf6sDBBf4AWK6Fd0jynYRc5cS7A/E/L1ezPr77198CB6hGAzt7YZEIYwbEgUwdgwWhiMEZc6cFfXZRs5xqk8QceeqyjmgbSIyTcSEwqhaFmpUCSVTUFUH0YOVwc9XwnMOjfig8b/K/xCJYw5iwn9EykJCpaNOUXVdAjsdbEDk7wT8xRULd+/Ysf7gse9BpxIqvUQhjDKJAhg9QsEJB3zAoME+Z86K+nS9Ww7ucow8HuUsEZknxkQTeSiPqqqoOgUNBfEIoR7tZzkoABheWah0xIAYkQHFoOpQ5w4ico/A3ThuLaa823duuOvAEUdsb/cS62B0SRTAyGPo6BCO8pPnt523VJDHKvJswV0gIvPF2EjQHRoSREIVBgAnzvOKMgSRYhAx0QvEgDqccweA1Qg3GeG2rfef9vcjLaEOG/5/ogxGkokyoCYaAh3myMHbYRedvvUxgfrtBnmBqj7WGGuBIwU+nNljgZ9MKKgLFQJGxBiR8CeGboy7T9FfqjG/rpO6Ozdu/HNP+ZsdHZaVK2M3IaGGJAqgppRnrfJMNr/tvKXGmA5UXwIsFTGh7+4cqAaRsz4ZBf5EKKhDUUSsiBExQujl6A6Um1T1m4vmttzZ2dnpR985hmJNqIZEAVSP0NFhWDkwKE9tWzY3JeaZYF6jqhcZa70oOKah0E84k340cKrqBtwFQxTPXI/ID5xzK7dvXr2+/OnEKqgJyQCsnHg2Ks/2i9rOu8yJuQLc84zY5iNn+ik5y1dKGAiJzAIxggsCH5FbBf2Op703bt68uRB+tMNGVYmJIqiARAEMHxOW3YaCv2jRObPVSz8X9DUgT4gG62DzPpnpq8OFBQxijQlvpTq3QYUbEfP9bfev2hB97hEKOeHEJANz6Bwh+Ke2LZvrqfknjPlnY8wsVUWdK89cJPe21sQxA8RYK0ZwzhUE/a6IfG7r/XevjT53xHNKeHSSQXpijhhQcxefe45nvbcp+iIjplnDlFYgiYk/mgxYBdbinAuA3xvV/9i6efXN0WcSRTAEEgVwfIT2dksUgV68+NxznPXepqqvNMaknYvN/GS2H0Nii8saY+PKyJuPVARJjODRSAbuI4mj+gHAwoXLziCVelci+OMajUqhxRhrYkWgwie233/3LUCcNUjSh0eRDOAj6LCxybh48bmzAmuvBn2rMV6LC/xE8CcEGpQVQbiC4Rt+4P/nji1r1wFRuXG5rmDKkwzkkEHm/orUgjZ3BfAhY+2pLvAJK/QmjuDLUf8/8P5QJ78jPzkxu35oAGKMteICVwT9pHXuC1u2rN1LuYlK4hZMiAE9ogyaEeaffv6l4viosfax6gKcc76IWMbhfZJBr1g0NRJcP3rX1/C/o8XBBENUARbFRN8xQFoUBVJodM7y2sBym6Hxqhwi5W2N9dDA36nIB7Ztvvvr4V/bPThyYdZUY9wN7FEkjti7efPOP8Vm9SNgXouABsG4MvUHhD0cpw4hAEoq+AhRwQEeikWZYQIccJLxmWV8fBU8gaU2jyfKo3UFMCj3+xm61JIWpVcN24MUFjikloKG53YIFsUDUhKe1x6liMaRVKmqBsYYT4xBnd4C/vse3LT2r+GfB1y/qca4GOCjT7sH4ay/oO381wn6YbHeKS7wXdQSY0zTeYMFXhF8QmEvRoKVRWkxjlnGZ44pcbotkBXlTFsgI46FtoSgNIqjURwOQdDyDH4iSgiOUEMWVDikFgtsD1LkMGz20/RgeTBI8XCQYqdL0a2GPjUoQgolLY7UoN8wThSCqmpgrec5F5SAT1hnP7Vly6quyBKcctbAVFMAZd9v0aJzT3ee/bwx9vJB5r43lhdmorFXQiiooRTNsq0m4GTjs8zmOcMrcJotMM+WaJWARnGEPoriR4JWDFfmE0SWQszQxP/ICIAQmv5K6AoYOOJ8eRUOq2W3S7EpSLPJz3CPn2W7S3HIWQoYPJSMxAooVAhj6nyHwVxrrUfggvvFBW9+8IG1v4n+ahleP8QJzRRSAANm3sLTzn+TwoeNmJYg8MfMz4+FXhEKkTABzDABi02Rc70856VynGkLnGR8msUhgE8o5LGAx4IdC+7xgoCVcnQQcECRKJYwZpASygLep4YD6rElSLPar2NNKcumIMMe51FEyOLIipZ/+1gpA1X1jbEeAurcF7I2976NGzf2TKVMwRRRAKHJP2/e+aeYjH7GWO8lYb2+CwiFf9QYLPRFhJwaDMo8W+KxXj8rUjku8HKcbErUR+Z7IfL1/UGCPhAAHHsGAoHhFZnI3UiL4qEUEfY7j7V+HX8r1fFXv55Nfpo8hswgZeCGkaeo4dU7AGNTRl3wdwiuDmMD1xi4bpx4LiPHeBlDI0U50LdwybmXI+YbYu0cF/g+jO6sHy1joYihXw0WZa4t8Tivn4vTvTzGy3OSKUFkCRQRXBS/HzfRyGEwWCnE8YdspBC61HKvn6Wz1MCfSg1s9tPkMNRFykAYfRtcVX1jrYeqr+r+bdvmNZ8N/zK5A4QTbVwNg4EHt2DJ8mvF2msIF+z4jJKvH8/2DqE/8unnmhJPSvdxcWpA6F1kCZQGzaCT7cEM1OKGcY06caRQugcpg9tKDWz0MyjQIA5v1K2CqJrQeuJc8INSX+7qnTs3HBgcNJ5sTLZxFhEK//z5Z86RTPYb1niXB4Efu5ojHuGPBb+E0KeGDMp5qTzPTndzSbqXU02J4Aihn5izfDWENbkDyiCNclAtd5Qa+FmhiTtKDRxSS504srjRjBWEmQIv5TkXbNLAvXb7ljW3R2Nq0pUST7YxV14TPn/x8icaa1aKmNDkH4VZPzbzCxhyKswwAU9L9/KCdBfnpvJkceTUUIjKbKaa0B+PWBl4KA3iUGBTkOGmYhM/yTfzkEuRQqmX0VME5QAh6gP/8uCmu69nElYQTqbxV17+ufC0868Cvgh40VLdEQ30xYLfHwn3qabES7KHeX6mm3mmhAP61OCQSWne15LY2a4TJYNywFluKTXy7fw01vsZDNAoofyNvBTGLoEVFwTXb9vc8i+RKzBpUoWTZSwaovGwoO28rxhrr3JBEG1uMXJFPUKYAutXQx7DMi/PyzKHuTjdy1xTok8NhagUN2kUMDxiqyCF0igBh9VyR6meH+Rb+WOpAQWaJBgNi0BBnbEp61xwe5ArPDfc4GRyBAcngQKI/f1l0yTj3WCMudwFQcAIN920UUS/Rw1n2QKvqzvIM9M9NEtAnxqKmGS2rwFh8HDAPfCBP5ca+HpuOreVGsjgyunSkXTOowpC61Q3Bb575Y6tq++aDPUCE3x8Dgr2pet+aq290PdLI1rRF9t+PWo5xZR4cbaLV2UPMUt8utQSJGb+iBFEKcUmcfgIPyk08+38NO71M5HL4MrrIkYEVd9Yz1N1h1zgnrN9y5rbJ7oSmMDjNEzNzF103oWeJz8VkTlR59gREf44+tOjhjpROjKHubLuIKeYEj1qKUazVMLIE5t3zeLoU2FloZWv5qaz23k0iRvwB0cC1UCMsYDvnLt6+wNr/ru9vd3rnKBKYIIqgCOE/zeITItW8I1IsM+i5DEUVbgk3ctb6/dzts2Ti3x/m8z4Y0IQpRGbxLHbeXw1N50bC62UVGiUYATdgnL3IQkC/8qJrAQm3riNTK6y8CPTVIMgquyrKfGa+C61zDUl3lG/j+dkuvGjwp7E1B8fBAhpHA3iWOXX87G+Wazy62iUgBQ6Um6BAs4Ya2MlsGLFitSqVatKI3GykWKCjd945l9+keeZX0fC70Yi0u9Fi1ocwiuzh3hD3QFmmYBuDU+VRPXHF3GwsFECipFb8Pn+GXSppXnkrIFHKIGJVjU4ccZxe3hj57ctf5Xn2d8BIyL8ccrugHossCW+2ryDaxv20CSOLrUYJtJNmzrEKdk+NQQIr80e5IaW7Twl1cch9XCEAdwROK1xLgis9b46v235p6HTb29vH7Nl5cNlglgAR/j8nUCdqqu58Nuoiq+owqvqunhz/X5ajaPLmbLgazyPaBLwG8/4CA0Szvs35Kfx2f6Z9KqhSYLyqsoaEloC1rNaKr3hwS1rrp8o7sAEUABHBfxg2kgIvyfQrR7Tjc8Hsjt5jneIbmcoOR2YOQQQQcQg1oKJLiFRBuOSOBMw3QSsLtXxvr6TWetnmS4BI1DUr0BgjPUmUmBwnCuAMM9/VMCvpsJvIqE+VIKL6OKjzXs5ozlNb+N0Utk60q3TooJCAecoHtqPKxQodR0iyOVAwKTS4SXppCkRn1T4CE0S0K+Gf++fxY35VhokIEXN63mPERMY3xWD41gBjLzwe0bI+Y5iscTrTnK877Q6muYtoDRzDulsXagdzKDTKeAcuICgr5f8np3kHnqQ/K4duEIek86EiiKxCMYdQVRW3CABNxZa+XjfLPrV0Fh7l+CRSmAcFwuNVwVgABdtzrFORE5SV9tUn2eEQ7kSs5uyvP+82bzi3DlQPy3ccs4vhYIO0ew/+JsSCrkx4HmgUDq4j5777qF/y/1oECDp9MD3E8YNcU+CGRJwl1/Pu3pPZkuQpkWCWqcKB5RAqXjZ9q33/G68ZgfGowIwAKeccua0VH3dTWLkwloW+Uj0P4dyJV6+dA7XtZ/GrJZ6gkKACXxEIgE/EYNnec8Dz6O4ZxeH/tJJYd8eTLYucQnGKT5CswQccJZ39c7htlIDLeJqHBdQF3aW55D47llbt665czy6A+NNAQi0W+j0F7Qtv9na1NMCv1Sz8t54IXeuFPCx9tP5pwvmQ6AEpQBrqrgVGi08zGTQUpFDf/0jvRvXY7LZxB0YpwRAOmpT9sG+k/nffCszJKhx+3J1Em5Rts8GwTnRrkQjWqk8XMaZAohy/UvO/Yr1Ulc5v3aNPKJYH73FgM897SxevmI+QV/YmkOGMuMPBdXINUhx6M+/p2fDvZhMNrEExinx3gd14vhWfjqf6DuJulqvJVANjLXWOb2r2Gcu3rVrVZ5xtJnSOKpp6bDQ6c9bvPwq66WvcqHZXzPhN0bYk/P5ePtpvHzFfEq9eaxI7YQfypkCSgWmPfGpNCw+DVfIj/U+IwnHIS717lPDG+r2c13jHvqiNm01e2Ii1gWBb6y9MN3g/xfgQit3fDBORmboGy1Ycs7jrTVfdoEfL/iqGgFUhO58kU8ta+F1Kxbi9xXwzAj9dJFwVJVKTHvcU0i1TkP90tDiCgmjTlz5uc95vCxzmP9p3kGDOPIqtascFPGcXyoZm3r1grblbw2DgeOjWnA8KAADK92iRefMxqR+Er1Xk7b38aaYfQF8ZGYv//yE01AHXi0O/qgnFnABpq6B1vMvSuIAEwALHFbLJalevtK0g0bjyNVaCQS+L8Z+Zt6i8y4LlUDHmFsC40ABdAigzrPfNmJmhVV+1V9XLPz9YrkuvZ2rzjkZ1zobKRVHZzYWA4U8dQvbyMyegxut8yZUjIeyXz3O93J8tfZKIGoWrWo8+faiRefMjroMj6kMjunJw0UTK4MFS5Zfa0zqsmBgw46qKM/8avhQ3S6uaM6Rm38Gxi9GpX+jRRgUbFh8Ojhl3MVcEx5BCuXQMZRAjQTFqDpnxMx2nv02oNEEOGaMoQLosJ2dnf68ReddJtZe4wI/qFUrLwFyavhw4x5emTpAd+MMsq2tEASMqhCKgSAgc9LJmHQ6yQZMELyjlECTcTUMDIoNAt83JnXZgiXLr4WVwViuHhwrBWBgpWtrO+8k48m3Ua3Z9OgB+53lXQ37+H91h9nnC9nWViSVGhtfPHDY+gZsQyPqxlUNSMKjECuBx3g5vtj0MIGGtQO1GKQSxgMCsfaa+YuXXRouGBqbeMCYKID29nYDaEn1v4yxs52rjd/voRxQy6vrDvPq7EEOOA9PHanW6VFN/xgoAHVIJoPX0Ey4lCFxAyYKHspB9bjI6+eaxr3komYwtXmCKigq1l4/d+7S6bByTHzEMVAAoek/f8nyNxov9WIXlPxabNwRCr/HSzJdfLhhd/lhAeMkCj8eriFhuHgoh9XyyswhrmnYQ7faGkmpGOcCZ4y3xGbTXwFce/vo1weMsgK4xsDKYF7b2UvEmH/XoDYLfCxhm+4LvBzvb9hDTsPNIsq72I/1wpy4VDhhQmKBA2p5VfYQr8oe4rDamnSAFhHrgpJvrO1YuGT5S8bCFRhlBbA+LMrDu96IadKw4LIqhWoJo/3zbZGvNO8gHW3KGf6wMApfOrh/9AOAMcbi8nlK3Ycxnk0UwQTFAN1qua5hD8/OdHNAvRq1gRejzjk15gsLFiw9OXIFRk0uR1EBhNV+Cxefd4WxqUtrkfIToIhQJ47/aNxFqwTkMQM/ShWxhlL3YbRYHP2SXFWwhqCvB5frP7K3QMKEIk4t51S4tmEP53p5utViq1cCxjnnjLGzSKU+Djg6Ri81OFoj0sBKXbBg6clYPq4ucCLVS6MABRXe17CXFV6OnmM8ELEefk83xf17IOWN8gwcWiC5h7fjSj7jou4qoWIMUMTQKgEfa9xFqwkoYqq2K8tZAWOvmL/ovKexcmUwWq7A6IzIUKM5UqmPi/FOds5VbeZ4wCG1vCZ7iJdnDj+KSSZoENC3ZdPod+sRgxaL9D+4GfFsUgcwCbAo3Wo51+a5pmEPeZWaZQUEDJYvLV26NA0rYRR81lFQAB2WlSuDRYuWPVmMvSIq+KlKu1mgWw2PS/Xztvp9HHo0U0wdJpOhb8v9FHY+BKO1PNc5yGbpvW8txYMHEC818udMGBXijNNz0928NnuIQ2qpvpJHTBAEvrXe6X2F9DuAADpGXD5H+gQCK3Xp0qVpZ+1nJeycWZVWi/3+aSbgow27scIREf/josrhv/0FLRXAjHAwTh2kM5T27qZ73d1REVIy+08mLEqXWt5Wv4/HpfrpVlP1mgERseoCh5F3zWtbsSRcK3DNiMroCCuADgO4vnzqFcZ6jwkCP6g2Ehf7/R9s2EObLdCn5sQ/QhVJpSns282hv/4RvNTIuQPqwEvhinkO3v57XLGIJMG/SUfcXcoKfKRhN9NNQJGq3QGJAoLNBv8aQKPM2YgxkgcXQOacvmJ6ygX3GJFZYcVv5UrHI8zHvjZ7iA817Gb/cE0vMbh8jqazljHtiZdAyQfn1y474MKZ3xXz7Lv5F2FvwHQmmf0nMT7CdPH5SbGFt/WcEjUYrZpAjAHnLn1w8+rbwol0ZHoJjuDU1G4Bl3HBG631Tq623NcAfSqcYQu8uX5/lIIZJuow2Sw9G9Zx4NZf4/xiFBOoslAnFvC6ekoH97Hv1z8NhT+TCP9kJ1wzYHluuovnZro5XJPUoCKIdXAtoFFAcEQYIQvgGgPX6dwl5y+xRv8mKk0a+v4Vn0+AfjV8tXkH7ak+uqrxucTgCjnS02bQesETyc5dEJ6gVIoE9gSdgQcrC2MglUJLJfo2rafr73cSlIrhZiGJ8E8JlHAZ8UG1vKxrAQfVkhrYRK7SowZiPCsueMnWzatXjlRH4RFSAFGLr7bl3zI29f8Cv1RV5N8Sp/wOcm3DnijqXyXGoKUSqJI9ZR5NZy8nO/sUiAU3CEJBP7qM2JhQOVgPBDSXo/+hrfSsX0vxwD5MKhV+Jqn4m1IECK3i89NiC2/vmUOzuCpdAXXGWONcsClF37LNmzeXGIFmoiOgAMLZf+HCZadryluDaooqWnwJUEKYLgE/bNlW3tyxJhcezfJhoE5Itc6gbu58snPmkmpuRbwUkskS3vMwaOgKObRUpHjwALmHt5PftQO/pwsxJkz1JYI/ZXFAkziu7JnLrcXGquMBqhpYz7NaCl7z4JbV3xoJK2AEFEBtZ38D9Kjh0027eG66iy71alF+eSSRIlC/FO7sYy0mU4dJp/GaWgaEWjUsK/ZLBPkcKIjnhRuFRn9PmLo4IIuyzaV4Zdd88hhsVa6AOjFWnHP3p+ldPhJWQI2DgOFqv4ULl52BmJe6wK+q5Ddc5We4JN3Lc9Ldtaq9fiRREFC8FCZTh3gptFTE7+0mt2MbuYe3R7P9QwS5ftT3MekMJpNB4pqCRPinPAbox3CWLfCaukP0qsFUNV7FqAuctfYM3zW+DHC1Lg6qsQIIc5bqmfcaYzNaZaefAKgT5a31+/FHQ75UQ/8/2g1YrIdJp8svSaXDnH5cQ6DjZn+HhHFC3D/g1dlDLLV5+tRWK2SiquoM75k793F1USPRmlnutVQAUm7vjXmRukCrn/0tHZnDnG3z9DOEgp9aEwv54FdCwgkIEBok4Mr6gzXYYShcLmytPcOm85cQNhKtmSjUUKY6DKBqvTcYaxqivH/Fgb8iwimmxJV1B8kNpdovIWGcEC8Yek66myel+iJXoBoUFMXw9vDfK8ddDEBgpZtz+oqZCm9S56qc/ZVuNbw428UppkShBksuExJGGwVeU3eoFr2DrHOBijFPXbBk+cWEsYCaLBeukQJot4BmAv8FxtoZ1c7+/RiW2gKvyh6iR22VgZSEhNHHAL1qeFKqj+dkeqoOYKuG240rXAnQ0VGb66zVxGoAN79t+Z3WeBc457tKu/3ERT+faNzFyzKHOTgSab8phJZfElczRP91vM/KEZ+pyR5tUxQH1Itjc5DhZV3zqz2cigiq2mcCv23r1nV7GGhUVDE1sAA6LOAWLFl+sTF2hXOBVir88ey/zOZ5ZrqHrpFK+01iHGEQKq4WyaA0iaNVAmaIT6sENIh7xKtelBZx5c80iaNOtLxVdkDYaDV5GkMnXL9iOcvmeVamJ+pYVTHhSkHrNar1rgrfqj4YWHUfg44OWLkSVLjSiDFOA79S/9+gFFR4Wd1hmiXgUDL7D4lQMAUPpUEcqei9XjVsc2n2OI+dzmOXS9GvwkY/e0SBihCuaptrS5xsSjTgWOIVmS4B82yJZgnwUAKEvBqK0cRjSKyDEyEoJRVekT3MLwrNVWUFRBCcQ5VXz537uP/YsWNlniqtgKrbmQG6aNE5s531NotIQ7Tkd9jHjUt+p0nAD1q20VrLkt9JiAIOwaLUiSMd5Z83BBnu8bOsKdWx1aXZFXh0qyUgnMUFxeORI0YI6y4cgkGxhObrbOOzwJY428tzns1xlldgtinhEHJqKEXHTLI0xyd2Ba7qnsttpQaaxFWjCJwYa9QP/mHbltW/qrY8uEoLoN1Cpx8Y+1xrbaMLG35UZOUYlH61XFV3kLmmlPj+xyE2w7Mo9RLQrZa7SvXcVmrgT6UGHgjS5c0sUyhpCa2C2K+P/fxjIdFf4niBA3a4FFuCNL8rNpJCOdWWeJzXz8XpXh7j5ZhtfPIYclGjp0QRHBsLvLruEH8uNVR1nLAmCONEXwn8KrbAK6XaCdYAzG877y/W2Iucq0wBhLOPkMXxo9ZtnCR+NLMkxMQzfr04UijbghQ3F5v4VbGJ+/wMBQwZHFnRctYkFuSqilFhkPIQitHMb1Dm2xKXpXt4VrqHpV6+XLoNiSI4GgfUieP/dc1nlV9HY+VWgIqIqGqvFvOnb9++YRdVuAFVPKdrDODmLjl/sSDnVRP8C4MlhqdleplnShQS4T+CACGF0io+m/w07+k7mY7uBXysfxb3+RmyokwTnzoJZ/gwCFiboF1sCcTHi6+jSRy7ncdXczN4Vfd8ruqeyx9LDVFA0REcN9cwNVEgDbwg2zW0HpbHR5xzgbG20aSylwFUs6VYFQrgDwbA4l5lrE2rasV+iAMyOF6QqfrmTCriGWKa+OxXj/f0zuEV3fP5Qb6FvMojhH402o8MPleaUPEYlNtKDby+ey7/1D2XNX4d08UvBw4TBjpaPS3dy4IqJzmJ5nsVXg1IZ2dnxY++mqcjbW1t6RIN64zYNhdufTtshRLP/iu8HN9oeYhizfqsT2wChEYJKKlwY6GV63PT2e1SNEuARXHjbIa1hMqhRw1ZUV6SOcxVdQeZZXy61ST1BITPdJr4fKx/NtfnpjNd/GoUpCIEFP1l27at2wDljO2wqNAC6LCAFrXuHMQsduq00s6aEu3l9+xsN3VUFR2dFLjoNU181vp1XNE9n+v6ZtOjluniA4xL8zrMIFBWUN/IT+fFXQv4WaGZZnHY6DNTGUEpqvCsdDdNkZtUKaoaGON5pOwzANrb2ytMvVdAe/ve6MrtJcZYU6n5Hy76Mcw1JS5J9Q6txfckJvb1m8Txtfx0ruiex1o/y7TInPYnwBwaD+pp4nNQLW/tPYX39p1MADSKmxC/YaSI+wUs9fJc6PXTX8V4F0HCFapyKUClbkBF549OZoAXoxpeTEUnV/rU8KR0H6eaUk32WZuo+AhNEpDD8NbeU/hw32w8lMYJGlCLldk08bkh38qruuezwc8wQ/wprQQUIY3yzExPVOdS6ZMVo+pAaJ8//8w5DHF/nKOpRAEYwC1adG6biJyvWnn0P65euzjVh6vqZkxsfIQWCdjgZ3hN9zx+Vmhmhvjl4pyJShwwnCE+9/kZXtszj58Xm5lWne87oQnrXQwXpvqZLT6lyie9OBvQZLzs06GybMCwFUDsazjLk4w1aecq630dr/mfa0qc7/XTP0WDfz5hN9k1fpZXd887YpacLOqwbN2o4U09p3JDYRozpqgSiMf9PFPi/FSu2nGvIKjRpwLMmtU57CEzbAXQ2RmeRJHnoo/ePv/RTxxqwsem+pllqtKEExY/igqv9uu4smcufWpojkqgJxuxS9AsAR/onc13prASiC3fS9K90erLylR9tJcgIJfOnn1uw8qVBAzTDRiuAhAgmDNnRb2orNBwE42K4ggDN6GvqpswUYln/rsj4e91hjqZGIG+SolNxQZxRymBqcURk1+VboCqKiInZxr1jPCt4a0QHKbwhgdP1xeWi5E5qlpR4OEIM2gKmv+xz7/6KOGfCoIQ9yQYrASmT1Kr53gc4f5W6QaE6UBrjTGXwuAM3dAYlgIYOLj3LDHWRgpg2MQa8KIpaP4HCM0ScF+Q4fXdU0v4YwYrgff3zuYHhdYplx0oB8DT1QXA43Sgc/wDYIabDhyWAogPrsKF1aT/IBwAK1K5Sr8+IQnrwR2H1fLu3jl0qY3q5qceSjj46kT5SN8sVvl1NNVmZ90JQdj7wrDMy0U7CFVcEWBUHQJL29ouamSY6cDhnFUAN3v2uQ3A0qjlf0Xmv49hpvis8PrJV715wsRBgawo1/XN5h4/O2oBP62gnbmqjngX9Hg9QU4N7+ydw2G1pKl2U82JgQB5hMW2yBm2UF7CXcmhVFUxZlpRc6eFb10zEgogPGi6wZ4lIqequliJDwsB8iosskXmWJ/iFFn5FwCtEvCN/LRynn8khT8WemOE5uamYSkB5xwNDQ1kMulIEWhFSmQohBWCAZuDDB/qm01GpoYCgHB5dx2Oc1P5cmOVSojiAJ6IeTJAe/sfhiyXQ/5gfFCLPqG68t+w9v/cVJ56HG4KiL8jLINd5dfzn/0nRSZf7X93LKjGmLLQO6f09fUjwzDWjDHkcjlKpRKqGimDDM65EVEEPuHmrz8tNPOd/DSmSYBf87OMPyRa1HWel4tatFU2JuI4gCJPgYFU/VAYsgIoFxkYzh/2FQ5CCdtYne/lpkz1nwFKKnysbxalyNSr9a8OAkcmk6GhoQHf948Qenf0FudDYLAyyedzFAoFstkMjQ0NBEHtPfWAcCHR5/tnsDHIUC866ReGCVBQ4SxbYHo0KVSsAkLFvHTp0qVphrEqcMgKYOVK3IoVK1JOWY46pAKXJe78M00CzrAFClMg/RcP7BsLrdV2gjkmzjlEhNbWZoqFIvl8DmNMRUJ//HMoIkKp5NPb10dTUxPpdJogqN05lLDZyCH1+FJuJqkpMDHE6cA5tsRCWyRfuTyIoiowr78/M4eBGOsJGaoQC6D79hUbRVhYaQAQoAicbHxOMj4lJvcacSVsy73dpbk+N52GGgm/CEQ94mlqaiSVStHT0wsSCutIEZv/uVwO3/dpbW0mfoLDcTGORxDVR/yi0MStpcZqm2dOCOI4wGJbrCYOIKqqYky9Wrc4fKtjSA9kiAogDABKxixAaKx019849XGOl6e5qtTHxCDuBvtf/TPY7VKkcVXPayJCECilUonGxgZ8P6BQKAzj++ExrDFYO/ASkSEJcax4nHP09+dobmrAOcX3/ZooAQBP4LN9M6fM8nABHpPKVTUZDto5aCkMvSBoiPc3DACqkwuMsalKC4BizvAKk3rmh0j4cawLsvyq2BQpvOp+tYhQLJaor6/j7LPOoLu7h3w+f0LBExGstVhrcS5UHt09PXR1DbwKhSJBEGCMwVqLMSceGkEQsP/AIRYumMuck2eTG8K1nIjwvgU1vW/jmTgovsQWaxIUF+RxMPSFQUNqC97eDp2dIOj8aOKvaCJzCBmU02yhyrXQ4x8FUqJ8OzeNbrVVL4ENZ35HU1MjZ515Gvdt2ISIYIw5bmTeGIMRIV8o0N+fQ0RoaWli+vRpnNa2GGvjRl7Cg9se4sCBgxw6dBjf98lmM9TX1wP6qL5+Op1i+0MPs+ycpagqu3bvJZXyqsoWKEJGlO/kpvGMdA/eJK4NiAOBp5oSM43PPvVIVfB7BzIBOg9g5cqhHWJICqCcVhA5s9IKwDgA2GrC3WYmc++/2Pff5tLcUmyMAn/V/drQ7A5YMO9U7tuwiZ6eXtLp1DEFLTbxe/v7yecLLFwwj0sveQpPveRJnH7aEmbPnk1zU+MR38nn8xw4cIhND2zhz3+5k9/89lbWrb8PI4am6LPHCyyqKmvWrmPpWWdw6HAXxWIRa03FhUSx9bQ+yPKXUgOXp3vonqTuQLwr03Tjc6op8bCfIl1RLYSIqoKwcM6cFfW7dq3KMYR24UMdlbJixQpv3+Hgr9aa850bfgNQA+QQTjdFvtOynYGtKicfAcJ08bk+P4OP9c2qSQMMVaWxsYHu7l5EwFp7TOG31pZN/BXnL+d1r3klT7/sEk6aOeOIz4XBwoHvH23yF4tFbu38E9/69o3c/Ls/4Hm2nGI8HqVSiebmZoqFAn4QVOUOGKBbDZene/li08N0q6lmX71xTRj89Hlv7xxuLLTSWtl4iTcPzYkvSx988O5tDKFR6FCEWAA9dIh6hEXVZABKGqY8ajEjjmcsSpdaflVoiirbqvSLnZYDfsbIcYU/lfLo7ukhm81w3Qfexa9/8QNe+fIXc9LMGQRBQBAE5WIeY0L3IX7Fef8gcARBQDqd5vLLnsr3/vd6vnb951i8aCEHDhzE845vNKZSKUrFIvUN9TWJBTSIckepno1BhrpJ7AZA2FV5gVeqJusxOBOwKHzrxJmAoSoARPLNMtD9efhXF/WIP80rVlX1NN6JI//3Blnu87M16XRsraFU8ssBv2MJv+dZ9u7dz/Jl5/B/K/+Xt7zpKlJeiiAIUNVyENAYc0zhjLMAYVbARsogVBjPe84z+OXPvs9LO57P3n37HjVjUCz55PMFrK3eYPdwHFTLbaUG6ibxpCFRw9c2W4j8/yp/pzJtqB8dwlMKtUhJ7WliTFOlKcCYukn7GEM06nzTWWyINn+obt4KAkdjYwPFYvG4Qud5lq6ubl720hfy45Xf4uylZ4ameuQqVDIbx5kDYwxBENDa0sxXvvRprv3Au8ppx2Md1lpDPl+IAoiVLUSKiRtodhYbyCGTetFYuN+jq8rNiVOBSFitO5RU4JDVtBpTlQsWC8aZ3uTOAFjCXXr/VGwgU+WspQp1ddmwyOc4pFIp9u07wIte8Byu/9KnaW5qJHDuUU314RJbBL4f8La3/DMfvu697D9wEGsfeY7Q2jB0dfWQTqeGlE48HvF+evf6WTYFGbI1qKMYjwhQVGGBLTHd1GJfzKFr/BM+nViLWNzjRAzV1ABYwi3AJuNDhIEBuzHI8ECQJlu136p4nocxx36e1loOd3Vx4QXn84l/v7ZsstsqhO54xO5BqVTiH1/zSq78x//Hvv0HjqtoRCDlpao+bxxP+WupgazopLUf430XK0kBxpT3CkAfB0PbK2AY08RxRuFQLgwoRamO+bZEXge2n55MBAgesNavI4chS3XRf2stvb29x5xFw9r8Ei3NzXzp85+kpbmJIHBVzbgnQkTwPA/nHB+57r3cs249a9beS0NjPe6oWgERoae3N6o1qJx48djqUpZSdnKOGwjlo9UELLAldpYqTQVGyNAzdENWAA5aqk3DWKBJAuqjHWImmy4PEDLiWF3KIlUGc8JluPX09fUfM/9ureHQocN87CPv54zT2/B9v6Zm//EQEZxz1NVl+diH38+zn/9y9DjrD0SExsYG+vr6Kl6joEBGlPuCDDk10VLqyZdAjpeMp2sQNFZohKEtOj3RfRRAZ8w4o6lxWt19YSOQyoKASqhtzvHyk7qyywjc52dqkrcOG74+8lYbY+jvz3H20jO46Rc/wEapvFrV4g+FWOG8413X8D/f/A4zpk/D9x+5TDgOAlZ7bYZw7FRjIo93jMBGP8NhtdXIiIqIiq+P27p19V3hPp4rj7t+e0hTRl2dTSnaWM2cHVY8wV9K9ZP2AcZlV3Xi8Khuzb8xwvFW9IZr9PNc+U+vJp1K4fvVFd1Udn1h7cAbrnwNP1j5f8cUfqBcrlzt8mQH3DEFxk5WXLUTpCJiAvGbh/LhISkAY6wKUnUXCCE0cyY7R9bYVfB9VRoaGo9pOosI+XyehQvnc9nTLi5H3UebWKiXLF7Ik5/0eH5z8620tDQ9Yt3AgCtTuRsQk4ydoSNihiSvw20KWjVuCrxqseS3u7vnmAJjraGvr5+nP+0Spk9rLTcEGQviRiEveuFzohn+2AVGx/stwz7fFHjV0MKp5XLghNHmeEKtCmKES5/65FHp3PtoxJbHEx7/WGbOnE6pVDpulWHC+CRRABMM3/dpbWnhtLYlZf96rIjLkqdPa2X+vLmPWq2YMD5JFMAEQkTwfZ/prS3MmnVS9N7YXpOqkk6nOPXUUyiV/DG/noThkSiACYQxYUegxUsWUV+XHVP/PyaO7i875yz8wB9ODUrCOCB5WhMM1bg8eHw9ulSq+rLfhNFnfI2ihCFRy5bftWI8XlPCiUkUwASk2vr6kWA8XlPCiUkUwAQiDrg9+OC2cgfekdqzb6jEMYj7Ntx/3E5FCeOXRAFMIFTB8zz27z/AoUOHIwUwttdkjMH3Ax56aAeera4bcMLokyiACUQcADx4qIstWx4svzeW1xMv+9227SEymWN3KU4YvyQKYJxyvKCaMULJL3H7X+4CxlYBxNe4Zu069uzdTyqVPub1JAHC8cuoK4C4oeRkflWLqtLU2HjMYznnyGay3PTrm8vNN8d60v3JT39FyS8ds3PRo/2W4TLWz3UijJ3hMvIdJI6i5PuM+YgdMcJFnZU24hx8nJJfOuZfnAtX192z7j7+csddXNz+RJwLRj0KH28dvv/AQX79m1tobGg85g5CIhI+8xrg+z4D7Sgm2xiq1dgBQFV1SAcZkgIQMaqoqb5VoTC9tRWReEOqyUX8m3r7+qvaLFMECoViWciOdSYxwte+8R0uufhJ1VxyxQSBw/Ms3/v+D9m9dy8zZ0w/Zk8A5xz5fL4mhUutrS0YmZxbysTqrL+/PyqpruoXijFDWw48hLN0WFjpFrSd9y1j7BXO+QHIsKYbkbB/3fRprfzyZzfS3NwULWubXI/RubAn31VXv43f/b6z3KevElSVxoYGcvncMZfSGmPo7u7h29/8Ms+8/FKCYPSsgLgEecfDO3naM15ILpc/ZgrwRL9hKMRjZ+aM6fziZ9+nqbFxUo4ddQ4xwj9d9Vb+0Hk7zc3HtqhOgBMxxqnbkOsqXrhv3/q++PDH+8IJLYD29r3S2YmibEDC/QcrvffGGGbMmE59XbayA0wQHvfYC/j1b28hrIuvNAAWms5BcPx6/1TK48Mf/RRPePyFNDc1HbeFWK1xTvE8w0f//TPs3bf/UduBlfxSVR6fMUI+X2Dp0jOZe8qcKq56YpDJZKronaAqIuD0oX371vdSo63BABChvsKrKqev9h84xP33by7vOhNvRzVZXr4f/qaLLjifdCpdVfRbJNywM5NJHzcY2NDQwH0b7ufd7/0QIjLIRx45SqUSnmf5+re+xw0/+DEzph/b9AfIZrNlV6ZSRAwlv8SFF5wfKpRSacyfc61f8XZtPb19PPDAVjKZVHUNVESy1KohSGfnLAVQ1b+pOqTC5V7GGAqFArlcLhrQYx9xrfXL2rAx57JlS1kwfy6FQqGqGVlESHmp8gA5Gt/3mTljOt+94Yd89gvXk0oNbAU2EpRKPqlUitv//Ffe/d7rmD6t9bibhQZBgOfZqtuVBUFAQ1097U9+AiKCMXbMn/NIvVSVvr6+iuMlqigiGGUVoB0dtdkbMKaroquKEBH8wOe+jZuAsc1fjxQiQhAENDU20v6UJ9Lfn6tKAESE7p4eGhrqjzsoSr7PjBnT+cSnPs/Xvv5tPM8rX0etcM7hnCOV8rjtj3/hqqvfTjp9bMsEwmfb3NREX19/xTEQCM3/XC7PmWeexrJlS1Edm/6HI00sC1u3buPQ4S48r7qKSkW7AfburcnWYEvDKzFmt6rLSfjUh311IkLgArq6usuXOZl51jOfFgXGqjuOtXZIGYVsJsPb/u0DvO3fPkBff3/0vaAqNyR2a+IdhL/29e/Q8fLXcriri3T6+C6OMYaS71fdqtwYSy6f52mXXkzK82qq1MYT8Rjp7+sjny9UbAGIiKgqKFthwHp/NIZwpusUwAZmp6oWqTADo6p41mPT5i3xxVZymHFP/PAuunAFixctKO/oWw25XIGGhvrjRvnDh67MmnUSX//md3lhx6u5/c9/xfNsuX334JjLoxF/Ng4+ep5ly4PbuOqNb+cd7/og9fX1xxX++Hc2NTVSLBarrgAMgoCG+jqe9YxLo+NPvtkfIN5tb9MDW6ttqhIm2IUHh/qFoZ5JisVUEWRXJP/DntdiBbBt20P40ewwGZEoGNfYUM/znvtMevv6q07PWWvo7e2lob6OYvHYBUJKFBOYOYPVa9bx4pe9lre/84Pct+H+KD4x4Ds75/D9AN/3o1dAEAlr/FlrDbt27eY/P/tlnvWcl7Lyhz9h5szp5aDVsX53vlCgvr6OXC6PanUZibD7cR8XXfgYzj33nHDPw0lo/g/mgS0PRvet4kMIqnkV2Rv+c2ktLICw7mLHjjtyoFsjD6AiBZBOp9ix42H6+nPloMdkJFZuHS96Hi3NTccNlA0HVTjc3UPbkoXRv49973zfp6Ghnmw2yze+9T0u/4cOXn7F67lx5U/YsWMnQRCa9J5n8TwvetnyhqL7Dxzk5ls6ecvb3sslT38+H/7Yp+jryzH9OKk+CIW/UCiwZNFCfN+vOvgZHtNQLJV4accLMCI1aSs+XonHy/2bHohWVFZkOamIiFPtznUVt4dvXXfCmzakSsD29nbT2dnpRGUtIs/UCmoBVAdWsu3YsZOWpWdUPUuMV+JNM04/bQlPeuJj+e3Nf6ClpbkqH1ZE0CAgny+w7JylrFm77rj3Lp6hp01rJQgCbr6lk9/cfCszpk9n/rxTOWXOySw/9xy81ECwacPGTezYsZNt2x9i7979lPwSTY2NTJ8+rWwxHO+6CoUCZ55xGiJh0K7aIJZIuPnJgnnzeMbTnzppg38wsKIyly/w0EM7SKUqXVGpTsRa0WDTvn3r+xlCDQAMdy2A6O4KrqyMtZau7m7u27CRs5eegXPKJPUEyjbSm954Jbf8/raqrZ1YgW7f8TCqytlnncHadesftRdfrHBampuAUFDvXb+RNWvv5ee//M2gDagEz1qsZ8mk0zQ2NpRdhUdTWqGgFliyeCEiwr3rN1JXl636t1prOXToMO9427+Uldhk7TikGmY7du7cxcMP7yKdrq4GQGEvoeAP6YYNSfzKtQCOu1QDJxVGKUQEdcq69RsHLneSYm1oBTz+sRdwycVPpquru/qtslWpy2bZtWcvmx7YSnNzM5615R16jkcQuLIQ1dfX0dLSzMyZ0zlp5szoNYPW1hYaGxrK238PpZ5AVZk2rYW9e/dx/6YHyGYzVQt/PPvPnXsKr37VS1E93nqIyUFs7m/evIXunt6Kd3iOawBEuQugvb29ljsDrXQAHrpJnfZFCmDYT9o5RzqdZtWq1ZNaqx/N+97zNurqsjVJY6kqKc+jWCxSLBSoq68jk0kf10Q/+ruxcB8ZBPQJguC4BUfHOo6I0NzcRKnkky8UarY1eRjw7OOdb38z08Z467PRIL7fd9y5isAFFQcARcSoOlBWw9BSgDD0LIACEgRd3Qq7pIpMQCaTZuvWB+nq7pnUgUAIYwFBELDs7LP4p9e+isNdXTURlNgn9oOAnp5enAtobW3GuROn+aolCAIaGxpIpVJ0d/dQLBbLqcZqsdbQ3dPLk574WF7x8heVF1dNZuLft+7e+0h5VXVUEnVaJCg9GP5zZU0VAIDZtm1bXlTXUkUmIJVKsf/AQTZGFYGTOboLAwHBf33LP7NowXxyudosjVUdyLsHgaOnp5dsNk1jQ8OQZ/Khn0vL1ltTUyO9fX3lmvxazs4abY17zfvfiRcVUU322d8Yw+GubjZv3kImk65UHpyIEcXtDoKmB+PDD+WLQx6Jg3yK1Ui4KnCYFxme0Bhy+Tx/vevvwIAPNFmJrZyWlmY+8qH30dffhxmBQR0ulPHpz+Ww1tLc3FRWApUog/g78aKjbDZDoVAgny+U/15L4Uylwman/3zVa7jwgvMjF3Fyz/6xsN9330Ye3rmbdPrYLdVOTLQKUGVDmK5nyC76kO/wwKIgd0c1i4JUHSkvxV/vXDXpAzwx1lqCIOAfnnkZV/7jq9m3/wCpVG2bMcWKJn719YVLwY2RI5TBUIiFPp1OA0I+nys3qRgJn9zzLF1dPTz2ohW88+1vLtcqTHbiye+vd/2dQuRKVXacKACI3gFh2n6o3x3GGcNAoCsGd6tz+ysPBCrZbIb77ttIT09vzfzH8U4cD7j2g+/kogsfEy36GLkgaJwZcE7p6+sfltAaY8jlcpRKYZ+/kYwtGCMUCkUaGur54uc+QUNDfblicbITC/ydd/2dlFdxAVAcAHTAH2DoAUAYXgxAAbNjx/pDwIZI/od9xWFFYJqHd+7mb6tWA1Oja2w8qOvr6vji5z7BjOnTKRQq1/rDoZL7O5R1A9UiQrl46NOf/BBnnN42hWb/0Prds3cfa9aso64uW6n/ryJinHM9xX7vnvCtlUN+4MO605FpodQgDlAsFfnTn/8KTM6lwcci3kTjjNPb+Nx/foy+vv5oIEz+2e5YeJ7H7j37eMubruKFz382vu9PmdTwQEv1e9m1Z08N/H+27NrVeJhhdkwdlgIYKAjSX6s6rTQO4FxAXbaO2277M6XS1HnoEPq7vh/wjKc/lf/6wn9EabyppwQ8z2PPnn286erX84H3vj0S/lFvUj3m3Py7P1S1AEgVhxgEfgedfnt7+7CEaZgCHJoWEnC7OnewmjhAXV2We+/byLp774saWEx+NyAmVgIve8kL+OLnPkFvb9+UUgKe57F37z6ufsPr+PhHPxCt9LPVrIKbUIR1HJbevn7+0Pkn6uvqKh7/kf+vIvwShuf/w/A3BlHAbNu2pktV11UaB4AwMp7L5bjpN7eEB57k6cCjCZWAfwwlMHn9XxFIHSH8Hyz3HZgKQb+Y2Py/865VbH1wO9lsxesnYv+/q9ifXxe+NXT/HyrYGSiOAxjDL6uJAzgXkM1m+d0tnVPODYjxPO8IJdDT20upVJqU98IYQcSwa/eeI4Q/fH/qCP9gfnXT7wiCyst/wxWABlH+tHPnhoMMI/8fM2wFEJsYzrlb1AVOZHh7BMTEbsB9G+6fkm5AzGAl8JUvfopUKkVvb1/N6wTGEmstpZJPT08v73zHm/j4Rz8YlflOPeEfMP/76LztdurrKzf/4/w/orcAOpz8f0wF9ubKAJC05O51qpuNGKnGDejP5fj1b38PTD03ICZWAh0veh4/+eH/smTxQvbvP1hu8DmRSaU8enp6SaVSfOnzn+SD7/u3KWn2x8Tm/11/u7ta8x8jYl0QFCkFvwbo7OwctgBV5HC2t7fbzZs3F0T5CcaEkcgKcC6gvi7Lb357S7TRZfVNNCcqoRIIOHfZ2dz08xt5acfz2bd/f9Ree+JZA9aacp773HPP5uf/911e8uLnRdH+6pqFTgZ++vObqlr9BxqIsaK4Vdu2rdvIEBuAHE1FCmAg0qg3VVMW7JxSXx9udHn7X/4aVa5Nzs6vQ8HzLM45Wlqa+cqXPs1nP/VRstkMBw8eKgvUeCduJNrb20dfXz9vfuOV/PRH3+bspWdOWGVWK2Lzf+++/Y+6oerQjlVe//9bKjT/oeLtwcNIo1XvbufcnkrTgYP53vd/BEzu1V9DIS6Nds7x2le/gl//YiUv7Xg+3d299Pfnyp1+xxuh4HuUSiX2HzjIBSvO58c/+CYfue69NNTXl1N9U5m4H8RPf34Tu3fvJZOptPhnYP2/Ir+F4af/YiodSQoddsuWVV2C/lyMBbSiqdu5gMbGBv7QeTvbH9oRLZ+don5AhIiU1w4sXrSAL3/xU9z4va+x9KzTOXDwULThiK3VVtJVETcYjQV/Wmsr//nJD/OzH3+HJz7hseXOQuNRaY028aKwH/7op9EegJXGvNQZY4w6d29jpvg3QKLY3LCp+qmYgP9WFziodHUgpFIpDhw4yI/+7xfRe1MzGHg0Nmr35ZzjqRc/md/88od8+QufYulZp3P4cBddXV045/A8b1QFLBZ6EaG3t48DBw4xY/p0PvCet3Hr737K617zyuja3bhQUuOB0NQX7rhzFavXrKOhob5iBRBX/6nyzfXr1xeHW/03mGqfjCxdujTVW0zda41tcxUqAhGhWCwy5+TZ3HbrL6nLZsrvJ4QM7o5TKvn8/tbbuHHlT+j845/Zf+AAmXSG+vo6PC8MpNayKUhokYR5/CAIyOXz5PN56uvqufCC8+h40fN5xtOfysyZ0wGmVLu3oRLfk9dd+WZ+8tNflZudVogiBFIKznnwwXs2wjUGrqtIm1QpYe0edPoLliy/1nipawK/5ItIRVEeay2HD3fx1S9/hhe94NnJIDoGCrij7ssDD2zlN7+7ld/efCur16zj8OEurLVkshnSqVR5Btao3U64idCxFUOYmoN449Y4FlEqlcgXCpRKPvX1dZx5+mk89ZIn88zLL+WCFeeVvx+v5EsU95HEynvL1m087RkvjIp/Kr1HGhjjGeeCW7dtXn1ZfIpKr63KJxVqnrlLzm+zRu9DsZUe0xhDX38/Z591Br/62Y1kMmEzimQsPZJYMONYQcz9mx7gD7fdzl133c3adfeyd+8+urt78YMAawzGGoyYYwafRIRSyS9vMe77PsZaGurrOGnmDM4683QuuOB8nvKkx3P+eeeWu/XE15II/vGJJ7O3v+uD/M83vsPMGcffUv1EqGpgvZRV33/1gw+s/t/29navs7Oz4p1navHEDMD8tvN+Z429xDk/gMqqA+N+8D+68ZtccvGTEitgCMSm/tECmMvl2fHwTu7ftJmN9z/Arl17eHDbdorFElu2PIixZqCtY7Sd2SlzTmbatFamT2ulrW0x8+aewplnnM6ihfNpbm464rzxLJYE9x6dWNEeOHiIJ7Y/k1wuH9W7VFz7j6oeSMHSzZtX74/fr/T6qk7KRrsG+eL4GpZLwkaOlR4t7Hb7tW98h0suflIyowyBwQIYbuMdriqsq8tyWttiTmtbzD8888jvHO7qxogM2hYk/G5zc9NxBXrwsUVMopiHSBwI/e4NP2Tv3v3MmHH8LdZOhIbmv6dB6SebN6/ZBx220uh/TC0kTAAWLFiQwZu2ToxZolp5VsCYcCPMn/3f93jcRSsIgsm/KeRIMLg/YNzAc/DreMSR6djFGMp3Eo5NPMt3dXXzlEufw8GDh6rY+is8JEKgyvLtm1ffB9dIpcG/mFpIlkK73bZtWx70O1JFaTCE1oNT5TOf+3I0GKd2TUClxOa5teEmoNbasptwtHIYeIUKOEzzHfmdhOETK9H/+cZ32b59R1V1/2Hwz6LKH0Php2rhh9ooAODisGGo+N92LiiYqDKokiMFgaO1pYXf/Pb3/ORnvyoXTyTUjqNn9oHXWF/Z5GFw5P8LX/pqtDls5btEqxLGxB1fo4rS36OpkQK4zkGHfWjzvQ+g7vtijWiFKwQhvHnZbJYv/tfX8P1g0u8glDD5iN2u/7r+6xzu7iGV8qpY6KbOWGuCINhAcOjHgHR2dtZkVqyhc700/Hkl/xPOOV8qjAFA3Je+ntVr1vG9G39U3l0nIWEiEM/+99x7HytX/oTWluaKA38QLvwRMYLy6dDVbq/Ywj6aWht9BtD5befdUm1KMMxLl2htbeH2P/yKpqbGJBiVMCGI09cve9Xrufl3f6C1taWqqr/IAj5YNPbMXfevOhC/X4trrXF4vUMAFdUPh53CqkgIariByMM7d/OZz385sQISJgSx8N/0m1u45fed1Qo/qurEWEH1i7vuX7UfOqpeeTuYkZhODeDmt513qzX24uqsgDD44fs+v/nlDzl76RlTYsfYhIlJnE3J5fI8/Vkv5oGtD1JfV1fNxFWe/Ute/oydGzYcjN+v0SXX2gKAyApAVK+LrICKj6QaVgcWi0Xe+Z5r8f1gVHasSUiohHhy+uSnv8C69RvKOzVXimrY9QfVL+7csOFArWd/GBkLAGpoBUDYLmv//gN84bMf54pXviQpEU4Yd8TCf+/6jVz+Dy+uReejePY/VPJSp+/ccFfNZ38YEQsAYivAwLWKBtXqmSAIaG5u4kMf/RTbtu9I4gEJ44rYKi35Pu98zzUUi8WqJ6hBvv9/7txw14jM/jBiCmBlAB32wc2rO9UF3zXWs6qVdQyCeEPRFAcPHuK97/9wedfbhITxQGyR/tdXvs6fbv8rzc3NVRavqTPGmiDwNzZkSv8BmOFu+DFURjCatjRMA/juYy4IihLm7yqWWt8PmDatlV/edDPf+d7K8vZaCQljSRCEHZnW33c///HpL1Tb6CNEUTFGjPKx9evXF+PsWk0u+ChGOKkerlaa37b8o9am3hv4paDSjUSAaPOQgFQqxa9+9n3OOL0tyQokjBlxL4RCscjzXnQFa9euo7GxsdrZPzDGsy7wb9v2wJqnRm+O2Ew3wpKz0gHG5UufDgJ/twkltfKciCqpVIqenh7+5S3voj+XS7ICCWNGbPpf+6FPcuedq2hqaqrBuhVBUSfGfQAIoKMWl3pcRnrqVOiQHTvWHzSOd4uxolVKaxAEtLQ0c+ddf+faD30yWSyUMCb4frjHwQ9//HP++3/+l5kzZ+D7lS/2gTDtZ6xn1QXffnDTPbfVYr3/iRituloL6IK28/5gjH1ytWlBCOsDDh48xH9/5TO8+IXPjR5IkhpMGHniHhUb79/MM5/9krDlWuVdfmJURFShi2Jh6bZt6/cQ9WqpzVUfm1Fynq9RwKkGb3WqxUjvVHW3nHM0NTXyzvdcxz3r7ivvqpOQMJKEq/ygq7uHN775nfT29Vfb5CM+spOw1/8Htm1bvztK+434gB4lBXCda29v97Y/cM/fVYNPVZsWhIF4QF9fP1de/TYOH+4CSNKDCSOGKvhR5+N3v/c67vrb3dE6/2qt9DjwF/xx+wNrvjQapn/MqIXPo/XLNk3mE875DxhjbaW7CscEQUBzUyMbN27ijW9+Z5QNSIKCCSNDEPikPI/PfeF6vnvDD5k16yRKpVK1h1UQnLqSavDW8K2lozaARzN/ptDB5s13dmsQXIUgIFWbOCXfZ/r0Vm76zS28+30fLm+pleiAhFri+z6e53Hjyp/wsU98hpkzp9dC+MuBP5z72PYH7vl7R0eHrUWrr6EyBovrw81E5i9Z/iXPS10d+CWfCjcTGYxnLbv37OXzn/k4r3vNK5KgYELNiNN9q9es41nPfWm5X2IN/P7AGM8GQbD6pFZ70apVi12UOp+UFkBEZwAdts7LvzsI/LVirVetKwAQOMesWSfx7vddx/d/8H9RpWB1aZmEhFj4196znpe/6vUYEzZZrYGbqWBw6nqsk1evWrWqFJn+o2q7jkUJnQJs3LixB9xrUA1Aqv7hcUFQfX09//KWd3L7X+7E87xECSRUTJjusxw8dJgrXvMGDh4+TCaTrlG2SQNjrVXn3rN1691rQ8t49Ez/mDGqoV0ZQLu3bfPau1XdO4z1bKXbiw8m3iGnrq6Of7rqrdyzbn2kBJJCoYThEW7oYeju7uGK1/wzu3bvpanqMt+Q0O9Pec4v/Wj7A2u+1N4eusU1uOxhM6YN9uJ9zRYsWf5D46VeVO1agRhrDf39OVpamll5w9dZds7SJCaQMGTi9SXd3T28/IrX8+c77mLG9Ok1sibViVhR1a1a9C/Yvv2ew/EfanDwYTPWHTYFkPnzl7VI2vubiCxSDbTSXYUGY62NlEDTICXg16JRQ8IkJq7y6+7u4WVXvJ477vgbM2ZMo1SqyQStQCAiokX/Sdu23XPHaOb8j8VYL6NT6JDt2+85RMl/ZXh/qo8HQBi8qa+vo6urh46Xv461ZXcgiQkkHJsw4Dcw89dY+EHVN9bzVN07QuFv98ZS+GHsFQDleMC2e+4IAvfPtYoHwJFK4KWv+EdW/X1NEhNIOCZxtH/f/gO8/IorQ7O/hsKvqr7xUikXlL61bfOaz8bp8JocvArGgQKA8Ea0ew9tWXO98/2vGpvyQGtyc2Il0NPTy3Ne8IpyijBZQZgQ4/t+mOpbt56nPeOF3PW3u5kxvYYzPxpY63ku8P9W7POuBkyYDh97xokCgLg+YNsDq98Q+P4dxngeVa4XiAmCgHQ6TSqV4k1vfTffueGH5WXESdnw1CaOC636+xpe+op/ZPeevTQ3N9XQSlQnYkTVHdSie8muXav64RoYJ7vejnUQ8GgMwNy5S1ttNvM3Y8yiWiwdLh/cCKpwuKuLN7z+Nfz7Rz4AhEVENukqNKWIu/lYa7nhxh/z9nd+EGOETCZTS+tQIdzWS13xidseWPeXsQ76Hc14G/UubiDiHC9RdQdFjNSiUhAGVgpOn9bKV776Ta5649vp7unFGpMEB6cQQbRtt7WW//zcl/nXd7wPz7Ok0+laC38gxhjngqtC4R/7oN/RjDcLICLUkguWnPN4MenbVV28w0jNrtfzPPbt28+FF5zP5z/z7yw964wkTTgFiOtBunt6+Ld3X8sNN/6ImTNm1L61nGrJplKpwC/963gK+h3NeLMAIlYGtLd72x5Y9xfngquMsXFzhJo9Id/3mTXrJNasXccLX/JqfvGr35ZrvJPGIpMPVSUIQuG/d/0GXtjxar5/44+ZPesknHO1Fn7feqlU4Pv/vW3zms9GlX7jauaPGacWQEx55eDrrfW+6lwQECqtGloClnyhSCGf541X/xMfeM/bywHCZPehycHgztE33Phj3n/Nx+jp6aWlpamGkf6IUPi9IPD/e9vm1VfCNQauG/VFPkNlnCuAgXLhkVQC8eA4cPAgFz/lSXzuPz/GwgXzCKLuL8mW5BOX2OTv6+vnmg99nK9/83s0NjaQSqVGIBWsvrEpz5WFv8OO9vLe4TIhRvZgJWCs91UdASUAYVzg8OEuZs2ayb9/5IM87znPAEisgQmIiwJ9IsLqNffwb++5jjvv+jszZ0yvvckPYZWfl/JcUPrats1rXj8RhB8miAIAWLFiRWrVqlWl+W3LP21t6m0u8EdECcS7Eff353hpx/O59oPvYtZJM6O4gGDMhLllU5LB6b0gCPjcF67ns1+4nkKhQFNT0whle8oz/23bNq++mHBMjluzfzDjNAj4SFatWlVqb2/3tm9e83Z1pTeIsZYaBwaBKFDk0drawg03/pinP+vF/PTnv8YYgzGSVBCOY4IgKKf37l59D8954Su57qOfwhhDY2PjyAi/Dpj9M1vs0+CaCSP8MIEsgAGi7cZGMCYQ43keuVyOQrHIMy57Kh+69j0sXrQASNyC8USctTHG0Nvby8f/4/N869vfp1Ao0tzcNHIVn48I+JXH4IQQfpiQCmCQO3CkEhBGwKIxRhAxHDp8mJNmzuTqq17L1W/4R1Ip74iBlzD6xL58rIh/+vOb+OSnv8C9926gtbVlZHeNUi1ZL5UKJlDA71hMSAUAj8wOqDpUnatFL4FjYa2lVCrR09PL8nPP4V/f8gae95xnAiSKYJQZ7OcD3L16LR//5Oe4tfN2rDU0NDSMZGWnAs5az0504YcJrABCwjqBhUvOvRxjbxCRaS50BEfENo/9y57eXpxzXHrJU7j6qtfylCc/ARjwQRNFMDIcLfgb79/M9f/9LX70fz+nt7eP1taWES7kUgfGiBHUBVGF3/jO85+ICa4AgPZ2j85Of+6i8y70PPmpiMxxQVCTVuPHIxbwnp5eFOUlL3oeb3nTVZxxehsw0KA0UQS1ITT1w1ZvAPsPHOTr3/wu//WVr9PV1U1LS/OIbxKrqoExxgK+c+7q7Q+s+e+JPPPHTHwFAJQrBuefOUfSdT+11l7o+yVfRlAJAOXe8F1d3TQ1NfKiFzybf3ztFSw963RgYMZKiokqwzmHQnml5q5de7jhxh/xzW9/n+0P7aCluZlUauQbvKiqb8NOPgdd4J67fcua22MXdERPPApMolEZZgfOOOOMpoKr+6wY73VRrcCIBAcHY224B0FPTy+NjQ084fEXHeEaQOIeDJWjzXwYMPV/edNv2bvvAA31dWSzGYJgBAp6HnE5Glgv5bkguMt3+sqHt6zeREeHZeX4WtVXKZNIAQChoDuABW3L3yrGfgZV1LkRiwsMJjZDe3v7SKU8LrzgfF758g7+4ZmX0djYACRWwbEY8NulbOY75/jj7XfwjW/dwB//9GcOHjxEU1MTqVRqZCr5HnlVDkSM9USd//WMyb013MtifK3nr5bJOALjZcMuDA6ab4ixc5zvj2hcYDCxa9DT24sLHIsXL+S5/3A5L3rhc8vuAQyksaaiMhgcrBs82+/atYef/vwmfvR/P2ftPffi+0FYu+95BKMi+FH/PmM9RX3U/VsY7AsvFZg0wg+TUwFExHGBFXMkE3zDGu/yIPBd1Hl4VOzwWLDz+Tx9/f00NzXxxCdcxPOf+yye8qQnMGfO7PJnY2Uwmd2E4wl9T28vf/nLXfzyppv5zc2/Z/eefWQzaerr6xEZ1erLAZPfBZs0cK/dvmXN7RM90v9oTGIFAIPNtYVt512DMdcC6AhnCY4mTB8afD+gr6+fIPCZPXsWj3vsBTzj6ZfylCc/njknzz7iO/Ggn8jWQSjwiqKYoxRbLPS//u3vue1Pf2Hbtu0EgaOxsYF0OoVzo9yXQTVAxBrr4Vzwg1Jf7uqdOzcciLNMo3cho8vEHFnDIx51buGScy9XY79gjD3N+aUAkREpIX40Qh9XKJZK9Pf149RxcqQMLr/sqTzm/HM5/bQlj/herBDiFW7jTSnEqc/YRD+WJbNr9x7uvnstt9z6Rzr/+Ge2bduOHwTU19WRyWQQkVHy74++9Khrr7oegfc9uOnuL4R/mlz+/rEYX6NoJIk0+SmnnDkjXZ/9ohj7MlWHc27E04XHYrCAlEol+iJl0NrSwtlLz+SCxyznootWsHzZ2Zx66pxHfN+FwU1UIdQFAysVR0o5xIJZFnaigMtx3JbDh7u4d/1G7vzb37nzrr+zZu069uzZh6pSV5cdS6EPGTzra/BXDfyrtz9wz98nQ35/qEwdBQAM1ugLTjv/ZYJ8Wow5xY1ybOBoBguQ7/vk8nmKxRKetcyYMZ22JYs4/bQlPO6xKzjj9NNYvHgBzU1Nxz1ebDof2edOyoriRCgKg2byWKE8Wmwil8vz0I6H2bx5C3f+7W7uvXcDmx7Yws5duykWinieR11dlnQ6Xb7GMWzJrqrqrPWsU+fj+Oi2B5o/Ap3+ZDf5j2aKKQAABDoMrAzmzTv/FJvVj4B5LYC6wI/ShWN6X4wxGBGU0DooFAoUSyUEoa6+jtmzTmLhwvksXjifhQvms2zZUuqyWdqWLCKVStHU1Dgi15XL5ykUCmzbtoOenh7u37yFbdseYsPGTTz00MPs3LWbnp6wTNrzPDKZNOl0OmrHHsUDxngfhjDCbzwRg6reAv77Hty09q/Rn8tp5KnCVFQAEYMChOFagk+LMWe7wKE6Nm7BsTja53fORUqhiB8EqHOkUimsNcycOYNUKsXppy3BOcfCBfM49dRTcM6RTqVYfu45eJ4tm+5HE2ch7ttwPwcPHSbleXR193DvvfdhPY+tD26jp6eXrq5u8vkCfuCjTvFSHulUinQ6jbU27IahGrop42bjFQ1AjLFWnNO9gn5kwNcvN+0cLxc7akxhBQCA0NFhWLkyWLp0abq3lHmnwDuMsS2RW6C12pSklgxWCiID+x2USiVUlXyhAIALHIELQMPvpNIpZAiPvFQqhW6EgIjBi1J2oYCH/5YoOyHCuJndj4NDVY31bHh97huBkfc/tPHunQwKEI/h9Y0pU10BRAxYA4sWnXu6et67gdeGASrfRbdp3CfnB3z1+LEOzhZoWVEM5Tjl72mYxoMBRTNOBf1oVFWdMdaKETTQW5zRf99+/923hH+e/BH+oZAogAGE9nYbB4Dmn37+paK8y4hcpoDGxfwTQBFMcTRaueeJMahz61T5zLbNd389/PPUifAPhUQBPBIDHTKQLTjv5YK8V8Sco6qoSxTBOGWQ4FucC/YqfKExVfjk+vXriwwK/o71hY4nEgVwXDosrFTALV26NN1XzLwK4V/NEYoAxmOMYIrhVFWNMTYS/D3AV4xf+vLWrev2AEym1Xu1JlEAJ2TAVzxaEYR+tVNU3VhUFU5hFNShIJGP75x7pOAn5v4JSQbs0DjCfFy6dGm6v5B5hhr+RUQuExFcEMSVZYl7MHLEytaGRUmCU7dOkM+LX/xZWfDDYp4pmdYbLokCGB7ltGH8xqK28y5zwhXA84zY5rD6LnAomlgFNaE822OMNcYQ9X38vaDf8bT3xs2bN4d5z9DUT2b8YZAMzsqILYLyYGtrWzbXx/4jyMvEmDMhKslVF8cKEmUwPJyqOhHxBs32exB+ZuCLW++/e235k4ngV0wyIKumIwoChlZBW1tbxtemy1X0xSDPN8Y0ATgXoKq+CJIog2OiRAE9EbEiRsQIUYPXW1FuMEHpVwP+/SOVcMLwSQZh7XiEe3Bq27K5Ht5lCC9H9RJjrYcOsgwouwlTNWagoE4VFREvrC40qDrUubUq5tuo+9X2zavXD3xlIDszZlc9iUgUQO2JZiYYnHOe33beUsE8HfRi0Kcaa5vCRXcODQmmgHUweJY34cuACGEDV/2rYH/r1N28/YHVdzAg5HGRVhLYqzGTdaCNF445cNvals0t4V0mIk9WdZeKyHwxhuMohLjH4UR7VlELLdVohjcgRkxYZhzWUrgDIH8C+YPifnvkTE8czXcks/2IMdEG1UTGtLe3m86jBvScOSvqs03B2U55CsozQZeLmJlibFiHr2Hmi3BRS/i98aUYIsUWXZuiCKGwS7ivIiKoczh1XYLcD65Tnfm1n/ZW79xw14FBx4oVZmziJ7P9CDPWg2eqYmhvN3TO0qNLUxcvXtGiXnC6c+aJgnsKImeo6kIxpn5gJd8R7bdcPMsCSPlDx1zANNTnfbTgDXQI0fA/ovPIgKDH/wTC5p8BsBPRDTj+rKq3lbzU2l33r9p/9L04lmJMGB0SBTD2hIVD7e1ybHO3wy5ZsvWUknWnGeeWgZyHMN+paxPkJGNMHWWDgMFyGq7vJ35biXrdn+Byws5I8WrAsHfAUT0IwzXAALiwgcJBRNYrHBDVVSLeXSruoWKv2bZr16r+R/ze9nYbKb9klh9jEgUw/hikEB5pIcTMnfu4unS6dFKQYgklvxVhebguQR+rIp6oNiLSNvANzRpj604kbYKEQg1d8TuqbreI7FIQlNVipJvAbSPlPahBsMdz9uEtW1Z1HeeQ0QyfCPx4JFEA45/Itu4Q2vfGSmFIabD5y5ZNi8U4lXKNvpdt40TbZnseOLdbC/5uAFpa2H7Pn7o58YYYBjqkvX2vdA5c46TspT+ZSBTAxGVAMQDt7XsFIPKlofbCF8YT2ttNO9AJkAj6hCdRAJMbOfK/O4b4vFceS6ATAU9ISEhISEhISEhISEhISEhISEhISEhISEhISEgY//x/X1UTQzQvl7gAAAAASUVORK5CYII="

# Built-in mascots: original "sorting-center helper" characters, one per parcel stage (128 px PNG).
MASCOTS = {
    'Shipped': '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',
    'Dispatched': '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',
    'With Royal Mail': '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',
    'At mail centre': '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',
    'At delivery office': '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',
    'Out for delivery': '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',
    'Delivery attempted': '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',
    'Delivered': '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',
}


if __name__ == "__main__":
    if sys.stderr is None or sys.stdout is None:  # started with pythonw (Start with Windows)
        _log = open(Path(__file__).with_name("error.log"), "a", encoding="utf-8")
        sys.stderr = sys.stderr or _log
        sys.stdout = sys.stdout or _log
    run_gui()
