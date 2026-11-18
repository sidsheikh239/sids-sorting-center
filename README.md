# SID's Sorting Center

A small Windows app that watches your Gmail for Pokémon Center shipping emails, keeps a list of every Royal Mail parcel, and tells you (in the app and on Discord) when a parcel moves to its next stage.

## Setup (once)

1. Install Python 3 from python.org if you don't have it. Tick **"Add python.exe to PATH"** during the install.
2. Double-click **`Start SID's Sorting Center.bat`**. The first time, it takes about a minute to set itself up.
3. On the **Settings** tab:
   - **IMAP email**: the Gmail address that gets your Pokémon Center emails.
   - **App password**: create a new one at https://myaccount.google.com/apppasswords. IMAP must be turned on in Gmail (Settings › Forwarding and POP/IMAP).
   - **Discord webhook URL** (optional): in Discord, go to Server Settings › Integrations › Webhooks › New Webhook › Copy URL.
   - **Royal Mail API keys** (optional, see below).
   - Click **Test IMAP login**, then **Send Discord test**, then **Save**.
4. Go to the **Dashboard** and click **▶ Start tracking**.

## What it shows

- **Shipped orders / In transit / Delivered** counts at the top.
- A table of parcels: tracking number, order number, stage, latest update. Double-click a row to open it on Royal Mail.
- A log of every new shipment and stage change.

Stages: **Shipped → In transit → Out for delivery → Delivered**.

## Where updates come from

- **Always:** Pokémon Center's own emails ("on its way", "will arrive soon", "delivered").
- **With Royal Mail API keys:** live Royal Mail scans every check (for example "Item received at Mail Centre"). Royal Mail's website blocks automated checks, so the app uses their official Tracking API instead. Register for free at https://developer.royalmail.net, subscribe to the *Tracking API*, and paste the client ID and secret into Settings.

## Running in the background (Settings)

- **Start with Windows**: opens hidden in the system tray when you sign in, and starts tracking on its own.
- **Close to tray**: while tracking, the X button hides the window instead of quitting. Right-click the tray icon (near the clock) to open it, check now, send a summary, or quit.
- **Keep the PC awake** while tracking (optional).
- **Windows pop-ups** for the same alerts that go to Discord.

## Smart alerts (Settings)

- **Stuck parcels**: one Discord alert when parcels haven't had a new scan for 3 days (change the number, or 0 to turn off). They also show as **⚠ STUCK** in the table, with a **Stuck** filter.
- **Daily summary**: a Discord message at 09:00 with counts per stage and anything stuck or with a delivery attempt.
- **Ping on Delivery attempted**: that alert mentions @everyone (or whoever you choose) so you don't miss it.

## Missed deliveries, addresses and weekly CSV

- **Rebook**: when Royal Mail tries and fails to deliver, the parcel panel shows a **Rebook missed delivery** button. It copies the tracking number (or the card reference, if the tracking text shows one) and opens Royal Mail's redelivery page. The Discord alert includes the same link.
- **Group by address**: the button above the table groups parcels going to the same postcode, with "2 of 3 delivered" on each group. Names are often spelled differently, so grouping uses the postcode. When every parcel to an address is delivered, you get one Discord alert.
- **Weekly CSV**: every Monday (change the day in Settings, or blank to turn off) the full parcel list is posted to Discord as a CSV file, at the daily summary time.

## More (v3.1+)

- **Problem alert**: if checks keep failing for an hour (Gmail password changed, no internet, tracking page down), one Discord alert, then one "working again" message. Change the time in Settings › Smart alerts (0 = off).
- **History tab**: parcels older than 14 days move here (searchable) instead of disappearing.
- **Notes**: tick Paid / Handed over and type a note in the parcel panel. Shown in the NOTES column, search and the CSV.
- **Stats tab**: average time from despatch to first Royal Mail scan, to delivery, and how long parcels are waiting at the Pokémon Center hub.

## Icon and shortcut

The app uses its own red-and-white ball icon on the window, taskbar and tray. In **Settings › Running in the background**, click **Create desktop & Start menu shortcut** for a shortcut with the same icon that opens the app without the black console window.

## Mascots and pictures

The app comes with its own little sorting-center mascots, one for each stage. They parade across the top of the app, sit in the parcel panel, and appear in the corner of every Discord alert (matching the parcel's stage).

To use your own pictures instead, go to **Settings › Look & pictures**:
- **Header picture**: a PNG or GIF shown at the top of the app.
- **Discord picture**: a PNG, JPG or GIF shown on every Discord alert.
- Untick **Show the stage mascots on Discord alerts** for plain alerts.

## Discord

The first scan only fills the list, so you don't get a flood of old parcels. After that, every new shipment and every stage change is posted to your webhook.

## Privacy

- Gmail is opened **read-only**. Nothing is marked read, moved or deleted.
- The app password, Discord webhook and Royal Mail secret are stored in **Windows Credential Manager**, never in a file.
- Parcel data is kept in `%APPDATA%\SIDsSortingCenter\`.
