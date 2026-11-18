@echo off
setlocal
title SID's Sorting Center - launcher
cd /d "%~dp0"

rem ---- 1. Find a real Python 3 (not the Microsoft Store shortcut)
set "PY="
py -3 --version >nul 2>&1 && set "PY=py -3"
if not defined PY (
  python --version >nul 2>&1 && set "PY=python"
)
if not defined PY (
  echo.
  echo  Python 3 is not installed, or not on PATH.
  echo.
  echo  1. Download it from https://www.python.org/downloads/windows/
  echo  2. In the installer, TICK "Add python.exe to PATH", then Install.
  echo  3. Double-click this file again.
  echo.
  start "" https://www.python.org/downloads/windows/
  pause
  exit /b 1
)
echo Using: %PY%
%PY% --version

rem ---- 2. One-time setup
if not exist ".venv\Scripts\python.exe" (
  echo.
  echo First run: setting up, this takes about a minute...
  if exist .venv rmdir /s /q .venv
  %PY% -m venv .venv
  if errorlevel 1 goto :fail
)
".venv\Scripts\python.exe" -c "import requests, keyring, tkinter, pystray, PIL" >nul 2>&1
if errorlevel 1 (
  echo Installing requirements...
  ".venv\Scripts\python.exe" -m pip install --disable-pip-version-check -r requirements.txt
  if errorlevel 1 goto :fail
  ".venv\Scripts\python.exe" -c "import tkinter" >nul 2>&1
  if errorlevel 1 (
    echo.
    echo  Your Python was installed without Tk/tkinter, which the window needs.
    echo  Re-run the Python installer, choose Modify, and tick "tcl/tk and IDLE".
    goto :fail
  )
)

rem ---- 3. Launch without a console window, then close this launcher
rem      (errors go to error.log; if it fails to start, this window stays open and shows why)
echo Starting SID's Sorting Center...
type nul > error.log
if exist ".venv\Scripts\pythonw.exe" (
  start "" ".venv\Scripts\pythonw.exe" "%~dp0sids_sorting_center.py"
) else (
  start "" /min ".venv\Scripts\python.exe" "%~dp0sids_sorting_center.py"
)
timeout /t 4 /nobreak >nul
for %%A in (error.log) do if %%~zA GTR 0 (
  echo.
  echo  The app reported an error:
  type error.log
  goto :fail
)
exit /b 0

:fail
echo.
echo  Something went wrong. Take a screenshot of this window and send it over.
pause
exit /b 1
