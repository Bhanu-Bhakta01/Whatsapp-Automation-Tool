#!/usr/bin/env bash
# One-time setup for the WhatsApp Campaign Sender (Ubuntu).
# Creates a private Python environment in ./venv and downloads the browser.
set -e
cd "$(dirname "$0")"
echo "== WhatsApp Campaign Sender: setup =="

if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3 is missing. Install it with:  sudo apt install python3"; exit 1
fi
if ! python3 -c "import venv, ensurepip" >/dev/null 2>&1; then
  echo "Installing python3-venv (asks for your password once)..."
  sudo apt-get update && sudo apt-get install -y python3-venv python3-pip
fi

if [ ! -x venv/bin/python ]; then
  python3 -m venv venv
fi
venv/bin/python -m pip install --upgrade pip
venv/bin/python -m pip install --upgrade pandas odfpy openpyxl playwright
echo "Downloading the browser used for WhatsApp Web (~150 MB, one time)..."
venv/bin/python -m playwright install chromium

# Check the browser can actually start; if libraries are missing, install them.
if ! venv/bin/python - >/dev/null 2>&1 <<'EOF'
from playwright.sync_api import sync_playwright
with sync_playwright() as p:
    p.chromium.launch(headless=True).close()
EOF
then
  echo "Installing a few system libraries the browser needs (asks for your password)..."
  sudo venv/bin/python -m playwright install-deps chromium
fi

chmod +x run.sh whatsapp_bulk_sender.py 2>/dev/null || true
echo
echo "All set. Start the sender with:   ./run.sh"
