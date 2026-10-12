#!/usr/bin/env bash
# Starts the WhatsApp Campaign Sender. The control panel opens in your browser.
cd "$(dirname "$0")"
if [ ! -x venv/bin/python ]; then
  echo "First run ./setup.sh (one time only)."
  exit 1
fi
exec venv/bin/python whatsapp_bulk_sender.py "$@"
