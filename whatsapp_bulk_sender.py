#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WhatsApp Campaign Sender
========================
Sends a personalised WhatsApp message (with the campaign photo) to every
contact in a LibreOffice / Excel sheet through WhatsApp Web, at a paced,
human-like speed.

  * Column A = phone number, column B = name.  Names typed in the Preeti font
    are converted to proper Unicode Nepali automatically.
  * "(Name)" in the message is replaced with each person's name.
  * Test mode sends to one number you type in.
  * Bulk mode runs from row 1001 (or any row) to the end, with live counts,
    pause / resume / stop and an estimated finish time.
  * Every result goes into <sheet>_whatsapp_log.csv next to the sheet, so if
    you stop, close the app or the laptop restarts, pressing Start again
    continues where it left off (nobody gets the message twice).

Run it with ./run.sh   (or:  venv/bin/python whatsapp_bulk_sender.py)
The control panel opens in your normal web browser. WhatsApp Web opens in
its own Chromium window - scan the QR code once and the login is remembered.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import json
import mimetypes
import os
import queue
import random
import re
import socket
import sys
import threading
import time
import traceback
import unicodedata
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

try:
    import pandas as pd
except ImportError:  # pragma: no cover
    pd = None

# ----------------------------------------------------------------------------
# Paths & defaults
# ----------------------------------------------------------------------------
APP_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_FOLDER = "/home/bhanu/Desktop/Baba/UdhyogBadijya"
WA_BASE = os.environ.get("WA_BASE_URL", "https://web.whatsapp.com").rstrip("/")
PROFILE_DIR = os.environ.get("WA_PROFILE_DIR", os.path.join(APP_DIR, "whatsapp_session"))
SETTINGS_FILE = os.environ.get("WA_SETTINGS_FILE", os.path.join(APP_DIR, "sender_settings.json"))
ERROR_LOG = os.path.join(APP_DIR, "sender_errors.log")
COUNTRY_CODE = "977"
SHEET_EXT = (".ods", ".xlsx", ".xls", ".csv")
IMAGE_EXT = (".jpg", ".jpeg", ".png", ".webp")

DEFAULT_TEMPLATE = """नमस्कार (Name) ज्यू,

बुटवल उद्योग वाणिज्य संघ, रुपन्देहीको ७३ औँ वार्षिक साधारण सभा तथा २६ औँ अधिवेशनमा मैले कोषाध्यक्ष पदमा उम्मेद्वारी दिएको छु। मेरो उम्मेद्वारीमा यहाँको साथ, सहयोग र अमुल्य मतको लागि हार्दिक अनुरोध गर्दछु।

टिकाराम बन्जाडे
कोषाध्यक्ष पदका उम्मेद्वार
बु उ वा संघ, रुपन्देही"""

# Pacing.  gap = wait after each sent message (seconds); every = take a longer
# break after this many sent messages; brk = break length (minutes);
# daily_cap = stop for the day after this many sent (0 = no cap).
PACE_PRESETS = {
    "safe": dict(gap_min=40, gap_max=80, every_min=15, every_max=25, brk_min=8, brk_max=15, daily_cap=200),
    "balanced": dict(gap_min=25, gap_max=50, every_min=20, every_max=30, brk_min=5, brk_max=10, daily_cap=400),
    "fast": dict(gap_min=12, gap_max=25, every_min=30, every_max=40, brk_min=3, brk_max=6, daily_cap=0),
}
PACE_KEYS = ("gap_min", "gap_max", "every_min", "every_max", "brk_min", "brk_max", "daily_cap")

DEFAULT_SETTINGS = dict(
    folder=DEFAULT_FOLDER, sheet="", image="", mode="caption",
    phone_col=1, name_col=2, preeti=True,
    template=DEFAULT_TEMPLATE,
    start_row=1001, end_row=0, resume=True,
    preset="balanced", **PACE_PRESETS["balanced"],
    hours_on=True, hours_from="07:00", hours_to="21:00",
    test_phone="", test_name="भानु", _preeti_sheet="",
)
INT_KEYS = {"phone_col", "name_col", "start_row", "end_row", "every_min", "every_max", "daily_cap"}
FLOAT_KEYS = {"gap_min", "gap_max", "brk_min", "brk_max"}
BOOL_KEYS = {"preeti", "resume", "hours_on"}

FINAL_STATUSES = ("SENT", "NO_WHATSAPP", "INVALID_NUMBER")   # skipped when resuming
DEFAULT_SEND_SECONDS = 20.0   # first guess of how long one send takes (refined live)


# ----------------------------------------------------------------------------
# Preeti (legacy Nepali font) -> Unicode
# ----------------------------------------------------------------------------
_PREETI_COMBOS = [
    ("km", "फ"), ("Km", "फ्"), ("em", "झ"), ("Em", "झ्"), ("qm", "क्र"), ("Qm", "क्त"),
    ("pm", "ऊ"), ("cf", "आ"), ("O{", "ई"), ("P]", "ऐ"),
]
_PREETI_MAP = {
    "a": "ब", "b": "द", "c": "अ", "d": "म", "e": "भ", "f": "ा", "g": "न", "h": "ज",
    "i": "ष्", "j": "व", "k": "प", "l": "ि", "m": "", "n": "ल", "o": "य", "p": "उ",
    "q": "त्र", "r": "च", "s": "क", "t": "त", "u": "ग", "v": "ख", "w": "ध", "x": "ह",
    "y": "थ", "z": "श",
    "A": "ब्", "B": "द्य", "C": "ऋ", "D": "म्", "E": "भ्", "F": "ँ", "G": "न्", "H": "ज्",
    "I": "क्ष्", "J": "व्", "K": "प्", "L": "ी", "M": "ः", "N": "ल्", "O": "इ", "P": "ए",
    "Q": "त्त", "R": "च्", "S": "क्", "T": "त्", "U": "ग्", "V": "ख्", "W": "ध्", "X": "ह्",
    "Y": "थ्", "Z": "श्",
    "!": "ज्ञ", "@": "द्द", "#": "घ", "$": "द्ध", "%": "छ", "^": "ट", "&": "ठ", "*": "ड",
    "(": "ढ", ")": "ण्", "-": "(", "_": ")", "=": ".", "+": "ं",
    "[": "ृ", "]": "े", "{": "\x01", "}": "ै", "\\": "्", "|": "्र",
    ";": "स", ":": "स्", "'": "ु", '"': "ू", ",": ",", ".": ".", "/": "र", "?": "रु",
    "<": "?", ">": "श्र", "`": "ञ", "~": "ञ्",
    "1": "१", "2": "२", "3": "३", "4": "४", "5": "५", "6": "६", "7": "७", "8": "८",
    "9": "९", "0": "०",
    "§": "ट्ट", "è": "ध्", "Ë": "ङ्ग", "ª": "ङ", "«": "्र", "ˆ": "फ्", "¿": "रू",
    "Í": "ङ्क", "å": "द्व", "Ø": "्य", "ß": "द्म", "Ì": "न्न", "´": "झ", "‰": "झ्",
    "Ý": "ट्ठ", "¶": "ठ्ठ", "•": "ड्ड", "÷": "/", "Å": "हृ", "ç": "ॐ", "°": "ङ्क",
    "Œ": "त्त्", "¥": "र्", "Ö": "=", "Ù": "स्", "Ú": "ु", "æ": "“", "Æ": "”",
}
_C = "[\u0915-\u0939\u0958-\u095F]"          # consonants
_M = "[\u093E-\u094C\u0962\u0963]"           # dependent vowel signs
_CLUSTER = "(?:%s\u094D)*%s" % (_C, _C)


def preeti_to_unicode(s: str) -> str:
    if not s:
        return ""
    # "(" and ")" are letters in Preeti (ढ, ण्) but typists also use them as real
    # brackets around nicknames:  "yfkf (rtL{)".
    s = re.sub(r"(^|\s)\(([^()]*)\)(?=\s|$)", "\\1\x02\\2\x03", s)
    out, i = [], 0
    while i < len(s):
        for k, v in _PREETI_COMBOS:
            if s.startswith(k, i):
                out.append(v)
                i += len(k)
                break
        else:
            out.append(_PREETI_MAP.get(s[i], s[i]))
            i += 1
    t = "".join(out)
    t = re.sub("\u094D([\u0947\u0948])\u093E", r"\1", t)      # I]f -> क्षे
    t = t.replace("\u094D\u093E", "")                           # half letter + ा = full letter
    for a, b in (("ाे", "ो"), ("ाै", "ौ"), ("ेा", "ो"), ("ैा", "ौ"),
                 ("अो", "ओ"), ("अौ", "औ"), ("आे", "ओ"), ("आै", "औ"), ("एे", "ऐ")):
        t = t.replace(a, b)
    t = re.sub("\u093F(%s)" % _CLUSTER, "\\1\u093F", t)        # ि typed before its consonant
    t = re.sub("(%s+)\u094D\u0930" % _M, "\u094D\u0930\\1", t)  # k]| -> प्रे
    t = re.sub("([\u0901\u0902])(%s)" % _M, r"\2\1", t)         # ँ/ं before a vowel sign
    t = re.sub("(%s%s*[\u0901\u0902]?)\x01" % (_CLUSTER, _M), "र्\\1", t)  # reph
    t = t.replace("\x01", "र्").replace("््", "्").replace("\x02", "(").replace("\x03", ")")
    return re.sub(r"\s+", " ", t).strip(" ,;")


def has_devanagari(s: str) -> bool:
    return bool(re.search("[\u0900-\u097F]", s or ""))


def looks_like_preeti(names) -> bool:
    sample = [n for n in names if n and n.strip()][:300]
    if not sample:
        return False
    latin = sum(1 for n in sample if not has_devanagari(n) and re.search(r"[a-zA-Z]", n))
    marks = sum(1 for n in sample if re.search(r"[\]\[/;'{}|>]", n))
    return latin > 0.6 * len(sample) and marks > 0.3 * len(sample)


def greeting_name(name: str) -> str:
    """Name as used in the greeting: drop nicknames in brackets, tidy spaces."""
    n = re.sub(r"\s*\([^)]*\)", "", name or "")
    return re.sub(r"\s+", " ", n).strip(" ,;")


# ----------------------------------------------------------------------------
# Phones & messages
# ----------------------------------------------------------------------------
_DEV_DIGITS = str.maketrans("०१२३४५६७८९", "0123456789")


def normalize_phone(raw, default_cc: str = COUNTRY_CODE):
    """Return digits with country code (e.g. 9779857051494) or None."""
    s = str(raw or "").strip().translate(_DEV_DIGITS)
    if re.fullmatch(r"\d+\.0+", s):
        s = s.split(".")[0]
    for part in re.findall(r"\+?\d[\d \-]{6,}\d", s):
        d = re.sub(r"\D", "", part)
        if d.startswith("00"):
            d = d[2:]
        if len(d) == 10 and d.startswith("9"):                  # Nepal mobile
            return default_cc + d
        if len(d) == 13 and d.startswith(default_cc + "9"):
            return d
        if part.startswith("+") and 8 <= len(d) <= 15:           # other country, typed with +
            return d
    return None


def build_message(template: str, name: str) -> str:
    name = greeting_name(name)
    if name:
        return re.sub(r"\(name\)", lambda _m: name, template, flags=re.I)
    msg = re.sub(r"\s*\(name\)\s*ज्यू", "", template, flags=re.I)
    msg = re.sub(r"\s*\(name\)", "", msg, flags=re.I)
    return re.sub(r"नमस्कार\s+,", "नमस्कार,", msg)


def pretty_phone(p):
    if not p:
        return ""
    if p.startswith(COUNTRY_CODE) and len(p) == 13:
        return "+977 " + p[3:]
    return "+" + p


class Contact(object):
    __slots__ = ("row", "phone_raw", "phone", "name_raw", "name")

    def __init__(self, row, phone_raw, phone, name_raw, name):
        self.row, self.phone_raw, self.phone, self.name_raw, self.name = row, phone_raw, phone, name_raw, name


def read_columns(path, phone_col=1, name_col=2):
    """Returns (phones, names) as lists of strings; index 0 = spreadsheet row 1."""
    if pd is None:
        raise RuntimeError("pandas is not installed - run setup.sh")
    ext = os.path.splitext(path)[1].lower()
    if ext == ".csv":
        df = pd.read_csv(path, header=None, dtype=str, keep_default_na=False)
    else:
        engine = "odf" if ext == ".ods" else None
        sheets = pd.read_excel(path, sheet_name=None, header=None, dtype=str, engine=engine)
        df = None
        for d in sheets.values():
            if d.shape[0] > 0 and d.shape[1] >= max(phone_col, name_col):
                df = d
                break
        if df is None:
            raise RuntimeError("No sheet with at least %d columns found" % max(phone_col, name_col))
    df = df.fillna("")
    if df.shape[1] < max(phone_col, name_col):
        raise RuntimeError("The sheet has only %d column(s)" % df.shape[1])
    phones = [str(x).strip() for x in df.iloc[:, phone_col - 1]]
    names = [str(x).strip() for x in df.iloc[:, name_col - 1]]
    return phones, names


def make_contacts(phones, names, use_preeti):
    """Row numbers match LibreOffice's row numbers."""
    contacts = []
    for i, (p, n) in enumerate(zip(phones, names)):
        if not p and not n:
            continue
        conv = preeti_to_unicode(n) if (use_preeti and not has_devanagari(n)) else n
        contacts.append(Contact(i + 1, p, normalize_phone(p), n, conv))
    info = dict(rows=len(contacts), last_row=contacts[-1].row if contacts else 0,
                preeti_used=bool(use_preeti), bad_phones=sum(1 for c in contacts if not c.phone))
    return contacts, info


# ----------------------------------------------------------------------------
# Send log (CSV) - this is what makes resume work
# ----------------------------------------------------------------------------
class SendLog(object):
    FIELDS = ["time", "row", "phone", "name", "status", "detail"]

    def __init__(self, path):
        self.path = path
        self.lock = threading.Lock()
        self.last = {}       # phone -> status (latest)
        self.sent_by_day = {}
        if path and os.path.exists(path):
            with open(path, newline="", encoding="utf-8") as f:
                for r in csv.DictReader(f):
                    self._note(r.get("phone") or "row%s" % r.get("row", ""), r.get("status", ""), r.get("time", ""))

    def _note(self, phone, status, when):
        if not phone:
            return
        self.last[phone] = status
        if status == "SENT":
            day = (when or "")[:10]
            self.sent_by_day[day] = self.sent_by_day.get(day, 0) + 1

    def add(self, row, phone, name, status, detail=""):
        when = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with self.lock:
            new = not os.path.exists(self.path)
            with open(self.path, "a", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                if new:
                    w.writerow(self.FIELDS)
                w.writerow([when, row, phone or "", name, status, detail])
            self._note(phone or "row%s" % row, status, when)

    def sent_on(self, day: dt.date) -> int:
        return self.sent_by_day.get(day.strftime("%Y-%m-%d"), 0)


# ----------------------------------------------------------------------------
# Time window / ETA helpers
# ----------------------------------------------------------------------------
def parse_hhmm(s, default):
    try:
        h, m = str(s).strip().split(":")
        return dt.time(int(h) % 24, int(m) % 60)
    except Exception:
        return default


class Pace(object):
    def __init__(self, s):
        self.gap_min = max(1.0, float(s["gap_min"]))
        self.gap_max = max(self.gap_min, float(s["gap_max"]))
        self.every_min = max(1, int(s["every_min"]))
        self.every_max = max(self.every_min, int(s["every_max"]))
        self.brk_min = max(0.0, float(s["brk_min"]))
        self.brk_max = max(self.brk_min, float(s["brk_max"]))
        self.daily_cap = max(0, int(s["daily_cap"]))
        self.hours_on = bool(s["hours_on"])
        self.h_from = parse_hhmm(s["hours_from"], dt.time(7, 0))
        self.h_to = parse_hhmm(s["hours_to"], dt.time(21, 0))
        if self.h_from == self.h_to:
            self.hours_on = False

    @property
    def gap_avg(self):
        return (self.gap_min + self.gap_max) / 2.0

    @property
    def break_avg(self):
        return (self.brk_min + self.brk_max) / 2.0 * 60.0

    @property
    def every_avg(self):
        return (self.every_min + self.every_max) / 2.0

    def in_window(self, t: dt.datetime) -> bool:
        if not self.hours_on:
            return True
        x = t.time()
        if self.h_from < self.h_to:
            return self.h_from <= x < self.h_to
        return x >= self.h_from or x < self.h_to

    def next_start(self, t: dt.datetime, next_day=False) -> dt.datetime:
        if not self.hours_on:
            return dt.datetime.combine(t.date() + dt.timedelta(days=1), dt.time(0, 0)) if next_day else t
        day = t.date() + dt.timedelta(days=1 if next_day else 0)
        cand = dt.datetime.combine(day, self.h_from)
        if cand <= t:
            cand += dt.timedelta(days=1)
        return cand

    def per_hour(self, send_s):
        per_msg = send_s + self.gap_avg + self.break_avg / self.every_avg
        return 3600.0 / per_msg


def simulate_finish(n, pace: Pace, send_s, start: dt.datetime, sent_today, since_break=0, next_break=None):
    """Walks forward message by message (gaps, breaks, hours, daily cap) -> finish time."""
    t = start
    if n <= 0:
        return t
    day, today = t.date(), sent_today
    every = next_break if next_break else pace.every_avg
    sb = since_break
    for i in range(n):
        for _guard in range(4):
            if t.date() != day:
                day, today = t.date(), 0
            if pace.daily_cap and today >= pace.daily_cap:
                t = pace.next_start(t, next_day=True)
                continue
            if not pace.in_window(t):
                t = pace.next_start(t)
                continue
            break
        t += dt.timedelta(seconds=send_s)
        today += 1
        sb += 1
        if i < n - 1:
            if sb >= every:
                t += dt.timedelta(seconds=pace.break_avg)
                sb, every = 0, pace.every_avg
            else:
                t += dt.timedelta(seconds=pace.gap_avg)
    return t


def fmt_when(t: dt.datetime) -> str:
    now = dt.datetime.now()
    clock = t.strftime("%I:%M %p").lstrip("0")
    if t.date() == now.date():
        return "Today " + clock
    if t.date() == now.date() + dt.timedelta(days=1):
        return "Tomorrow " + clock
    return t.strftime("%a %d %b, ") + clock


def fmt_dur(sec) -> str:
    sec = int(max(0, sec))
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    if h >= 24:
        return "%dd %dh" % (h // 24, h % 24)
    if h:
        return "%dh %02dm" % (h, m)
    if m:
        return "%dm %02ds" % (m, s)
    return "%ds" % s


# ----------------------------------------------------------------------------
# WhatsApp Web automation (Playwright).  Everything browser-related runs in
# this one thread.
# ----------------------------------------------------------------------------
class StopRequested(Exception):
    pass


class SendError(Exception):
    pass


JS_SCREEN = r"""() => {
  const q = s => document.querySelector(s);
  const useHere = [...document.querySelectorAll('button, div[role="button"]')]
      .find(b => /^\s*use here\s*$/i.test(b.innerText || ''));
  if (useHere) { useHere.click(); return 'loading'; }
  if (q('#side') || q('#pane-side') || q('[aria-label="Chat list"]') || q('[data-testid="chat-list"]') ||
      q('[data-testid="chatlist-header"]') || q('[data-icon="new-chat-outline"]')) return 'ready';
  if (q('canvas[aria-label*="QR" i]') || q('div[data-ref] canvas') || q('[data-testid="qrcode"]')) return 'qr';
  const t = (document.body && document.body.innerText || '').slice(0, 3000);
  if (/log in(to)? whatsapp web|scan (the|this) qr|link with phone number|steps to log in/i.test(t)) return 'qr';
  return 'loading';
}"""

JS_INVALID = r"""() => {
  const re = /invalid|not on whatsapp|isn.t on whatsapp|अमान्य|अवैध/i;
  const d = [...document.querySelectorAll('[role="dialog"], [data-animate-modal-popup="true"], [data-animate-modal-body="true"]')];
  if (d.some(x => re.test(x.innerText || ''))) return true;
  if (!document.querySelector('#main')) {
    const t = document.body ? document.body.innerText : '';
    if (/shared via url is invalid/i.test(t)) return true;
  }
  return false;
}"""

JS_TAG_COMPOSE = r"""() => {
  const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
  document.querySelectorAll('[data-wbs="compose"]').forEach(e => e.removeAttribute('data-wbs'));
  let c = [...document.querySelectorAll('#main footer div[contenteditable="true"], footer div[contenteditable="true"]')].filter(vis).pop();
  if (!c) c = [...document.querySelectorAll('div[contenteditable="true"]')].filter(vis)
        .find(e => !e.closest('#side') && /type a message|message/i.test(
          (e.getAttribute('aria-placeholder') || '') + (e.getAttribute('aria-label') || '') + (e.getAttribute('title') || '')));
  if (!c) return false;
  c.setAttribute('data-wbs', 'compose');
  return true;
}"""

JS_TAG_CAPTION = r"""() => {
  const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
  document.querySelectorAll('[data-wbs="caption"]').forEach(e => e.removeAttribute('data-wbs'));
  const eds = [...document.querySelectorAll('div[contenteditable="true"]')].filter(vis)
        .filter(e => e.getAttribute('data-wbs') !== 'compose' && !e.closest('#side'));
  const lab = e => (e.getAttribute('aria-label') || '') + (e.getAttribute('aria-placeholder') || '') +
                   (e.getAttribute('title') || '') + (e.getAttribute('data-placeholder') || '');
  let c = eds.find(e => /caption/i.test(lab(e)));
  if (!c) c = eds.filter(e => !e.closest('footer')).pop();
  if (!c) return false;
  c.setAttribute('data-wbs', 'caption');
  return true;
}"""

JS_TAG_MEDIA_SEND = r"""() => {
  const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
  document.querySelectorAll('[data-wbs="msend"]').forEach(e => e.removeAttribute('data-wbs'));
  const c = [...document.querySelectorAll('[aria-label="Send"], [data-icon="send"], [data-icon="wds-ic-send-filled"], [data-testid="send"]')]
      .filter(vis).filter(e => !e.closest('#main footer'));
  if (!c.length) return false;
  let b = c[c.length - 1];
  b = b.closest('[role="button"], button') || b;
  b.setAttribute('data-wbs', 'msend');
  return true;
}"""

JS_TAG_PHOTO_INPUT = r"""() => {
  document.querySelectorAll('[data-wbs="photo"]').forEach(e => e.removeAttribute('data-wbs'));
  const ins = [...document.querySelectorAll('input[type="file"]')];
  const i = ins.find(e => /image/.test(e.accept || '') && /video/.test(e.accept || ''));
  if (!i) return false;
  i.setAttribute('data-wbs', 'photo');
  return true;
}"""

JS_TAG_ATTACH = r"""() => {
  const vis = e => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
  document.querySelectorAll('[data-wbs="attach"]').forEach(e => e.removeAttribute('data-wbs'));
  const sels = ['button[title="Attach"]', '[aria-label="Attach"]', 'div[title="Attach"]',
                'span[data-icon="plus-rounded"]', 'span[data-icon="plus"]', 'span[data-icon="attach-menu-plus"]',
                'span[data-icon="clip"]', '[data-testid="clip"]'];
  for (const s of sels) {
    const e = [...document.querySelectorAll('#main ' + s + ', footer ' + s)].filter(vis)[0];
    if (e) { (e.closest('button, [role="button"]') || e).setAttribute('data-wbs', 'attach'); return true; }
  }
  return false;
}"""

JS_PASTE_FILE = r"""async ([b64, name, mime]) => {
  const target = document.querySelector('[data-wbs="compose"]');
  if (!target) return false;
  const bin = atob(b64), arr = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  const dt = new DataTransfer();
  dt.items.add(new File([arr], name, {type: mime}));
  target.focus();
  target.dispatchEvent(new ClipboardEvent('paste', {clipboardData: dt, bubbles: true, cancelable: true}));
  return true;
}"""

JS_COUNT_OUT = r"""() => document.querySelectorAll('#main div.message-out, #main [data-id^="true_"]').length ||
                       document.querySelectorAll('div.message-out').length"""

JS_PENDING = r"""() => document.querySelectorAll('#main [data-icon="msg-time"], #main [data-icon="status-time"]').length"""


def _norm_text(s):
    s = unicodedata.normalize("NFC", s or "")
    return re.sub(r"[\s\u200b\u200c\u200d\ufeff]+", "", s)


class Engine(threading.Thread):
    def __init__(self, app):
        threading.Thread.__init__(self, daemon=True)
        self.app = app
        self.cmds = queue.Queue()
        self.pw = None
        self.ctx = None
        self.page = None
        self.ctx_dead = True
        self.busy = False
        self.ema_send = DEFAULT_SEND_SECONDS
        self.since_break = 0
        self.next_break = None

    # ---------------- thread loop ----------------
    def run(self):
        while True:
            cmd, arg = self.cmds.get()
            if cmd == "quit":
                self._close()
                return
            self.busy = True
            self.app.stop_flag.clear()
            try:
                if cmd == "login":
                    self.ensure_ready()
                    try:
                        self.page.bring_to_front()
                    except Exception:
                        pass
                elif cmd == "test":
                    self.do_test(arg)
                elif cmd == "bulk":
                    self.do_bulk(arg)
            except StopRequested:
                self.app.log("Stopped.", "alert")
                if cmd == "bulk":
                    self.app.finish_run("stopped")
            except Exception as e:
                self.app.log("Problem: %s" % e, "error")
                self._trace()
                if cmd == "bulk":
                    self.app.finish_run("error")
            finally:
                self.busy = False
                self.app.paused.clear()
                if self.app.run_state in ("testing", "starting", "running", "paused", "break", "waiting"):
                    self.app.run_state = "idle"
                self.app.current = None
                self.app.next_at = None

    def _trace(self):
        try:
            with open(ERROR_LOG, "a", encoding="utf-8") as f:
                f.write("\n==== %s ====\n%s" % (dt.datetime.now(), traceback.format_exc()))
        except Exception:
            pass

    # ---------------- waiting helpers ----------------
    def check_stop(self):
        if self.app.stop_flag.is_set():
            raise StopRequested()

    def _pump(self, sec):
        """Sleep while letting the browser connection breathe."""
        try:
            if self.page is not None and not self.ctx_dead and not self.page.is_closed():
                self.page.wait_for_timeout(int(sec * 1000))
                return
        except Exception:
            pass
        time.sleep(sec)

    def nap(self, a, b=None):
        self._pump(random.uniform(a, b if b is not None else a))

    def sleep(self, seconds, show_next=True):
        """Interruptible sleep; Pause freezes the countdown."""
        end = time.time() + seconds
        while True:
            self.check_stop()
            if self.app.paused.is_set():
                t0, prev = time.time(), self.app.run_state
                self.app.run_state = "paused"
                self.app.next_at = None
                while self.app.paused.is_set():
                    self.check_stop()
                    self._pump(0.5)
                end += time.time() - t0
                self.app.run_state = prev
            left = end - time.time()
            if left <= 0:
                break
            if show_next:
                self.app.next_at = end
            self._pump(min(0.5, left))
        self.app.next_at = None

    def wait_if_paused(self):
        if self.app.paused.is_set():
            prev = self.app.run_state
            self.app.run_state = "paused"
            self.app.log("Paused. Press Resume to continue.")
            while self.app.paused.is_set():
                self.check_stop()
                self._pump(0.5)
            self.app.run_state = prev if prev != "paused" else "running"
            self.app.log("Resumed.")

    # ---------------- browser ----------------
    def _launch(self):
        from playwright.sync_api import sync_playwright
        self._close(quiet=True)
        if self.pw is None:
            self.pw = sync_playwright().start()
        os.makedirs(PROFILE_DIR, exist_ok=True)
        self.app.wa_state = "starting"
        opts = dict(headless=False, no_viewport=True, locale="en-US",
                    args=["--disable-blink-features=AutomationControlled", "--window-size=1250,900"],
                    ignore_default_args=["--enable-automation"])
        errors = []
        ctx = None
        for channel in (None, "chrome"):
            try:
                if channel:
                    ctx = self.pw.chromium.launch_persistent_context(PROFILE_DIR, channel=channel, **opts)
                else:
                    ctx = self.pw.chromium.launch_persistent_context(PROFILE_DIR, **opts)
                break
            except Exception as e:
                errors.append("%s: %s" % (channel or "chromium", str(e).splitlines()[0]))
        if ctx is None:
            self.app.wa_state = "error"
            raise RuntimeError("Couldn't start the browser (%s). Run ./setup.sh again. If another "
                               "copy of this app is open, close it first." % " | ".join(errors))
        self.ctx = ctx
        self.ctx_dead = False

        def _dead(*_a):
            self.ctx_dead = True
            self.app.wa_state = "closed"
        ctx.on("close", _dead)
        self.page = ctx.pages[0] if ctx.pages else ctx.new_page()
        for extra in ctx.pages[1:]:
            try:
                extra.close()
            except Exception:
                pass
        self.page.on("close", _dead)
        self.page.set_default_timeout(30000)

    def _close(self, quiet=False):
        try:
            if self.ctx is not None:
                self.ctx.close()
        except Exception:
            pass
        self.ctx, self.page, self.ctx_dead = None, None, True
        if not quiet:
            try:
                if self.pw is not None:
                    self.pw.stop()
            except Exception:
                pass
            self.pw = None

    def _alive(self):
        try:
            return self.ctx is not None and not self.ctx_dead and self.page is not None and not self.page.is_closed()
        except Exception:
            return False

    def ensure_ready(self):
        if not self._alive():
            self._launch()
        if not self.page.url.startswith(WA_BASE):
            self.page.goto(WA_BASE, wait_until="domcontentloaded", timeout=90000)
        self.wait_logged_in()

    def screen(self):
        try:
            return self.page.evaluate(JS_SCREEN)
        except Exception:
            return "loading"

    def wait_logged_in(self, timeout=900):
        end = time.time() + timeout
        told = False
        if self.app.wa_state != "ready":
            self.app.wa_state = "loading"
        while True:
            self.check_stop()
            st = self.screen()
            if st == "ready":
                if self.app.wa_state != "ready":
                    self.app.log("WhatsApp Web is connected.", "success")
                self.app.wa_state = "ready"
                return
            if st == "qr":
                self.app.wa_state = "qr"
                if not told:
                    self.app.log("Scan the QR code in the WhatsApp window: on the phone open WhatsApp → "
                                 "Settings → Linked devices → Link a device.", "alert")
                    told = True
            if time.time() > end:
                raise RuntimeError("WhatsApp Web didn't log in / finish loading in time.")
            self._pump(1.0)

    # ---------------- one message ----------------
    def open_chat(self, phone):
        self.page.goto("%s/send?phone=%s" % (WA_BASE, phone), wait_until="domcontentloaded", timeout=90000)
        end = time.time() + 60
        while time.time() < end:
            self.check_stop()
            st = self.screen()
            if st == "qr":
                self.app.wa_state = "qr"
                self.app.log("WhatsApp logged out - scan the QR code again. Waiting…", "alert")
                self.wait_logged_in()
                end = time.time() + 60
                continue
            if self.page.evaluate(JS_TAG_COMPOSE):
                return "ok"
            if self.page.evaluate(JS_INVALID):
                return "no_whatsapp"
            self._pump(0.5)
        return "timeout"

    def type_into(self, sel, text):
        loc = self.page.locator(sel).first
        loc.click()
        self.nap(0.2, 0.4)
        kb = self.page.keyboard
        for attempt in (1, 2):
            kb.press("Control+A")
            kb.press("Delete")
            lines = text.split("\n")
            for i, line in enumerate(lines):
                if line:
                    if attempt == 1:
                        kb.insert_text(line)
                    else:
                        kb.type(line, delay=10)
                if i < len(lines) - 1:
                    kb.press("Shift+Enter")
                self._pump(random.uniform(0.03, 0.12))
            self.nap(0.3, 0.6)
            got = loc.inner_text()
            if _norm_text(got) == _norm_text(text):
                return
            self.app.log("Text didn't land cleanly in the box (try %d) - retyping." % attempt, "warn")
        raise SendError("the message text didn't type correctly into WhatsApp")

    def _gone(self, sel, timeout):
        end = time.time() + timeout
        while time.time() < end:
            loc = self.page.locator(sel)
            try:
                if loc.count() == 0 or not loc.first.is_visible():
                    return True
            except Exception:
                return True
            self._pump(0.3)
        return False

    def _confirm(self, before):
        """After Enter: wait for the new bubble and for the clock icon to clear. Never raises."""
        try:
            end = time.time() + 20
            seen = False
            while time.time() < end:
                if self.page.evaluate(JS_COUNT_OUT) > before:
                    seen = True
                    break
                self._pump(0.4)
            if not seen:
                return "sent (bubble not confirmed)"
            end = time.time() + 120
            while time.time() < end:
                if self.page.evaluate(JS_PENDING) == 0:
                    return "delivered to WhatsApp server"
                self._pump(0.5)
            return "sent (still uploading when moved on)"
        except Exception as e:
            return "sent (check failed: %s)" % str(e)[:60]

    def attach_photo(self, image_path):
        page = self.page
        opened = False
        if page.evaluate(JS_TAG_ATTACH):
            page.locator('[data-wbs="attach"]').first.click()
            self.nap(0.6, 1.0)
            if page.evaluate(JS_TAG_PHOTO_INPUT):
                page.locator('[data-wbs="photo"]').first.set_input_files(image_path)
                opened = self._wait_media_editor(15)
            if not opened:
                page.keyboard.press("Escape")
                self.nap(0.4)
        if not opened:   # fallback: paste the image into the chat box
            import base64
            with open(image_path, "rb") as f:
                b64 = base64.b64encode(f.read()).decode("ascii")
            mime = mimetypes.guess_type(image_path)[0] or "image/jpeg"
            page.evaluate(JS_TAG_COMPOSE)
            page.evaluate(JS_PASTE_FILE, [b64, os.path.basename(image_path), mime])
            opened = self._wait_media_editor(15)
        if not opened:
            raise SendError("couldn't attach the photo (WhatsApp's layout may have changed)")

    def _wait_media_editor(self, timeout):
        end = time.time() + timeout
        while time.time() < end:
            if self.page.evaluate(JS_TAG_CAPTION) or self.page.evaluate(JS_TAG_MEDIA_SEND):
                self.nap(0.5)
                self.page.evaluate(JS_TAG_CAPTION)
                return True
            self._pump(0.4)
        return False

    def _send_photo(self, image_path, caption):
        """Attach the photo, optionally with caption, and send. Returns (caption_used, detail)."""
        page = self.page
        before = page.evaluate(JS_COUNT_OUT)
        self.attach_photo(image_path)
        self.nap(0.8, 1.5)
        has_caption_box = page.locator('[data-wbs="caption"]').count() > 0
        used = False
        if caption and has_caption_box:
            self.type_into('[data-wbs="caption"]', caption)
            used = True
            self.nap(0.5, 1.0)
        if has_caption_box:
            page.locator('[data-wbs="caption"]').first.press("Enter")
        else:
            page.evaluate(JS_TAG_MEDIA_SEND)
            page.locator('[data-wbs="msend"]').first.click()
        if not self._gone('[data-wbs="caption"]', 6) or not self._preview_closed(4):
            if page.evaluate(JS_TAG_MEDIA_SEND):
                page.locator('[data-wbs="msend"]').first.click()
            if not self._gone('[data-wbs="caption"]', 10) or not self._preview_closed(6):
                page.keyboard.press("Escape")
                raise SendError("photo preview didn't send")
        return used, self._confirm(before)

    def _preview_closed(self, timeout):
        end = time.time() + timeout
        while time.time() < end:
            if not self.page.evaluate(JS_TAG_MEDIA_SEND):
                return True
            self._pump(0.3)
        return False

    def _send_text(self, text):
        page = self.page
        if not page.evaluate(JS_TAG_COMPOSE):
            raise SendError("message box not found")
        before = page.evaluate(JS_COUNT_OUT)
        self.type_into('[data-wbs="compose"]', text)
        self.nap(0.4, 0.9)
        page.locator('[data-wbs="compose"]').first.press("Enter")
        end = time.time() + 8
        while time.time() < end:
            page.evaluate(JS_TAG_COMPOSE)
            if _norm_text(page.locator('[data-wbs="compose"]').first.inner_text()) == "":
                return self._confirm(before)
            self._pump(0.3)
        page.locator('[data-wbs="compose"]').first.press("Enter")
        self._pump(2)
        page.evaluate(JS_TAG_COMPOSE)
        if _norm_text(page.locator('[data-wbs="compose"]').first.inner_text()) == "":
            return self._confirm(before)
        page.keyboard.press("Control+A")
        page.keyboard.press("Delete")
        raise SendError("WhatsApp didn't accept the message")

    def send_to(self, phone, message, image, mode):
        """Returns (status, detail).  status: SENT | NO_WHATSAPP.  Raises on errors."""
        st = self.open_chat(phone)
        if st == "no_whatsapp":
            return "NO_WHATSAPP", "number is not on WhatsApp"
        if st != "ok":
            raise SendError("chat didn't open (slow internet?)")
        self.nap(1.0, 2.2)
        if mode == "text" or not image:
            return "SENT", self._send_text(message)
        if mode == "caption":
            used, detail = self._send_photo(image, message)
            if not used:
                self.app.log("No caption box found - sent the text as a separate message.", "warn")
                self.nap(1.0, 2.0)
                detail = self._send_text(message)
            return "SENT", detail
        # photo, then text
        _u, _d = self._send_photo(image, None)
        self.nap(1.2, 2.5)
        return "SENT", self._send_text(message)

    def send_with_retry(self, phone, message, image, mode):
        last = ""
        for attempt in (1, 2):
            self.check_stop()
            try:
                if not self._alive():
                    self.ensure_ready()
                return self.send_to(phone, message, image, mode)
            except StopRequested:
                raise
            except Exception as e:
                last = str(e).splitlines()[0][:160]
                self._trace()
                if attempt == 1:
                    self.app.log("Hiccup (%s) - retrying once." % last, "warn")
                    try:
                        if self._alive():
                            self.page.keyboard.press("Escape")
                            self.page.goto(WA_BASE, wait_until="domcontentloaded", timeout=90000)
                        self.ensure_ready()
                    except StopRequested:
                        raise
                    except Exception:
                        self._trace()
                    self.sleep(5, show_next=False)
        return "FAILED", last

    # ---------------- jobs ----------------
    def do_test(self, job):
        app = self.app
        app.run_state = "testing"
        self.ensure_ready()
        app.log("Test: sending to %s …" % pretty_phone(job["phone"]))
        app.current = dict(row="test", name=job["name"], phone=pretty_phone(job["phone"]))
        t0 = time.time()
        status, detail = self.send_with_retry(job["phone"], job["message"], job["image"], job["mode"])
        took = time.time() - t0
        if status == "SENT":
            self.ema_send = 0.5 * self.ema_send + 0.5 * took
            app.log("Test sent to %s in %.0fs (%s). Check that phone - if it looks right, start the bulk run."
                    % (pretty_phone(job["phone"]), took, detail), "success")
        elif status == "NO_WHATSAPP":
            app.log("Test: %s is not on WhatsApp." % pretty_phone(job["phone"]), "alert")
        else:
            app.log("Test failed: %s" % detail, "error")

    def wait_for_allowed_time(self):
        while True:
            self.check_stop()
            pace = self.app.pace()
            now = dt.datetime.now()
            if pace.daily_cap and self.app.log_store.sent_on(now.date()) >= pace.daily_cap:
                until = pace.next_start(now, next_day=True)
                why = "Daily limit of %d reached" % pace.daily_cap
            elif not pace.in_window(now):
                until = pace.next_start(now)
                why = "Outside sending hours"
            else:
                return
            self.app.run_state = "waiting"
            self.app.wait_reason = "%s - continues %s" % (why, fmt_when(until))
            self.app.log(self.app.wait_reason + ". Keep this app and the computer on.", "alert")
            while dt.datetime.now() < until:
                self.check_stop()
                self.app.next_at = time.mktime(until.timetuple())
                self._pump(min(5.0, max(0.5, (until - dt.datetime.now()).total_seconds())))
                np = self.app.pace()   # settings may change while waiting
                if (np.daily_cap != pace.daily_cap or np.hours_on != pace.hours_on
                        or np.h_from != pace.h_from or np.h_to != pace.h_to):
                    break
            self.app.wait_reason = ""
            self.app.next_at = None
            self.app.run_state = "running"

    def do_bulk(self, job):
        app = self.app
        contacts = job["contacts"]
        app.begin_run(job)
        log = app.log_store
        todo = []
        seen = set()
        for c in contacts:
            if not c.phone:
                if log.last.get("row%s" % c.row) != "INVALID_NUMBER":
                    log.add(c.row, "", c.name, "INVALID_NUMBER", "can't read phone: %s" % c.phone_raw)
                app.set_row(c.row, "INVALID_NUMBER")
                continue
            if c.phone in seen:
                app.set_row(c.row, "DUPLICATE")
                continue
            seen.add(c.phone)
            if job["resume"] and log.last.get(c.phone) in FINAL_STATUSES:
                continue
            todo.append(c)
        app.log("Bulk run: rows %d–%d → %d to send%s." % (
            job["start"], job["end"], len(todo),
            " (skipping %d already done)" % (len(contacts) - len(todo)) if job["resume"] else ""))
        if not todo:
            app.log("Nothing left to send in this range.", "success")
            app.finish_run("done")
            return
        app.run_state = "starting"
        self.ensure_ready()
        app.run_state = "running"
        pace = app.pace()
        self.since_break = 0
        self.next_break = random.randint(pace.every_min, pace.every_max)
        fails = nowa = 0
        for i, c in enumerate(todo):
            self.wait_if_paused()
            self.wait_for_allowed_time()
            self.check_stop()
            msg = build_message(job["template"], c.name)
            app.current = dict(row=c.row, name=greeting_name(c.name), phone=pretty_phone(c.phone))
            app.run_state = "running"
            t0 = time.time()
            status, detail = self.send_with_retry(c.phone, msg, job["image"], job["mode"])
            took = time.time() - t0
            log.add(c.row, c.phone, c.name, status, detail)
            app.set_row(c.row, status)
            left = app.remaining_count()
            if status == "SENT":
                fails = nowa = 0
                self.ema_send = 0.7 * self.ema_send + 0.3 * took
                app.session_sent += 1
                app.log("✓ Row %d · %s · %s  (%.0fs)" % (c.row, greeting_name(c.name), pretty_phone(c.phone), took), "ok")
            elif status == "NO_WHATSAPP":
                nowa += 1
                fails = 0
                app.log("✗ Row %d · %s · %s - not on WhatsApp" % (c.row, greeting_name(c.name), pretty_phone(c.phone)), "warn")
            else:
                fails += 1
                app.log("✗ Row %d · %s - failed: %s" % (c.row, pretty_phone(c.phone), detail), "error")
            app.current = None
            if fails >= 4:
                app.paused.set()
                app.log("4 failures in a row, so I've paused. Look at the WhatsApp window (internet? logged out? "
                        "a popup?), fix it, then press Resume.", "alert")
                fails = 0
            if nowa >= 12:
                app.paused.set()
                app.log("12 numbers in a row came back 'not on WhatsApp', which is unusual. Paused - check the "
                        "WhatsApp window, then press Resume.", "alert")
                nowa = 0
            if i == len(todo) - 1 or left == 0:
                break
            pace = app.pace()
            if status == "SENT":
                self.since_break += 1
            if self.since_break >= self.next_break:
                mins = random.uniform(pace.brk_min, pace.brk_max)
                app.run_state = "break"
                app.log("Anti-spam break: %.1f min after %d messages." % (mins, self.since_break))
                self.sleep(mins * 60)
                self.since_break = 0
                self.next_break = random.randint(pace.every_min, pace.every_max)
                app.run_state = "running"
            else:
                gap = random.uniform(pace.gap_min, pace.gap_max) if status == "SENT" else random.uniform(4, 8)
                self.sleep(gap)
        app.finish_run("done")


# ----------------------------------------------------------------------------
# App state shared by the web panel and the engine
# ----------------------------------------------------------------------------
class App(object):
    def __init__(self, folder_override=None):
        self.lock = threading.RLock()
        self.settings = dict(DEFAULT_SETTINGS)
        self.settings.update(self._load_settings())
        if folder_override:
            self.settings["folder"] = folder_override
        if not os.path.isdir(self.settings["folder"]):
            self.settings["folder"] = DEFAULT_FOLDER if os.path.isdir(DEFAULT_FOLDER) else APP_DIR
        self.logs = []
        self.log_seq = 0
        self.contacts = []
        self.sheet_info = {}
        self.sheet_error = ""
        self.log_store = SendLog(None)
        self.files = dict(sheets=[], images=[])
        self.wa_state = "closed"
        self.run_state = "idle"
        self.wait_reason = ""
        self.current = None
        self.next_at = None
        self.run_status = {}
        self.run_range = None
        self.session_sent = 0
        self.last_result = ""
        self.stop_flag = threading.Event()
        self.paused = threading.Event()
        self.engine = Engine(self)
        self.engine.start()
        self.scan_folder()

    # ---------------- settings ----------------
    def _load_settings(self):
        try:
            with open(SETTINGS_FILE, encoding="utf-8") as f:
                data = json.load(f)
            return {k: v for k, v in data.items() if k in DEFAULT_SETTINGS}
        except Exception:
            return {}

    def save_settings(self):
        try:
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(self.settings, f, ensure_ascii=False, indent=1)
        except Exception as e:
            self.log("Couldn't save settings: %s" % e, "warn")

    def update_settings(self, patch):
        reload_sheet = rescan = False
        with self.lock:
            for k, v in patch.items():
                if k not in DEFAULT_SETTINGS:
                    continue
                if k in INT_KEYS:
                    try:
                        v = int(float(v or 0))
                    except Exception:
                        continue
                elif k in FLOAT_KEYS:
                    try:
                        v = float(v)
                    except Exception:
                        continue
                elif k in BOOL_KEYS:
                    v = bool(v)
                else:
                    v = "" if v is None else str(v)
                if k == "preset" and v in PACE_PRESETS:
                    self.settings.update(PACE_PRESETS[v])
                if k in PACE_KEYS and patch.get("preset") is None:
                    self.settings["preset"] = "custom"
                if k == "folder":
                    v = os.path.expanduser(v.strip())
                    rescan = True
                if k in ("sheet", "phone_col", "name_col", "preeti"):
                    reload_sheet = True
                self.settings[k] = v
            self.save_settings()
        if rescan:
            self.scan_folder()
        elif reload_sheet:
            self.load_sheet()

    def pace(self):
        with self.lock:
            return Pace(self.settings)

    # ---------------- files ----------------
    def scan_folder(self):
        folder = self.settings["folder"]
        sheets, images = [], []
        if os.path.isdir(folder):
            for fn in sorted(os.listdir(folder)):
                low = fn.lower()
                if fn.startswith((".", "~", ".~lock")) or low.endswith(("_whatsapp_log.csv", "_not_sent.csv")):
                    continue
                if low.endswith(SHEET_EXT):
                    sheets.append(fn)
                elif low.endswith(IMAGE_EXT):
                    images.append(fn)
        self.files = dict(sheets=sheets, images=images)
        s = self.settings
        if s["sheet"] not in sheets:
            pref = [f for f in sheets if f.lower().endswith(".ods")] or sheets
            s["sheet"] = pref[0] if pref else ""
        if s["image"] not in images:
            if images:
                images_by_time = sorted(images, key=lambda f: os.path.getmtime(os.path.join(folder, f)), reverse=True)
                s["image"] = images_by_time[0]
            else:
                s["image"] = ""
        self.save_settings()
        self.load_sheet()

    def sheet_path(self):
        return os.path.join(self.settings["folder"], self.settings["sheet"]) if self.settings["sheet"] else ""

    def image_path(self):
        return os.path.join(self.settings["folder"], self.settings["image"]) if self.settings["image"] else ""

    def log_path(self):
        p = self.sheet_path()
        return os.path.splitext(p)[0] + "_whatsapp_log.csv" if p else ""

    def not_sent_path(self):
        p = self.sheet_path()
        return os.path.splitext(p)[0] + "_not_sent.csv" if p else ""

    def load_sheet(self):
        path = self.sheet_path()
        self.contacts, self.sheet_info, self.sheet_error = [], {}, ""
        self.run_status = {}
        if not path:
            self.sheet_error = "No spreadsheet (.ods / .xlsx / .csv) found in this folder."
            self.log_store = SendLog(None)
            return
        try:
            s = self.settings
            phones, names = read_columns(path, int(s["phone_col"]), int(s["name_col"]))
            if s.get("_preeti_sheet") != s["sheet"]:      # new sheet: detect the font once
                s["preeti"] = looks_like_preeti(names)
                s["_preeti_sheet"] = s["sheet"]
                self.save_settings()
            contacts, info = make_contacts(phones, names, bool(s["preeti"]))
            self.contacts, self.sheet_info = contacts, info
            self.log_store = SendLog(self.log_path())
            self.log("Loaded %s: %d contacts (last row %d)%s." % (
                os.path.basename(path), info["rows"], info["last_row"],
                ", names converted from Preeti" if info["preeti_used"] else ""))
        except Exception as e:
            self.sheet_error = "Couldn't read the spreadsheet: %s" % e
            self.log(self.sheet_error, "error")

    # ---------------- logging ----------------
    def log(self, text, level="info"):
        with self.lock:
            self.log_seq += 1
            self.logs.append(dict(id=self.log_seq, t=dt.datetime.now().strftime("%H:%M:%S"), level=level, text=text))
            if len(self.logs) > 1500:
                self.logs = self.logs[-1000:]
        try:
            print("[%s] %s" % (dt.datetime.now().strftime("%H:%M:%S"), text), flush=True)
        except Exception:
            pass

    # ---------------- run bookkeeping ----------------
    def range_bounds(self):
        last = self.sheet_info.get("last_row", 0)
        start = max(1, int(self.settings["start_row"] or 1))
        end = int(self.settings["end_row"] or 0)
        end = last if end <= 0 or end > last else end
        return start, end

    def contacts_in_range(self):
        start, end = self.range_bounds()
        return [c for c in self.contacts if start <= c.row <= end]

    def begin_run(self, job):
        with self.lock:
            self.run_status = {}
            self.run_range = (job["start"], job["end"], job["resume"])
            self.session_sent = 0

    def set_row(self, row, status):
        with self.lock:
            self.run_status[row] = status

    def finish_run(self, how):
        self.run_state = "done" if how == "done" else ("stopped" if how == "stopped" else "error")
        self.current = None
        self.next_at = None
        st = self.stats()
        path = self.export_not_sent()
        self.log("Run %s. Sent %d · not on WhatsApp %d · invalid %d · failed %d · remaining %d.%s" % (
            "finished" if how == "done" else how, st["sent"], st["no_wa"], st["invalid"], st["failed"],
            st["remaining"], (" Not-sent list: %s" % path) if path else ""),
            "success" if how == "done" else "alert")

    def stats(self):
        with self.lock:
            rows = self.contacts_in_range()
            resume = bool(self.settings["resume"])
            last = self.log_store.last
            c = dict(total=len(rows), sent=0, no_wa=0, invalid=0, failed=0, dup=0)
            seen = set()
            for x in rows:
                st = self.run_status.get(x.row)
                if st is None:
                    if not x.phone:
                        st = "INVALID_NUMBER"
                    elif x.phone in seen:
                        st = "DUPLICATE"
                    elif resume and last.get(x.phone) in FINAL_STATUSES:
                        st = last.get(x.phone)
                if x.phone:
                    seen.add(x.phone)
                if st == "SENT":
                    c["sent"] += 1
                elif st == "NO_WHATSAPP":
                    c["no_wa"] += 1
                elif st == "INVALID_NUMBER":
                    c["invalid"] += 1
                elif st == "FAILED":
                    c["failed"] += 1
                elif st == "DUPLICATE":
                    c["dup"] += 1
            c["not_sent"] = c["no_wa"] + c["invalid"] + c["failed"]
            c["remaining"] = c["total"] - c["sent"] - c["not_sent"] - c["dup"]
            return c

    def remaining_count(self):
        return self.stats()["remaining"]

    def export_not_sent(self):
        path = self.not_sent_path()
        if not path:
            return ""
        last = self.log_store.last
        rows = []
        for c in self.contacts_in_range():
            st = self.run_status.get(c.row) or (last.get(c.phone) if c.phone else "INVALID_NUMBER")
            if st in ("NO_WHATSAPP", "INVALID_NUMBER", "FAILED"):
                rows.append([c.row, c.phone_raw, c.name, st])
        try:
            with open(path, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(["row", "phone", "name", "status"])
                w.writerows(rows)
            return path
        except Exception as e:
            self.log("Couldn't write not-sent list: %s" % e, "warn")
            return ""

    # ---------------- ETA ----------------
    def eta(self, remaining):
        pace = self.pace()
        eng = self.engine
        send_s = eng.ema_send
        now = dt.datetime.now()
        start = now
        if self.next_at and self.run_state in ("running", "break", "waiting"):
            start = max(now, dt.datetime.fromtimestamp(self.next_at))
        running = self.run_state in ("running", "break", "waiting", "paused", "starting")
        if self.current is not None and remaining > 0:
            start = now   # mid-send
        nb = (eng.next_break if running else None)
        sb = (eng.since_break if running else 0)
        finish = simulate_finish(remaining, pace, send_s, start, self.log_store.sent_on(now.date()), sb, nb)
        return finish, pace.per_hour(send_s)

    # ---------------- snapshot for the panel ----------------
    def state(self, since=0):
        st = self.stats()
        start, end = self.range_bounds()
        finish, per_hour = self.eta(st["remaining"])
        with self.lock:
            logs = [l for l in self.logs if l["id"] > since]
        pace = self.pace()
        eng = self.engine
        info = dict(self.sheet_info)
        return dict(
            ok=True, settings=self.settings, files=self.files, sheet=info, sheet_error=self.sheet_error,
            presets=PACE_PRESETS, wa=self.wa_state, run=self.run_state, paused=self.paused.is_set(),
            busy=eng.busy, wait_reason=self.wait_reason, range=[start, end], stats=st,
            current=self.current, next_at=self.next_at, now=time.time(),
            eta=fmt_when(finish) if st["remaining"] else "",
            eta_in=fmt_dur((finish - dt.datetime.now()).total_seconds()) if st["remaining"] else "",
            per_hour=round(per_hour), send_s=round(eng.ema_send),
            sent_today=self.log_store.sent_on(dt.date.today()), daily_cap=pace.daily_cap,
            session_sent=self.session_sent, logs=logs, log_seq=self.log_seq,
            log_file=self.log_path(), not_sent_file=self.not_sent_path(),
            image_ok=bool(self.image_path() and os.path.exists(self.image_path())),
        )

    # ---------------- actions ----------------
    def start_bulk(self):
        if self.engine.busy:
            return "Already busy - stop the current job first."
        if not self.contacts:
            return self.sheet_error or "Load a spreadsheet first."
        s = self.settings
        if s["mode"] != "text" and not (self.image_path() and os.path.exists(self.image_path())):
            return "Choose the photo first (or switch 'Send as' to Message only)."
        if not s["template"].strip():
            return "The message is empty."
        start, end = self.range_bounds()
        if start > end:
            return "Start row %d is after the end row %d." % (start, end)
        self.stop_flag.clear()
        self.paused.clear()
        self.run_state = "starting"
        job = dict(contacts=self.contacts_in_range(), template=s["template"], image=self.image_path(),
                   mode=s["mode"], resume=bool(s["resume"]), start=start, end=end)
        self.engine.cmds.put(("bulk", job))
        return ""

    def start_test(self, phone_raw, name):
        if self.engine.busy:
            return "Busy - wait for the current job or press Stop."
        phone = normalize_phone(phone_raw)
        if not phone:
            return "That phone number doesn't look right. Use 10 digits like 98XXXXXXXX (or +countrycode…)."
        s = self.settings
        if s["mode"] != "text" and not (self.image_path() and os.path.exists(self.image_path())):
            return "Choose the photo first (or switch 'Send as' to Message only)."
        self.update_settings(dict(test_phone=phone_raw, test_name=name))
        self.stop_flag.clear()
        self.run_state = "testing"
        self.engine.cmds.put(("test", dict(phone=phone, name=name, image=self.image_path(), mode=s["mode"],
                                           message=build_message(s["template"], name))))
        return ""

    def open_whatsapp(self):
        if self.engine.busy:
            return "Busy right now."
        self.engine.cmds.put(("login", None))
        return ""

    def preview(self, row=None, name=None, phone=None):
        s = self.settings
        if row is not None:
            c = next((x for x in self.contacts if x.row == row), None)
            if c is None:
                return dict(ok=False, error="Row %s not found in the sheet." % row)
            return dict(ok=True, row=row, message=build_message(s["template"], c.name), name=c.name,
                        name_raw=c.name_raw, phone=pretty_phone(c.phone) or "(invalid: %s)" % c.phone_raw,
                        mode=s["mode"], image=self.settings["image"])
        p = normalize_phone(phone or "")
        return dict(ok=True, row=None, message=build_message(s["template"], name or ""), name=name or "",
                    name_raw="", phone=pretty_phone(p) if p else "", mode=s["mode"], image=self.settings["image"])

    def names(self):
        out = []
        last = self.log_store.last
        for c in self.contacts_in_range():
            odd = bool(re.search(r"[A-Za-z]|ुा|ाु|्\s|्$", c.name)) or not c.name
            out.append(dict(row=c.row, phone=c.phone_raw, raw=c.name_raw, name=greeting_name(c.name),
                            status=self.run_status.get(c.row) or (last.get(c.phone, "") if c.phone else "INVALID_NUMBER"),
                            odd=odd))
        return out


# ----------------------------------------------------------------------------
# Web control panel
# ----------------------------------------------------------------------------
PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>WhatsApp Campaign Sender</title>
<style>
:root{--bg:#f3f5f9;--card:#fff;--text:#1b2232;--muted:#5f6b7f;--line:#e2e7ef;--blue:#1d4fa3;--blue-soft:#e8effb;
--red:#c8202b;--red-soft:#fdeced;--green:#18834a;--green-soft:#e6f5ec;--amber:#a86a0c;--amber-soft:#fdf3e1;
--input:#fff;--bubble:#dcf8c6;--chat:#efe7dd;--shadow:0 1px 2px rgba(16,24,40,.06),0 1px 3px rgba(16,24,40,.08)}
@media (prefers-color-scheme:dark){:root{--bg:#0e131b;--card:#161d28;--text:#e5e9f1;--muted:#97a1b3;--line:#273142;
--blue:#7aa5f2;--blue-soft:#1b2a44;--red:#f0656d;--red-soft:#3a1d22;--green:#53c98a;--green-soft:#173326;
--amber:#e7b45a;--amber-soft:#3a2e17;--input:#10161f;--bubble:#1f4d3a;--chat:#0b141a;--shadow:none}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:14px/1.5 system-ui,-apple-system,"Segoe UI",Ubuntu,Roboto,"Noto Sans","Noto Sans Devanagari","Lohit Devanagari",sans-serif}
.deva{font-family:"Noto Sans Devanagari","Lohit Devanagari","Mukta","Kalimati",system-ui,sans-serif}
header{display:flex;flex-wrap:wrap;gap:12px;align-items:center;justify-content:space-between;padding:14px 22px;
background:var(--card);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:5}
h1{font-size:18px;margin:0;letter-spacing:-.01em}
.sub{color:var(--muted);font-size:13px}
.grid{display:grid;grid-template-columns:minmax(0,1.1fr) minmax(0,.9fr);gap:18px;padding:18px 22px;max-width:1400px;margin:0 auto}
@media (max-width:980px){.grid{grid-template-columns:minmax(0,1fr)}}
@media (max-width:560px){.grid{padding:12px 16px}header{padding:12px 16px}.card{padding:14px}}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:16px 18px;margin-bottom:16px;box-shadow:var(--shadow)}
.card h2{font-size:15px;margin:0 0 12px;display:flex;align-items:center;gap:8px}
.n{display:inline-grid;place-items:center;width:22px;height:22px;border-radius:50%;background:var(--blue);color:#fff;font-size:12px}
label{display:block;font-size:12px;color:var(--muted);margin:10px 0 4px;font-weight:600}
input,select,textarea{width:100%;padding:8px 10px;border:1px solid var(--line);border-radius:8px;background:var(--input);color:var(--text);font:inherit}
input[type=checkbox],input[type=radio]{width:auto;margin:0 6px 0 0;accent-color:var(--blue)}
textarea{min-height:250px;resize:vertical;line-height:1.6}
.row{display:flex;gap:8px;align-items:center}
.two{display:grid;grid-template-columns:1fr 1fr;gap:12px}
.three{display:grid;grid-template-columns:repeat(3,1fr);gap:12px}
@media (max-width:560px){.two,.three{grid-template-columns:1fr}}
.check{display:flex;align-items:center;margin:10px 0 0;font-size:13px;color:var(--text);font-weight:500}
.seg{display:flex;flex-wrap:wrap;gap:6px}
.seg label{margin:0;display:flex;align-items:center;border:1px solid var(--line);border-radius:8px;padding:7px 10px;cursor:pointer;color:var(--text);font-weight:500;font-size:13px}
.seg label:has(input:checked){border-color:var(--blue);background:var(--blue-soft)}
button{font:inherit;font-weight:600;border:1px solid var(--line);background:var(--card);color:var(--text);border-radius:8px;padding:8px 14px;cursor:pointer;white-space:nowrap}
button:hover:not(:disabled){border-color:var(--blue)}
button:disabled{opacity:.45;cursor:not-allowed}
button.primary{background:var(--blue);border-color:var(--blue);color:#fff}
button.go{background:var(--green);border-color:var(--green);color:#fff}
button.stop{color:var(--red)}
.note{color:var(--muted);font-size:12.5px;margin-top:6px}
.note.err{color:var(--red)}
.pill{display:inline-flex;align-items:center;gap:6px;padding:5px 11px;border-radius:999px;font-size:13px;font-weight:600;background:var(--blue-soft);color:var(--blue)}
.pill::before{content:"";width:8px;height:8px;border-radius:50%;background:currentColor}
.pill.ok{background:var(--green-soft);color:var(--green)}.pill.warn{background:var(--amber-soft);color:var(--amber)}.pill.bad{background:var(--red-soft);color:var(--red)}
.side .sticky{position:sticky;top:76px;max-height:calc(100vh - 90px);overflow:auto;padding-bottom:4px}
@media (max-width:980px){.side .sticky{position:static;max-height:none}}
.state{font-size:15px;font-weight:700;margin-bottom:10px}
.counters{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}
@media (max-width:560px){.counters{grid-template-columns:repeat(2,1fr)}}
.ctr{border-radius:10px;padding:10px 12px;background:var(--bg)}
.ctr b{display:block;font-size:26px;line-height:1.1;font-variant-numeric:tabular-nums}
.ctr span{font-size:12px;color:var(--muted);font-weight:600}
.ctr.sent b{color:var(--green)}.ctr.bad b{color:var(--red)}.ctr.left b{color:var(--amber)}
.bar{height:10px;background:var(--bg);border-radius:99px;overflow:hidden;margin:14px 0 6px;display:flex}
.bar i{display:block;height:100%}
.facts{display:grid;grid-template-columns:auto 1fr;gap:6px 14px;margin:14px 0;font-size:13.5px}
.facts dt{color:var(--muted)}.facts dd{margin:0;font-weight:600;font-variant-numeric:tabular-nums}
.eta{font-size:20px;font-weight:700;color:var(--blue)}
.btns{display:flex;gap:8px;flex-wrap:wrap}
.btns button{flex:1}
.log{height:300px;overflow:auto;font-size:12.5px;border:1px solid var(--line);border-radius:8px;padding:6px 8px;background:var(--bg)}
.log div{padding:2px 0;border-bottom:1px dashed var(--line)}
.log time{color:var(--muted);margin-right:6px;font-variant-numeric:tabular-nums}
.log .ok{color:var(--green)}.log .success{color:var(--green);font-weight:600}.log .warn{color:var(--amber)}
.log .error{color:var(--red)}.log .alert{color:var(--blue);font-weight:600}
.chat{background:var(--chat);border-radius:10px;padding:14px;margin-top:10px}
.bubble{background:var(--bubble);border-radius:8px;padding:6px;max-width:360px;margin-left:auto;box-shadow:0 1px .5px rgba(0,0,0,.13)}
.bubble img{display:block;width:100%;max-height:280px;object-fit:cover;object-position:top;border-radius:6px;margin-bottom:6px}
.bubble p{margin:0;padding:0 4px 4px;white-space:pre-wrap;font-size:14px;line-height:1.55}
.meta{font-size:12.5px;color:var(--muted);margin-top:8px}
table{width:100%;border-collapse:collapse;font-size:13px}
th,td{text-align:left;padding:5px 6px;border-bottom:1px solid var(--line);vertical-align:top}
th{color:var(--muted);font-size:12px;position:sticky;top:0;background:var(--card)}
tr.odd td{background:var(--amber-soft)}
.tablebox{max-height:420px;overflow:auto;margin-top:10px}
code{font-size:12px;background:var(--bg);padding:1px 5px;border-radius:4px;word-break:break-all}
#toast{position:fixed;left:50%;bottom:22px;transform:translateX(-50%);max-width:min(640px,92vw);display:none;
padding:11px 16px;border-radius:10px;background:var(--text);color:var(--card);font-weight:600;box-shadow:0 8px 24px rgba(0,0,0,.25);z-index:20}
.warnline{color:var(--amber);font-size:12.5px;margin-top:6px}
</style></head>
<body>
<header>
  <div><h1>WhatsApp Campaign Sender</h1>
  <div class="sub deva">बुटवल उद्योग वाणिज्य संघ · कोषाध्यक्ष पदका उम्मेदवार टिकाराम बन्जाडे</div></div>
  <div class="row"><span id="waPill" class="pill">WhatsApp: not open</span><button id="btnOpen">Open WhatsApp</button></div>
</header>
<div class="grid">
<section>
  <div class="card"><h2><span class="n">1</span>Contacts &amp; photo</h2>
    <label for="folder">Folder</label>
    <div class="row"><input id="folder" spellcheck="false"><button id="btnScan">Reload</button></div>
    <div class="two">
      <div><label for="sheet">Spreadsheet</label><select id="sheet"></select></div>
      <div><label for="image">Photo</label><select id="image"></select></div>
    </div>
    <div id="sheetInfo" class="note"></div>
    <div class="three">
      <div><label for="phone_col">Phone column</label><input id="phone_col" type="number" min="1"></div>
      <div><label for="name_col">Name column</label><input id="name_col" type="number" min="1"></div>
      <div><label>&nbsp;</label><label class="check"><input type="checkbox" id="preeti">Names are in Preeti font</label></div>
    </div>
    <label>Send as</label>
    <div class="seg">
      <label><input type="radio" name="mode" value="caption">Photo with message as caption (1 message)</label>
      <label><input type="radio" name="mode" value="photo_then_text">Photo, then message</label>
      <label><input type="radio" name="mode" value="text">Message only</label>
    </div>
  </div>

  <div class="card"><h2><span class="n">2</span>Message</h2>
    <textarea id="template" class="deva" spellcheck="false"></textarea>
    <div class="note"><b>(Name)</b> is replaced with each person's name. Nicknames in brackets are left out. Changes save automatically.</div>
    <div class="row" style="margin-top:12px"><span style="white-space:nowrap">Preview row</span><input id="pvRow" type="number" min="1" style="max-width:110px"><button id="btnPv">Show</button></div>
    <div class="chat"><div class="bubble"><img id="pvImg" alt="" hidden><p id="pvText" class="deva"></p></div></div>
    <div id="pvMeta" class="meta deva"></div>
  </div>

  <div class="card"><h2><span class="n">3</span>Test on one number first</h2>
    <div class="two">
      <div><label for="test_phone">Phone number</label><input id="test_phone" placeholder="98XXXXXXXX" inputmode="tel"></div>
      <div><label for="test_name">Name to use in the greeting</label><input id="test_name" class="deva"></div>
    </div>
    <div class="row" style="margin-top:12px"><button id="btnTest" class="primary">Send test message</button></div>
    <div class="note">Use your own or a family member's number. It goes through exactly the same steps as the real run, so if the photo and text arrive right, the bulk run will too.</div>
  </div>

  <div class="card"><h2><span class="n">4</span>Bulk run settings</h2>
    <div class="two">
      <div><label for="start_row">From row</label><input id="start_row" type="number" min="1"></div>
      <div><label for="end_row">To row (0 = last row)</label><input id="end_row" type="number" min="0"></div>
    </div>
    <div id="rangeInfo" class="note"></div>
    <label class="check"><input type="checkbox" id="resume">Skip numbers already done (resume where it stopped)</label>
    <label for="preset">Speed</label>
    <select id="preset">
      <option value="safe">Safe: slowest, lowest risk</option>
      <option value="balanced">Balanced (recommended)</option>
      <option value="fast">Fast: higher ban risk</option>
      <option value="custom">Custom</option>
    </select>
    <div class="three">
      <div><label for="gap_min">Wait between messages (sec): min</label><input id="gap_min" type="number" min="1" step="1"></div>
      <div><label for="gap_max">max</label><input id="gap_max" type="number" min="1" step="1"></div>
      <div><label for="daily_cap">Daily limit (0 = none)</label><input id="daily_cap" type="number" min="0"></div>
      <div><label for="every_min">Break after (messages): min</label><input id="every_min" type="number" min="1"></div>
      <div><label for="every_max">max</label><input id="every_max" type="number" min="1"></div>
      <div></div>
      <div><label for="brk_min">Break length (minutes): min</label><input id="brk_min" type="number" min="0" step="0.5"></div>
      <div><label for="brk_max">max</label><input id="brk_max" type="number" min="0" step="0.5"></div>
    </div>
    <label class="check"><input type="checkbox" id="hours_on">Only send between&nbsp;
      <input id="hours_from" type="time" style="width:auto">&nbsp;and&nbsp;<input id="hours_to" type="time" style="width:auto"></label>
    <div id="paceInfo" class="note"></div>
    <div id="paceWarn" class="warnline"></div>
  </div>

  <div class="card"><details id="namesBox"><summary><b>Check the converted names in the selected rows</b></summary>
    <div class="note">Highlighted rows look odd (usually a typo in the sheet). Fix those in LibreOffice, save, then press Reload.</div>
    <div id="names" class="tablebox"></div></details></div>
</section>

<section class="side">
  <div class="sticky">
  <div class="card"><h2>Progress</h2>
    <div id="runState" class="state">Idle</div>
    <div class="counters">
      <div class="ctr sent"><b id="cSent">0</b><span>Sent</span></div>
      <div class="ctr bad"><b id="cNot">0</b><span>Not sent</span></div>
      <div class="ctr left"><b id="cLeft">0</b><span>Remaining</span></div>
      <div class="ctr"><b id="cTotal">0</b><span>In range</span></div>
    </div>
    <div class="bar"><i id="barSent" style="background:var(--green)"></i><i id="barNot" style="background:var(--red)"></i></div>
    <div id="breakdown" class="note"></div>
    <dl class="facts">
      <dt>Now</dt><dd id="fNow" class="deva">-</dd>
      <dt>Next message</dt><dd id="fNext">-</dd>
      <dt>Estimated finish</dt><dd><span id="fEta" class="eta">-</span><div id="fEtaIn" class="note"></div></dd>
      <dt>Sent today</dt><dd id="fToday">0</dd>
    </dl>
    <div class="btns">
      <button id="btnStart" class="go">▶ Start bulk run</button>
      <button id="btnPause">Pause</button>
      <button id="btnStop" class="stop">■ Stop</button>
    </div>
    <div id="files" class="note"></div>
  </div>
  <div class="card"><h2>Activity</h2><div id="log" class="log deva"></div>
    <div class="row" style="margin-top:10px;justify-content:space-between">
      <button id="btnExport">Save not-sent list</button><button id="btnQuit" class="stop">Close app</button></div>
  </div>
  </div>
</section>
</div>
<div id="toast"></div>
<script>
const $ = id => document.getElementById(id);
let S = null, logSeq = 0, inited = false, listsKey = '', toastTimer = null, imgStamp = Date.now();
const FIELDS = ['folder','phone_col','name_col','template','start_row','end_row','gap_min','gap_max','every_min',
  'every_max','brk_min','brk_max','daily_cap','hours_from','hours_to','test_phone','test_name','preset'];
const CHECKS = ['preeti','resume','hours_on'];
const RUN_TEXT = {idle:'Idle - ready', starting:'Starting…', running:'Sending…', paused:'Paused', break:'Anti-spam break',
  waiting:'Waiting', testing:'Sending test message…', done:'Finished ✓', stopped:'Stopped', error:'Stopped because of an error'};
const WA_TEXT = {closed:['WhatsApp: not open',''], starting:['WhatsApp: starting…','warn'], loading:['WhatsApp: loading…','warn'],
  qr:['WhatsApp: scan the QR code','bad'], ready:['WhatsApp: connected','ok'], error:['WhatsApp: browser error','bad']};

function toast(msg, kind) {
  const t = $('toast'); t.textContent = msg; t.style.display = 'block';
  t.style.background = kind === 'error' ? 'var(--red)' : kind === 'success' ? 'var(--green)' : 'var(--text)';
  clearTimeout(toastTimer); toastTimer = setTimeout(() => t.style.display = 'none', kind === 'error' ? 9000 : 6000);
}
async function api(path, body) {
  try {
    const opt = body === undefined ? {} : {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify(body)};
    const j = await (await fetch(path, opt)).json();
    if (!j.ok && j.error) toast(j.error, 'error');
    return j;
  } catch (e) { toast('The app is not running (closed?). Start it again with run.sh', 'error'); return {ok:false}; }
}
function applySettings(s) {
  for (const k of FIELDS) { const el = $(k); if (el && document.activeElement !== el) el.value = s[k] ?? ''; }
  for (const k of CHECKS) { const el = $(k); if (el) el.checked = !!s[k]; }
  for (const r of document.querySelectorAll('input[name=mode]')) r.checked = (r.value === s.mode);
  if (!$('pvRow').value) $('pvRow').value = s.start_row || 1;
}
function fillSelects(j) {
  const key = JSON.stringify([j.files, j.settings.sheet, j.settings.image]);
  if (key === listsKey) return; listsKey = key;
  for (const [id, list, cur] of [['sheet', j.files.sheets, j.settings.sheet], ['image', j.files.images, j.settings.image]]) {
    const el = $(id); el.innerHTML = '';
    if (!list.length) { const o = document.createElement('option'); o.textContent = '(none in this folder)'; o.value = ''; el.appendChild(o); }
    for (const f of list) { const o = document.createElement('option'); o.value = o.textContent = f; o.selected = (f === cur); el.appendChild(o); }
  }
  imgStamp = Date.now();
}
async function save(patch, quiet) {
  const j = await api('/api/settings', patch);
  if (j.ok) { S = j; applySettings(j.settings); fillSelects(j); render(j); if (!quiet) preview(); }
}
const tmrs = {};
for (const k of FIELDS) {
  const el = $(k); if (!el) continue;
  if (k === 'template' || k === 'test_name' || k === 'test_phone') {
    const quiet = (k === 'test_phone');
    el.addEventListener('input', () => { clearTimeout(tmrs[k]); tmrs[k] = setTimeout(() => save({[k]: el.value}, quiet), 500); });
    el.addEventListener('change', () => { clearTimeout(tmrs[k]); save({[k]: el.value}, quiet); });
  } else el.addEventListener('change', () => save({[k]: el.value}));
}
for (const k of CHECKS) $(k).addEventListener('change', () => save({[k]: $(k).checked}));
for (const r of document.querySelectorAll('input[name=mode]')) r.addEventListener('change', () => save({mode: r.value}));
$('sheet').addEventListener('change', () => save({sheet: $('sheet').value}));
$('image').addEventListener('change', () => { imgStamp = Date.now(); save({image: $('image').value}); });
$('btnScan').onclick = async () => { const j = await api('/api/scan', {}); if (j.ok) { listsKey=''; S = j; fillSelects(j); render(j); preview(); toast('Folder reloaded'); } };
$('btnPv').onclick = () => preview();
$('pvRow').addEventListener('change', () => preview());

async function preview() {
  const row = parseInt($('pvRow').value || '0');
  const j = await api('/api/preview?row=' + row);
  if (!j.ok) return;
  $('pvText').textContent = j.message;
  const img = $('pvImg');
  if (j.mode !== 'text' && j.image) { img.src = '/photo?ts=' + imgStamp; img.hidden = false; } else img.hidden = true;
  $('pvMeta').textContent = 'Row ' + j.row + ' → ' + j.phone + (j.name_raw && j.name_raw !== j.name ? '   ·   sheet text "' + j.name_raw + '" → ' + j.name : '');
}
$('btnTest').onclick = async () => {
  const ph = $('test_phone').value.trim();
  if (!ph) { toast('Type a phone number for the test', 'error'); return; }
  const j = await api('/api/test', {phone: ph, name: $('test_name').value.trim()});
  if (j.ok) toast('Test started - watch the WhatsApp window');
};
$('btnOpen').onclick = async () => { const j = await api('/api/open', {}); if (j.ok) toast('Opening WhatsApp Web in a new window…'); };
$('btnStart').onclick = async () => {
  if (!S) return;
  const st = S.stats;
  if (!st.remaining) { toast('Nothing left to send in this range (all done). Untick "Skip numbers already done" to send again.', 'error'); return; }
  if (!confirm('Send to ' + st.remaining + ' people (rows ' + S.range[0] + '–' + S.range[1] + ')?\n\nEstimated finish: ' + (S.eta || '-') +
     '\n\nKeep this computer awake and online until then. You can pause or stop at any time.')) return;
  const j = await api('/api/start', {}); if (j.ok) toast('Bulk run started');
};
$('btnPause').onclick = async () => { if (!S) return; await api(S.paused ? '/api/resume' : '/api/pause', {}); refresh(); };
$('btnStop').onclick = async () => { if (confirm('Stop sending? Progress is saved; Start continues from where it stopped.')) await api('/api/stop', {}); };
$('btnExport').onclick = async () => { const j = await api('/api/export', {}); if (j.ok) toast('Saved: ' + j.path, 'success'); };
$('btnQuit').onclick = async () => {
  if (!confirm('Close the app and the WhatsApp window?')) return;
  await api('/api/quit', {}); document.body.innerHTML = '<div style="padding:40px;font-size:18px">The app is closed. You can close this tab.</div>';
};
$('namesBox').addEventListener('toggle', () => { if ($('namesBox').open) loadNames(); });
async function loadNames() {
  const j = await api('/api/names'); if (!j.ok) return;
  const esc = s => String(s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
  let h = '<table><tr><th>Row</th><th>Phone</th><th>In the sheet</th><th>Name used</th><th>Status</th></tr>';
  for (const r of j.rows) h += '<tr class="' + (r.odd ? 'odd' : '') + '"><td>' + r.row + '</td><td>' + esc(r.phone) + '</td><td><code>' +
     esc(r.raw) + '</code></td><td class="deva">' + esc(r.name) + '</td><td>' + esc(r.status || '') + '</td></tr>';
  $('names').innerHTML = h + '</table>';
}
function fmtClock(ts) { return new Date(ts * 1000).toLocaleTimeString([], {hour:'numeric', minute:'2-digit', second:'2-digit'}); }
function render(j) {
  const [wt, wc] = WA_TEXT[j.wa] || [j.wa, ''];
  $('waPill').textContent = wt; $('waPill').className = 'pill ' + wc;
  let rs = RUN_TEXT[j.run] || j.run;
  if (j.paused && j.run !== 'idle') rs = 'Paused';
  if (j.run === 'waiting' && j.wait_reason) rs = 'Waiting: ' + j.wait_reason;
  $('runState').textContent = rs;
  const st = j.stats;
  $('cSent').textContent = st.sent; $('cNot').textContent = st.not_sent; $('cLeft').textContent = st.remaining; $('cTotal').textContent = st.total;
  $('barSent').style.width = (st.total ? 100 * st.sent / st.total : 0) + '%';
  $('barNot').style.width = (st.total ? 100 * st.not_sent / st.total : 0) + '%';
  const parts = [];
  if (st.no_wa) parts.push(st.no_wa + ' not on WhatsApp'); if (st.invalid) parts.push(st.invalid + ' invalid number');
  if (st.failed) parts.push(st.failed + ' failed (retried next run)'); if (st.dup) parts.push(st.dup + ' duplicate number skipped');
  $('breakdown').textContent = parts.length ? 'Not sent: ' + parts.join(' · ') : '';
  $('fNow').textContent = j.current ? ('Row ' + j.current.row + ' · ' + j.current.name + ' · ' + j.current.phone) : '-';
  if (j.next_at && j.next_at > j.now) {
    $('fNext').textContent = fmtClock(j.next_at) + '  (in ' + Math.max(0, Math.round(j.next_at - j.now)) + 's)';
  } else $('fNext').textContent = j.current ? 'sending now' : '-';
  const running = ['starting','running','paused','break','waiting'].includes(j.run) || (j.busy && j.run !== 'testing' && j.run !== 'idle');
  $('fEta').textContent = st.remaining ? j.eta : (st.total ? 'All done' : '-');
  $('fEtaIn').textContent = st.remaining ? ((running ? 'in about ' : 'if started now: about ') + j.eta_in + ' · ≈' + j.per_hour + ' msgs/hour') : '';
  $('fToday').textContent = j.sent_today + (j.daily_cap ? ' / ' + j.daily_cap + ' daily limit' : '');
  $('btnStart').disabled = j.busy || running || !st.remaining;
  $('btnPause').disabled = !running; $('btnPause').textContent = j.paused ? 'Resume' : 'Pause';
  $('btnStop').disabled = !(running || j.run === 'testing');
  $('btnTest').disabled = j.busy; $('btnOpen').disabled = j.busy;
  const si = j.sheet || {};
  $('sheetInfo').className = 'note' + (j.sheet_error ? ' err' : '');
  $('sheetInfo').textContent = j.sheet_error ? j.sheet_error :
    (si.rows ? si.rows + ' contacts, rows 1–' + si.last_row + (si.preeti_used ? ' · names converted from Preeti to Unicode' : '') +
     (si.bad_phones ? ' · ' + si.bad_phones + ' unreadable phone numbers' : '') : '');
  $('rangeInfo').textContent = j.range && si.rows ? 'Rows ' + j.range[0] + '–' + j.range[1] + ': ' + st.total + ' contacts, ' + st.remaining + ' still to send' : '';
  $('paceInfo').textContent = 'At this pace: about ' + j.per_hour + ' messages per hour (one send takes ≈' + j.send_s + 's plus the wait and breaks).';
  const s = j.settings;
  $('paceWarn').textContent = (s.gap_min < 10 ? 'A wait under 10 seconds looks robotic to WhatsApp. ' : '') +
     (!s.daily_cap || s.daily_cap > 500 ? 'No daily limit or a very high one raises the ban risk, especially on a newer number.' : '');
  $('files').innerHTML = j.log_file ? 'Log: <code>' + j.log_file + '</code>' : '';
}
async function refresh() {
  let j;
  try { j = await (await fetch('/api/state?since=' + logSeq)).json(); } catch (e) { $('runState').textContent = 'App not running'; return; }
  S = j;
  if (!inited) { applySettings(j.settings); inited = true; }
  fillSelects(j); render(j);
  if (!$('pvText').textContent) preview();
  const box = $('log'), atBottom = box.scrollHeight - box.scrollTop - box.clientHeight < 40;
  for (const l of j.logs) {
    const d = document.createElement('div'); d.className = l.level;
    const t = document.createElement('time'); t.textContent = l.t; d.appendChild(t); d.appendChild(document.createTextNode(l.text));
    box.appendChild(d);
    if (['success','error','alert'].includes(l.level) && logSeq) toast(l.text, l.level);
  }
  while (box.childNodes.length > 600) box.removeChild(box.firstChild);
  if (j.logs.length && atBottom) box.scrollTop = box.scrollHeight;
  logSeq = j.log_seq;
}
refresh(); setInterval(refresh, 1000);
</script>
</body></html>
"""


class Handler(BaseHTTPRequestHandler):
    app = None  # set in main()

    def log_message(self, *a):
        pass

    def _json(self, obj, code=200):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _body(self):
        n = int(self.headers.get("Content-Length") or 0)
        if not n:
            return {}
        try:
            return json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception:
            return {}

    def do_GET(self):
        app = self.app
        u = urlparse(self.path)
        q = parse_qs(u.query)
        try:
            if u.path == "/":
                body = PAGE.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif u.path == "/api/state":
                self._json(app.state(int((q.get("since") or ["0"])[0] or 0)))
            elif u.path == "/api/preview":
                row = int((q.get("row") or ["0"])[0] or 0)
                self._json(app.preview(row=row if row else app.range_bounds()[0]))
            elif u.path == "/api/names":
                self._json(dict(ok=True, rows=app.names()))
            elif u.path == "/photo":
                p = app.image_path()
                if not p or not os.path.exists(p):
                    self.send_error(404)
                    return
                with open(p, "rb") as f:
                    data = f.read()
                self.send_response(200)
                self.send_header("Content-Type", mimetypes.guess_type(p)[0] or "image/jpeg")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)
            else:
                self.send_error(404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            self._json(dict(ok=False, error=str(e)), 500)

    def do_POST(self):
        app = self.app
        u = urlparse(self.path)
        b = self._body()
        try:
            err = ""
            if u.path == "/api/settings":
                locked = ("folder", "sheet", "phone_col", "name_col", "preeti", "image", "mode", "template",
                          "start_row", "end_row", "resume")
                if app.engine.busy and any(k in b for k in locked):
                    err = ("Stop the run first to change that (speed, limits and hours can be changed "
                           "while it runs).")
                else:
                    app.update_settings(b)
            elif u.path == "/api/scan":
                if app.engine.busy:
                    err = "Stop the current job before reloading."
                else:
                    app.scan_folder()
            elif u.path == "/api/open":
                err = app.open_whatsapp()
            elif u.path == "/api/test":
                err = app.start_test(b.get("phone", ""), b.get("name", ""))
            elif u.path == "/api/start":
                err = app.start_bulk()
            elif u.path == "/api/pause":
                app.paused.set()
                app.log("Pausing after the current message…")
            elif u.path == "/api/resume":
                app.paused.clear()
            elif u.path == "/api/stop":
                app.stop_flag.set()
                app.paused.clear()
                app.log("Stopping…")
            elif u.path == "/api/export":
                p = app.export_not_sent()
                self._json(dict(ok=bool(p), path=p, error="" if p else "Load a spreadsheet first."))
                return
            elif u.path == "/api/quit":
                self._json(dict(ok=True))
                threading.Thread(target=shutdown, args=(app,), daemon=True).start()
                return
            else:
                self.send_error(404)
                return
            if err:
                self._json(dict(ok=False, error=err))
            else:
                self._json(app.state(10 ** 9))
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            self._json(dict(ok=False, error=str(e)), 500)


SERVER = None


def shutdown(app):
    app.stop_flag.set()
    app.paused.clear()
    app.log("Closing…")
    app.engine.cmds.put(("quit", None))
    app.engine.join(timeout=15)
    if SERVER is not None:
        SERVER.shutdown()


def free_port(start):
    for p in range(start, start + 30):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)   # same as the real server
            try:
                s.bind(("127.0.0.1", p))
                return p
            except OSError:
                continue
    raise RuntimeError("No free port found")


def main():
    global SERVER
    ap = argparse.ArgumentParser(description="WhatsApp campaign sender")
    ap.add_argument("--folder", help="folder with the spreadsheet and photo (default: %s)" % DEFAULT_FOLDER)
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--no-browser", action="store_true", help="don't open the control panel automatically")
    args = ap.parse_args()
    if pd is None:
        print("pandas isn't installed. Run ./setup.sh first.")
        sys.exit(1)
    try:
        import playwright  # noqa: F401
    except ImportError:
        print("playwright isn't installed. Run ./setup.sh first.")
        sys.exit(1)
    # Already running?  Just reopen its control panel (two copies would fight over the login).
    try:
        import urllib.request
        old = "http://127.0.0.1:%d/" % args.port
        with urllib.request.urlopen(old + "api/state?since=999999999", timeout=1.5) as r:
            if json.loads(r.read().decode("utf-8")).get("ok"):
                print("The sender is already running - opening its control panel: %s" % old)
                if not args.no_browser:
                    webbrowser.open(old)
                return
    except Exception:
        pass
    app = App(args.folder)
    Handler.app = app
    port = free_port(args.port)
    SERVER = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    SERVER.daemon_threads = True
    url = "http://127.0.0.1:%d/" % port
    print("\n  Control panel:  %s\n  (keep this terminal open; press Ctrl+C to quit)\n" % url, flush=True)
    if not args.no_browser:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    try:
        SERVER.serve_forever()
    except KeyboardInterrupt:
        print("\nClosing…")
        shutdown(app)
    print("Bye.")


if __name__ == "__main__":
    main()
