"""Betfair starting prices from the files betfair_bsp.py downloads (data/betfair_bsp/win_<YYYY-MM>.csv.gz), keyed for joining to our runners.

A price is found by Melbourne race date and horse name (letters only, lower case). Commission as the owner set it on 10 Nov 2026:
10% on New South Wales racing, 8% elsewhere.
"""
import glob
import os
import re

import pandas as pd

DIR = os.path.join("data", "betfair_bsp")
COMM_NSW, COMM_OTHER = 0.10, 0.08


def norm(s):
    return re.sub(r"[^a-z]", "", str(s).lower())


def commission(state):
    return COMM_NSW if str(state).strip().upper() == "NSW" else COMM_OTHER


def load(months=None):
    """rows of the win files for the given months ('YYYY-MM'; None = all): date (Melbourne), hn, bsp, win_lose, event_id"""
    fs = sorted(glob.glob(os.path.join(DIR, "win_*.csv.gz")))
    if months is not None:
        want = set()
        for m in months:                       # an evening race can sit in the next UTC day's file, so read the neighbours too
            p = pd.Period(m, "M")
            want |= {str(p - 1), str(p), str(p + 1)}
        fs = [f for f in fs if os.path.basename(f)[4:11] in want]
    if not fs:
        return pd.DataFrame(columns=["date", "hn", "bsp", "win_lose", "event_id"])
    b = pd.concat([pd.read_csv(f).rename(columns=lambda c: c.strip().lower()) for f in fs], ignore_index=True)   # older files use upper-case headers
    b = b.drop_duplicates(["event_id", "selection_id"])
    t = pd.to_datetime(b.event_dt, format="%d-%m-%Y %H:%M", errors="coerce").dt.tz_localize("UTC")
    b["date"] = t.dt.tz_convert("Australia/Melbourne").dt.strftime("%Y-%m-%d")
    b["hn"] = b.selection_name.astype(str).str.replace(r"^\s*\d+\.\s*", "", regex=True).map(norm)
    for c in ("bsp", "win_lose"):
        b[c] = pd.to_numeric(b[c], errors="coerce")
    b = b[b.bsp > 1.0]
    return b[["date", "hn", "bsp", "win_lose", "event_id"]].drop_duplicates(["date", "hn"])


def lookup(dates):
    """{(date, hn): bsp} for the Melbourne dates given"""
    dates = sorted(set(str(d)[:10] for d in dates if isinstance(d, str) or pd.notna(d)))
    if not dates:
        return {}
    b = load(sorted(set(d[:7] for d in dates)))
    b = b[b.date.isin(dates)]
    return dict(zip(zip(b.date, b.hn), b.bsp))
