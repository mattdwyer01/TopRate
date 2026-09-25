"""
payload_io.py -- read the dashboard payload as ONE dict, whichever way it is stored on disk.

Since Sep 2026 toprate_daily.py (_write_payload) writes the payload in two files so the page loads fast:
toprate_data.json (every key, RACES = today's and later races) and toprate_history.json (earlier races).
Python readers that want the whole window (trackers, sweeps, scans) call load_payload(), which merges the
history RACES back in (race_id dedupe, the current file wins). Works unchanged on an old single-file payload.
"""
import json
from pathlib import Path

HISTORY_NAME = "toprate_history.json"


def load_payload(path="toprate_data.json"):
    path = Path(path)
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    hist_path = path.with_name(HISTORY_NAME)
    if hist_path.exists():
        with open(hist_path, encoding="utf-8") as f:
            hist = json.load(f).get("RACES") or []
        have = {r.get("race_id") for r in data.get("RACES") or []}
        data["RACES"] = [r for r in hist if r.get("race_id") not in have] + list(data.get("RACES") or [])
    return data
