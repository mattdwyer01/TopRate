"""Sky Racing venue codes for race replays (replay_codes.json).

TAB's meeting list carries each race's replay URL (skyRacing.video, e.g.
.../Race_Replay/2026/10/20261007OHIR01_V.mp4) only for the current day. The file name is
YYYYMMDD + venue code + 2-digit race number, and the code is stable per venue, so we keep a
venue -> code map and let the dashboard build the URL for any date (Sky keeps files for at
least a year, checked Oct 2026). Written by tab_results_poller.py; only rewritten when it changes.
"""
import json
import re
from pathlib import Path

PATH = Path("replay_codes.json")
_RX = re.compile(r"/\d{8}([A-Z]+)\d{2}_V\.mp4")
_seen = {}


def note(venue, race):
    """Remember the code from one TAB race stub. venue must be the PROVIDER venue (provider_venue_for(), e.g. "Randwick" not TAB's
    "RANDWICK KENSINGTON"), because that is the name the dashboard has for the race and for past runs."""
    url = (race.get("skyRacing") or {}).get("video")
    m = url and _RX.search(url)
    if m and venue:
        _seen[str(venue).strip().lower()] = m.group(1)


def flush():
    """Merge codes seen this cycle into replay_codes.json. Returns True if the file changed."""
    if not _seen:
        return False
    try:
        cur = json.loads(PATH.read_text()) if PATH.exists() else {}
    except Exception:
        cur = {}
    new = {**cur, **_seen}
    if new == cur:
        return False
    PATH.write_text(json.dumps(new, indent=0, sort_keys=True))
    return True
