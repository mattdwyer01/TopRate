"""
tab_replay_probe.py -- read-only probe: does TAB's public race JSON carry any replay, video or stream field?

Run it from an Australian IP (the Vultr runner or a home machine; TAB geo-blocks most cloud hosts, so it will not work in the cloud
session). It changes nothing in the repo:

    python tab_replay_probe.py                       # today's meetings, first resulted race of each (up to 4 meetings)
    python tab_replay_probe.py 2026-10-07 RANDWICK 3 # one race (date, TAB venue name as returned by the meetings call, race number)

For every payload it walks the whole JSON and prints each key or string value that looks media related (video, replay, stream, media, sky,
vimeo, brightcove, youtube, m3u8, mp4, hls, embed, player), with the path it was found at, then lists every distinct top-level and
race-level key so a human can eyeball anything the keyword list missed. Save the output and share it: if a public replay or stream
URL exists, a link-out button (or a payload field) can be built from the exact field names it shows.
"""
import json
import re
import sys
from datetime import date

import tab_results_poller as tp

MEDIA = re.compile(r"video|replay|stream|media|sky|vimeo|brightcove|youtube|m3u8|mp4|hls|embed|player", re.I)


def walk(obj, path, hits):
    if isinstance(obj, dict):
        for k, v in obj.items():
            p = f"{path}.{k}" if path else k
            if MEDIA.search(str(k)):
                hits.append((p, v if not isinstance(v, (dict, list)) else f"<{type(v).__name__} len {len(v)}>"))
            walk(v, p, hits)
    elif isinstance(obj, list):
        for i, v in enumerate(obj[:50]):
            walk(v, f"{path}[{i}]", hits)
    elif isinstance(obj, str) and MEDIA.search(obj) and len(obj) < 300:
        hits.append((path, obj))


def report(label, payload):
    hits = []
    walk(payload, "", hits)
    print(f"\n=== {label} ===")
    if isinstance(payload, dict):
        print("keys:", ", ".join(sorted(payload.keys())))
    if hits:
        for p, v in hits:
            print(f"  MEDIA-LIKE  {p} = {v}")
    else:
        print("  no media-like keys or values found")


def main():
    args = sys.argv[1:]
    if len(args) == 3:
        d, venue, n = args
        mn = venue
        payload = tp.get(tp.RACE_DETAIL.format(date=d, venue_mnemonic=mn, race_no=int(n)))
        report(f"{d} {venue} R{n} (venue treated as the mnemonic; use the venueMnemonic from the meetings call)", payload)
        return
    d = date.today().isoformat()
    meetings = tp.get(tp.MEETINGS.format(date=d), params={"jurisdiction": "VIC"})
    report("meetings list (VIC)", meetings)
    done = 0
    for m in meetings.get("meetings", []):
        if m.get("raceType") not in (None, "R"):
            continue
        mn = m.get("venueMnemonic")
        for race in m.get("races", []) or []:
            if race.get("raceStatus") in tp.FINAL_STATUSES:
                payload = tp.get(tp.RACE_DETAIL.format(date=d, venue_mnemonic=mn, race_no=race.get("raceNumber")))
                report(f"{m.get('meetingName')} R{race.get('raceNumber')} ({race.get('raceStatus')})", payload)
                done += 1
                break
        if done >= 4:
            break
    if not done:
        print("No resulted races found in the meetings payload (try later in the day, or pass a date, venue mnemonic and race number).")


if __name__ == "__main__":
    main()
