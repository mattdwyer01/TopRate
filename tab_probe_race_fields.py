"""
tab_probe_race_fields.py -- read-only probe: what does TAB's racing API return for a FINISHED race?

Why (Oct 2026): toprate.au is blocking our data refreshes, so our own WPR needs margins, finish times and (ideally)
sectionals from somewhere else (see the "own WPR ratings" entry in CLAUDE.md). The poller only reads results[]
(finishing order), prices, weights and conditions, so nothing in the repo shows whether TAB also carries the
race time, margins or sectionals. This answers that from a real payload.

Run on the AU self-hosted runner (TAB geo-blocks other hosts; check with tab_results_poller.py --diagnose first):
    python tab_probe_race_fields.py                    # yesterday, 3 paying races
    python tab_probe_race_fields.py --date 2026-10-10 --n 5

What it does: lists the day's thoroughbred meetings, takes the first --n races whose raceStatus is Paying, fetches
each race detail, saves the raw meeting stub and race JSON to tab_raw/ (gitignored), and prints every key path with
a sample value. Paths whose name looks like margin / time / sectional / distance / weight / age are marked with
">>" so they stand out. Nothing is written to the runners file or the payload.
"""
import argparse
import json
import re
import sys
from datetime import date, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import tab_results_poller as poller  # reuse get(), MEETINGS, RACE_DETAIL, RACE_TYPE, AU_STATES

OUT = Path(__file__).parent / "tab_raw"
INTEREST = re.compile(r"margin|time|sect|split|furlong|600|800|400|200|dist|speed|weight|age|sex|result|position|"
                      r"placing|beaten|length|dividend|stewards|comment", re.I)


def walk(obj, path="", seen=None, out=None):
    """Collect (path, sample) for every leaf; list items share one path ('[]') so a field list stays short."""
    out = {} if out is None else out
    if isinstance(obj, dict):
        for k, v in obj.items():
            walk(v, f"{path}.{k}" if path else k, seen, out)
    elif isinstance(obj, list):
        if not obj:
            out.setdefault(path + "[]", "(empty list)")
        for v in obj[:3]:
            walk(v, path + "[]", seen, out)
    else:
        out.setdefault(path, obj)
    return out


def show(label, obj):
    print(f"\n===== {label} =====")
    for p, v in sorted(walk(obj).items()):
        mark = ">>" if INTEREST.search(p) else "  "
        print(f"{mark} {p} = {json.dumps(v, default=str)[:90]}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", default=str(date.today() - timedelta(days=1)))
    ap.add_argument("--n", type=int, default=3)
    args = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    taken = 0
    for jur in poller.TAB_JURISDICTIONS:
        try:
            payload = poller.get(poller.MEETINGS.format(date=args.date), {"jurisdiction": jur}, timeout=20)
        except Exception as e:
            print(f"{jur} meetings failed: {type(e).__name__}: {e}")
            continue
        for m in payload.get("meetings", []):
            if m.get("raceType") != poller.RACE_TYPE or m.get("location") not in poller.AU_STATES:
                continue
            for rc in m.get("races", []):
                if rc.get("raceStatus") != "Paying" or not m.get("venueMnemonic"):
                    continue
                name = f"{args.date}_{m.get('meetingName')}_R{rc.get('raceNumber')}".replace(" ", "-")
                det = poller.get(poller.RACE_DETAIL.format(date=args.date, venue_mnemonic=m["venueMnemonic"],
                                                           race_no=rc["raceNumber"]), {"jurisdiction": jur}, timeout=20)
                (OUT / f"{name}_stub.json").write_text(json.dumps({"meeting": {k: v for k, v in m.items() if k != "races"},
                                                                    "race": rc}, indent=1, default=str))
                (OUT / f"{name}_detail.json").write_text(json.dumps(det, indent=1, default=str))
                show(f"{name} meeting-list stub (race)", rc)
                show(f"{name} race detail", det)
                taken += 1
                if taken >= args.n:
                    print(f"\nRaw JSON saved under {OUT}. Look for margins, race time and sectionals among the >> lines.")
                    return
    print(f"\nOnly {taken} paying race(s) found for {args.date}.")


if __name__ == "__main__":
    main()
