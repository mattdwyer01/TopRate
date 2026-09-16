"""One-off cleanup (Sep 2026): re-validates every already-logged tracker pick
against the corrected solo-only-before-price rule (see
speedmap_jockey_tracker.py's own comment on why price moved after the solo
check) and drops any row that no longer qualifies. Not part of the daily
pipeline - the running script's own "never re-evaluate a logged pick" rule
is a deliberate default, but this is a one-off correction of a real rule
bug, run once by hand at the user's explicit request, same precedent as
wpr_form_history_dedup_cleanup.py.

Re-validates against toprate_data.json's CURRENT snapshot of each race (not
a preserved point-in-time capture, since none exists) - the best available
approximation, and the same data this fix's own backtest was measured
against.
"""
import csv
import json
from pathlib import Path

from speedmap_jockey_tracker import build_candidates, _load_pfm_lookup, _bush_meeting_keys

_DIR = Path(__file__).parent
DATA_JSON = _DIR / "toprate_data.json"
TRACKER_A_CSV = _DIR / "tracker_high_volume.csv"
TRACKER_B_CSV = _DIR / "tracker_low_volume.csv"


def main():
    data = json.load(open(DATA_JSON))
    pfm_rank_by_rid, pfm_score_by_rid = _load_pfm_lookup()
    bush_keys = _bush_meeting_keys(data)

    with open(TRACKER_A_CSV, newline="") as f:
        rows_a = list(csv.DictReader(f))
    with open(TRACKER_B_CSV, newline="") as f:
        rows_b = list(csv.DictReader(f))

    dates = sorted({row["date"] for row in rows_a} | {row["date"] for row in rows_b})

    still_valid_a = set()
    still_valid_b = set()
    for d in dates:
        for r, u, extra in build_candidates(data, pfm_rank_by_rid, pfm_score_by_rid, d, bush_keys):
            rid = str(u.get("rid", ""))
            if extra["include_in_a"]:
                still_valid_a.add(rid)
            if extra["include_in_b"]:
                still_valid_b.add(rid)

    def clean(rows, still_valid, path):
        fieldnames = rows[0].keys() if rows else []
        kept = [r for r in rows if r["run_id"] in still_valid]
        removed = len(rows) - len(kept)
        with open(path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            w.writerows(sorted(kept, key=lambda r: (r["date"], r["race_id"], r["tab"])))
        print(f"  {path.name}: {len(rows)} -> {len(kept)} rows ({removed} removed)")

    clean(rows_a, still_valid_a, TRACKER_A_CSV)
    clean(rows_b, still_valid_b, TRACKER_B_CSV)


if __name__ == "__main__":
    main()
