"""tr_field_rows.py -- bring TopRate's pre-race numbers (data/tr_fields/<date>.json, written by toprate_race_fetch.py) into the runners frame.

TopRate is the primary source for wpr_nett, speed, TopRate rating/price, form factor and jockey rating; racing.com stays the source of the
declared field (rc_field_rows.py) and is the fallback if a TopRate fetch fails. This module NEVER creates rows, never changes race_id/run_id,
never touches a resulted row, and only writes the columns in TR_COLUMNS. A runner TopRate has no value for keeps whatever the row had.

Rows are matched on (date, normalised venue, race number, normalised horse name), then (venue, race number, tab number) for a horse whose
name differs. IDs cannot be used: racing.com-built rows carry integer run_ids from 7e12 and race_ids from racing.com, TopRate's are its own.

Usage (dry run, writes nothing):  python tr_field_rows.py DATE [DATE ...]
"""
import json
import re
import sys
from pathlib import Path

from rc_field_rows import norm_venue

DIR = Path(__file__).parent / "data" / "tr_fields"

# runner column <- key in the fetcher's row
TR_COLUMNS = {
    "wpr_nett": "wpr_nett",
    "toprate_rating": "toprate_rating",
    "speed_rating": "speed_rating",
    "pfm_score": "pfm_score",
    "pfm_score_rank": "pfm_score_rank",
    "jockey_rating": "jockey_rating",
    "toprate_price": "toprate_price",
}


def _hn(s):
    return re.sub(r"[^a-z0-9]", "", str(s or "").lower())


def load(date_str):
    try:
        return json.loads((DIR / f"{date_str}.json").read_text()).get("rows", [])
    except Exception:
        return []


def merge_tr_fields(runners_df, date_str, dry_run=False):
    """Return (runners_df, stats). stats: rows (TopRate rows), matched, per-column changed counts, unmatched venues."""
    import pandas as pd
    rows = load(date_str)
    stats = {"tr_rows": len(rows), "matched": 0, "changed": {c: 0 for c in TR_COLUMNS}, "unmatched": 0, "unmatched_venues": {}}
    if not rows or not len(runners_df):
        return runners_df, stats
    day = runners_df["date"].astype(str).str[:10] == date_str
    idx = runners_df.index[day]
    by_name, by_tab = {}, {}
    for i in idx:
        v, n = norm_venue(runners_df.at[i, "venue"]), str(runners_df.at[i, "race"])
        by_name[(v, n, _hn(runners_df.at[i, "horse"]))] = i
        t = runners_df.at[i, "tab_number"] if "tab_number" in runners_df.columns else None
        if pd.notna(t) and str(t) not in ("0", "0.0", ""):
            by_tab[(v, n, str(int(float(t))))] = i
    out = runners_df if dry_run else runners_df.copy()
    snap = runners_df if dry_run else out
    for r in rows:
        if r.get("scratched"):
            continue
        v, n = norm_venue(r.get("venue")), str(r.get("race_no"))
        i = by_name.get((v, n, _hn(r.get("horse"))))
        if i is None and r.get("tab_number") is not None:
            i = by_tab.get((v, n, str(r["tab_number"])))
        if i is None:
            stats["unmatched"] += 1
            stats["unmatched_venues"][r.get("venue")] = stats["unmatched_venues"].get(r.get("venue"), 0) + 1
            continue
        stats["matched"] += 1
        if str(snap.at[i, "resulted"]) in ("1", "1.0"):
            continue
        for col, key in TR_COLUMNS.items():
            val = r.get(key)
            if val is None or col not in out.columns:
                continue
            old = snap.at[i, col]
            if pd.isna(old) or float(old) != float(val):
                stats["changed"][col] += 1
                if not dry_run:
                    out.at[i, col] = val
    return out, stats


if __name__ == "__main__":
    import pandas as pd
    df = pd.read_csv("runners.csv", low_memory=False)
    for d in sys.argv[1:]:
        _, s = merge_tr_fields(df, d, dry_run=True)
        print(d, json.dumps(s))
