"""tr_field_rows.py -- TopRate is the PRIMARY source of the declared field and its numbers; racing.com (rc_field_rows.py) is the backup.

Reads data/tr_fields/<date>.json (written by toprate_race_fetch.py) into the runners frame:
  * a runner already in the frame (matched on date, normalised venue, race number, then horse name, then tab number) gets TopRate's
    numbers and declared-field columns and field_source 'toprate.au'. Its run_id and race_id are NEVER changed (the projection log, results
    and payload key on them), and a resulted row is never touched. A scratching is only ever set, never cleared.
  * a race with no rows at all is created from TopRate with TopRate's own race_id / run_id.
  * a runner TopRate lists that the race does not have yet (a late entry) is added only if its tab number is free in that race.
A file older than MAX_AGE_HOURS (the fetch has been failing) is ignored, so racing.com simply carries on as before.

Usage (dry run, prints counts, writes nothing):  python tr_field_rows.py DATE [DATE ...]
"""
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

from rc_field_rows import norm_venue

DIR = Path(__file__).parent / "data" / "tr_fields"
MAX_AGE_HOURS = 30
SOURCE = "toprate.au"

# runner column <- fetcher row key. Numbers are always overwritten (TopRate is their only source).
NUMBER_COLUMNS = {
    "wpr_nett": "wpr_nett", "toprate_rating": "toprate_rating", "speed_rating": "speed_rating", "pfm_score": "pfm_score",
    "pfm_score_rank": "pfm_score_rank", "jockey_rating": "jockey_rating", "toprate_price": "toprate_price",
}
# Declared-field columns TopRate now owns on a row that has not been resulted.
DECLARED_COLUMNS = {
    "barrier": "barrier", "jockey": "jockey", "trainer": "trainer", "tab_number": "tab_number", "weight_carried": "weight",
    "horse_age": "horse_age", "horse_sex": "horse_sex", "silk_url": "silk_url", "handicap_rating": "handicap_rating",
}
# Filled only when the row has nothing (TAB writes prices later and wins; the race facts are the same on both sources).
FILL_IF_BLANK = {
    "horse_id": "horse_id", "fixed_win_price": "fixed_win_price", "open_price": "fixed_win_opening", "going": "going",
    "race_class": "race_class", "race_name": "race_name", "distance": "distance", "prize_money": "prize_money",
    "start_time": "start_time", "state": "state", "track_grading": "track_grading",
}


def _hn(s):
    return re.sub(r"[^a-z0-9]", "", str(s or "").lower())


def _blank(v):
    return v is None or str(v).strip() in ("", "nan", "None", "NaT")


def load(date_str, now=None):
    """The fetched rows for a date, or [] if the file is missing, unreadable or older than MAX_AGE_HOURS."""
    try:
        d = json.loads((DIR / f"{date_str}.json").read_text())
        fetched = datetime.fromisoformat(str(d.get("fetched", "")).replace("Z", "+00:00"))
        if fetched.tzinfo is None:
            fetched = fetched.replace(tzinfo=timezone.utc)
        age = ((now or datetime.now(timezone.utc)) - fetched).total_seconds() / 3600
        return d.get("rows", []) if age <= MAX_AGE_HOURS else []
    except Exception:
        return []


def _set(df, i, c, v):
    try:
        df.at[i, c] = v
    except (TypeError, ValueError):
        df.at[i, c] = str(v)


def _new_row(r):
    return {
        "date": r["date"], "venue": r["venue"], "state": r.get("state"), "race": r["race_no"], "race_id": r["race_id"],
        "race_name": r.get("race_name"), "distance": r.get("distance"), "race_class": r.get("race_class"),
        "prize_money": r.get("prize_money"), "going": r.get("going"), "track_grading": r.get("track_grading"),
        "start_time": r.get("start_time"), "run_id": r["run_id"], "horse_id": r.get("horse_id"),
        "scratched": 1 if r.get("scratched") else 0, "tab_number": r.get("tab_number"), "barrier": r.get("barrier"),
        "horse": r.get("horse"), "jockey": r.get("jockey"), "trainer": r.get("trainer"), "weight_carried": r.get("weight"),
        "horse_age": r.get("horse_age"), "horse_sex": r.get("horse_sex"), "silk_url": r.get("silk_url"),
        "handicap_rating": r.get("handicap_rating"), "fixed_win_price": r.get("fixed_win_price"),
        "open_price": r.get("fixed_win_opening"), "resulted": 0, "interim_resulted": 0, "field_source": SOURCE,
        **{col: r.get(key) for col, key in NUMBER_COLUMNS.items()},
    }


def merge_tr_fields(runners_df, date_str, dry_run=False, now=None):
    """Return (runners_df, stats). With dry_run the frame is returned unchanged and only stats are filled."""
    import pandas as pd
    rows = [r for r in load(date_str, now) if r.get("race_id") and r.get("run_id")]
    stats = {"tr_rows": len(rows), "updated": 0, "added_rows": 0, "added_races": 0, "unmatched_skipped": 0, "resulted_skipped": 0,
             "changed": {c: 0 for c in list(NUMBER_COLUMNS) + list(DECLARED_COLUMNS)}}
    if not rows:
        return runners_df, stats
    out = runners_df.copy()
    day = out["date"].astype(str).str[:10] == date_str if len(out) else pd.Series([], dtype=bool)
    by_name, by_tab, races, taken_ids = {}, {}, set(), set(out["run_id"].astype(str)) if len(out) else set()
    for i in out.index[day]:
        v, n = norm_venue(out.at[i, "venue"]), str(out.at[i, "race"])
        races.add((v, n))
        by_name[(v, n, _hn(out.at[i, "horse"]))] = i
        t = out.at[i, "tab_number"] if "tab_number" in out.columns else None
        if not _blank(t) and str(t) not in ("0", "0.0"):
            by_tab[(v, n, str(int(float(t))))] = i
    new_rows = []
    for r in rows:
        v, n = norm_venue(r.get("venue")), str(r.get("race_no"))
        if (v, n) not in races:                         # a race nobody has rows for: TopRate creates it
            if str(r["run_id"]) in taken_ids:
                continue
            new_rows.append(_new_row(r))
            taken_ids.add(str(r["run_id"]))
            stats["added_rows"] += 1
            continue
        i = by_name.get((v, n, _hn(r.get("horse"))))
        if i is None and r.get("tab_number") is not None:
            i = by_tab.get((v, n, str(r["tab_number"])))
        if i is None:                                   # late entry: only if its tab number is free in the race
            if r.get("scratched") or (v, n, str(r.get("tab_number"))) in by_tab or str(r["run_id"]) in taken_ids:
                stats["unmatched_skipped"] += 1
                continue
            new_rows.append(_new_row(r))
            taken_ids.add(str(r["run_id"]))
            stats["added_rows"] += 1
            continue
        if str(out.at[i, "resulted"]) in ("1", "1.0"):
            stats["resulted_skipped"] += 1
            continue
        stats["updated"] += 1
        for col, key in NUMBER_COLUMNS.items():
            val = r.get(key)
            if val is not None and col in out.columns:
                old = out.at[i, col]
                if _blank(old) or float(old) != float(val):
                    stats["changed"][col] += 1
                    _set(out, i, col, val)
        for col, key in DECLARED_COLUMNS.items():
            val = r.get(key)
            if val is not None and col in out.columns and str(out.at[i, col]) != str(val):
                stats["changed"][col] += 1
                _set(out, i, col, val)
        for col, key in FILL_IF_BLANK.items():
            val = r.get(key)
            if val is not None and col in out.columns and _blank(out.at[i, col]):
                _set(out, i, col, val)
        if r.get("scratched") and str(out.at[i, "scratched"]) not in ("1", "1.0"):
            _set(out, i, "scratched", 1)
        if "field_source" in out.columns:
            _set(out, i, "field_source", SOURCE)
    if new_rows:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", category=FutureWarning)
            out = pd.concat([out, pd.DataFrame(new_rows)], ignore_index=True)
        stats["added_races"] = len({(x["venue"], x["race"]) for x in new_rows if (norm_venue(x["venue"]), str(x["race"])) not in races})
    return (runners_df if dry_run else out), stats


if __name__ == "__main__":
    import pandas as pd
    df = pd.read_csv("runners.csv", low_memory=False)
    for d in sys.argv[1:]:
        res, s = merge_tr_fields(df, d, dry_run=False)   # computed in memory, never saved
        dup = res[res.date.astype(str).str[:10] == d].duplicated(["venue", "race", "horse"]).sum()
        print(d, json.dumps(s), "| duplicate (venue, race, horse) rows after merge:", int(dup),
              "| rows", len(df), "->", len(res))
