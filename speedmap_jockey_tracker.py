"""Forward-tracking log for two speed_map + jockey betting rules found via
session-long backtesting against toprate_data.json (see chat history, not
committed anywhere - this is a standalone research script, not part of the
main pipeline). NOT wired into any model, projection, or pick logic -
read-only against toprate_data.json/toprate_runners.csv, writes only its own
two CSV logs. Never touches toprate_runners.csv, toprate_data.json, or any
other production file.

Both rules require, in every race with at least 2 runners carrying a
speed_map value: the runner's speed_map, demeaned against that race's own
mean (see wpjcb.speed_map / SpeedMapGrid.tsx's own display logic), is
"favoured" or "neutral" (>= -0.5 relative to the field), AND the runner is
within 6 WPR of the race's own top-projected runner, AND its jockey's
trailing-90-day win% (jw) is >= 14, AND its live/final price is $3+.

Tracker A (high volume, no rating-agreement requirement) vs Tracker B (low
volume, ALSO requires the runner to be #1 in-race by both TopRate's own
rating (trr) and the external form-factor score (pfm_score_rank)) - see
GAP_MAX/JW_MIN/PRICE_MIN/TAGS below for the shared rule, and QUALIFIES_B for
B's extra requirement.

Run daily (idempotent): captures any newly-qualifying runner from TODAY's
races (Australia/Melbourne) not already logged, and fills in the result
(finish position / won / final price) for any previously-logged runner that
has since resulted. Never re-evaluates or removes an already-logged pick -
each tracker's log is an append-only record of what the rule would have
picked and how it went, not a live, moving list.
"""
import csv
import json
import sys
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import pandas as pd

_DIR = Path(__file__).parent
DATA_JSON = _DIR / "toprate_data.json"
RUNNERS_CSV = _DIR / "toprate_runners.csv"
TRACKER_A_CSV = _DIR / "tracker_high_volume.csv"
TRACKER_B_CSV = _DIR / "tracker_low_volume.csv"

DEMEAN_THRESHOLD = 0.5   # matches SpeedMapGrid.tsx's THREAT_THRESHOLD
GAP_MAX = 6.0            # WPR points from the race's own top-projected runner
JW_MIN = 14.0            # jockey_win_pct_90d floor
PRICE_MIN = 3.0          # SP/fixed price floor
TAGS = ("favoured", "neutral")

LOG_COLUMNS = [
    "run_id", "race_id", "date", "venue", "race_no", "tab", "horse", "tag",
    "gap_wpr", "jw", "trr_rank_1", "pfm_rank_1", "price_at_pick",
    "captured_at", "resulted", "finish_position", "won", "price_final",
]


def _melbourne_today() -> str:
    return datetime.now(ZoneInfo("Australia/Melbourne")).strftime("%Y-%m-%d")


def _rank_desc(value, all_values):
    if value is None:
        return None
    return 1 + sum(1 for v in all_values if v is not None and v > value)


def _load_pfm_rank_lookup() -> dict:
    if not RUNNERS_CSV.exists():
        return {}
    df = pd.read_csv(RUNNERS_CSV, usecols=["run_id", "pfm_score_rank"], dtype={"run_id": str})
    return dict(zip(df["run_id"], df["pfm_score_rank"]))


def _load_log(path: Path) -> dict:
    """Returns {run_id: row_dict} for an existing log, or {} if none yet."""
    if not path.exists():
        return {}
    with open(path, newline="") as f:
        return {row["run_id"]: row for row in csv.DictReader(f)}


def _write_log(path: Path, rows_by_run_id: dict):
    rows = sorted(rows_by_run_id.values(), key=lambda r: (r["date"], r["race_id"], r["tab"]))
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=LOG_COLUMNS)
        w.writeheader()
        w.writerows(rows)


def build_candidates(data: dict, pfm_by_rid: dict, target_date: str):
    """Yields (runner_dict, extra) for every runner in target_date's races
    that qualifies for Tracker A, with `extra` carrying the fields both
    trackers need (including whether it also qualifies for Tracker B)."""
    for r in data.get("RACES", []):
        if r.get("date") != target_date:
            continue
        runners = [u for u in r.get("runners", []) if not u.get("scr")]
        valid = []
        for u in runners:
            cb = u.get("wpjcb") or {}
            sm = cb.get("speed_map")
            if sm is not None:
                valid.append((u, sm))
        if len(valid) < 2:
            continue
        race_mean = sum(sm for _, sm in valid) / len(valid)

        trr_vals = [u.get("trr") for u in runners]
        wpr_vals = [u.get("wpjp") for u in runners]
        top_wpr = max((v for v in wpr_vals if v is not None), default=None)

        for u, sm in valid:
            demeaned = sm - race_mean
            if demeaned <= -DEMEAN_THRESHOLD:
                tag = "unfavoured"
            elif demeaned >= DEMEAN_THRESHOLD:
                tag = "favoured"
            else:
                tag = "neutral"
            if tag not in TAGS:
                continue

            wpjp = u.get("wpjp")
            gap = (top_wpr - wpjp) if (wpjp is not None and top_wpr is not None) else None
            if gap is None or gap > GAP_MAX:
                continue

            jw = u.get("jw")
            if jw is None or jw < JW_MIN:
                continue

            price = u.get("sp") if u.get("sp") is not None else u.get("fx")
            if price is None or price < PRICE_MIN:
                continue

            trr_rank = _rank_desc(u.get("trr"), trr_vals)
            pfm_rank = pfm_by_rid.get(str(u.get("rid", "")))
            qualifies_b = (trr_rank == 1) and (pfm_rank == 1)

            yield r, u, {
                "tag": tag, "gap": gap, "jw": jw, "price": price,
                "trr_rank_1": trr_rank == 1, "pfm_rank_1": pfm_rank == 1,
                "qualifies_b": qualifies_b,
            }


def capture_new_picks(data: dict, pfm_by_rid: dict):
    target_date = _melbourne_today()
    log_a = _load_log(TRACKER_A_CSV)
    log_b = _load_log(TRACKER_B_CSV)
    captured_at = datetime.now(ZoneInfo("Australia/Melbourne")).isoformat()

    new_a = new_b = 0
    for r, u, extra in build_candidates(data, pfm_by_rid, target_date):
        run_id = str(u.get("rid", ""))
        if not run_id:
            continue
        row = {
            "run_id": run_id,
            "race_id": r.get("race_id"),
            "date": r.get("date"),
            "venue": r.get("venue"),
            "race_no": r.get("race"),
            "tab": u.get("tab"),
            "horse": u.get("h"),
            "tag": extra["tag"],
            "gap_wpr": round(extra["gap"], 2),
            "jw": extra["jw"],
            "trr_rank_1": extra["trr_rank_1"],
            "pfm_rank_1": extra["pfm_rank_1"],
            "price_at_pick": extra["price"],
            "captured_at": captured_at,
            "resulted": False,
            "finish_position": "",
            "won": "",
            "price_final": "",
        }
        if run_id not in log_a:
            log_a[run_id] = row
            new_a += 1
        if extra["qualifies_b"] and run_id not in log_b:
            log_b[run_id] = dict(row)
            new_b += 1

    _write_log(TRACKER_A_CSV, log_a)
    _write_log(TRACKER_B_CSV, log_b)
    print(f"  captured {new_a} new high-volume picks, {new_b} new low-volume picks "
          f"for {target_date}")


def reconcile_results(data: dict):
    """Fills in the outcome for any previously-logged pick whose race has
    since resulted, by run_id. Never re-evaluates whether it still
    qualifies - a logged pick's rule inputs are frozen at capture time."""
    by_run_id = {}
    for r in data.get("RACES", []):
        for u in r.get("runners", []):
            rid = str(u.get("rid", ""))
            if rid:
                by_run_id[rid] = u

    for path in (TRACKER_A_CSV, TRACKER_B_CSV):
        log = _load_log(path)
        if not log:
            continue
        n_filled = 0
        for run_id, row in log.items():
            if row.get("resulted") == "True":
                continue
            u = by_run_id.get(run_id)
            if u is None or u.get("f") is None:
                continue
            row["resulted"] = True
            row["finish_position"] = u.get("f")
            row["won"] = int(u.get("won") == 1)
            row["price_final"] = u.get("sp") if u.get("sp") is not None else row["price_at_pick"]
            n_filled += 1
        _write_log(path, log)
        print(f"  {path.name}: reconciled {n_filled} newly-resulted pick(s)")


def main():
    if not DATA_JSON.exists():
        print(f"speedmap_jockey_tracker: {DATA_JSON.name} not found, skipping")
        return
    with open(DATA_JSON) as f:
        data = json.load(f)
    pfm_by_rid = _load_pfm_rank_lookup()

    print("Reconciling previously-logged picks...")
    reconcile_results(data)
    print("Capturing today's new picks...")
    capture_new_picks(data, pfm_by_rid)


if __name__ == "__main__":
    main()
