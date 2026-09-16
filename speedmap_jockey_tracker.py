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
trailing-90-day win% (jw) is >= 14, AND its live/final price is $3+, AND
it is the ONLY runner in that race meeting all of the above (solo-only,
Sep 2026 - see build_candidates' own docstring for the backtest that
justified this: the rule firing 2+ times in the same race performed
dramatically worse, +14% ROI solo vs -8% to -12% blended across every
multi-pick race, and no tie-breaker tested recovered the lost edge as
cleanly as just not betting a contested race at all).

Tracker A (high volume, no rating-agreement requirement) vs Tracker B (low
volume, ALSO requires the runner to be #1 in-race by both TopRate's own
rating (trr) and the external form-factor score (pfm_score_rank)) - see
GAP_MAX/JW_MIN/PRICE_MIN/TAGS below for the shared rule. Each tracker's
solo-only requirement is checked against its OWN population, independently
- a race with 3 base-rule qualifiers silences A entirely even if exactly
one of those 3 also satisfies B's extra condition, and B still fires for
that one regardless (a runner can end up in A, B, both, or neither).

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

# Bush/picnic-meeting threshold - matches lib/meetings.ts's own
# BUSH_TRACK_THRESHOLD exactly (a meeting whose biggest single race tops out
# at $20k or less). Real user feedback (2026-09-16): these small-field,
# thin-market meetings shouldn't feed a tracker meant to approximate a real
# bettor's actual selections.
BUSH_TRACK_THRESHOLD = 20_000


def _bush_meeting_keys(data: dict) -> set:
    """Returns {(date, venue)} for every meeting whose biggest single race's
    prize money is <= BUSH_TRACK_THRESHOLD - same rule as
    lib/meetings.ts's bushMeetingKeys(), computed independently here since
    this script never touches the frontend bundle."""
    top_prize = {}
    for r in data.get("RACES", []):
        key = (r.get("date"), r.get("venue"))
        prize = r.get("prize") or 0
        top_prize[key] = max(top_prize.get(key, 0), prize)
    return {key for key, prize in top_prize.items() if prize <= BUSH_TRACK_THRESHOLD}

LOG_COLUMNS = [
    "run_id", "race_id", "date", "venue", "race_no", "start_time", "tab",
    "horse", "silk_url", "tag", "wpr_prediction", "gap_wpr", "toprate_rating",
    "form_factor", "jw", "trr_rank_1", "pfm_rank_1", "price_at_pick",
    "captured_at", "resulted", "finish_position", "won", "price_final",
]


def _melbourne_today() -> str:
    return datetime.now(ZoneInfo("Australia/Melbourne")).strftime("%Y-%m-%d")


def _rank_desc(value, all_values):
    if value is None:
        return None
    return 1 + sum(1 for v in all_values if v is not None and v > value)


def _load_pfm_lookup() -> tuple:
    """Returns ({run_id: pfm_score_rank}, {run_id: pfm_score}) - both pulled
    from toprate_runners.csv since pfm_score/pfm_score_rank aren't in
    toprate_data.json's runner payload (see CLAUDE.md/adapter.ts - never
    exposed to the frontend directly, only used here)."""
    if not RUNNERS_CSV.exists():
        return {}, {}
    df = pd.read_csv(RUNNERS_CSV, usecols=["run_id", "pfm_score", "pfm_score_rank"], dtype={"run_id": str})
    return dict(zip(df["run_id"], df["pfm_score_rank"])), dict(zip(df["run_id"], df["pfm_score"]))


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


def build_candidates(data: dict, pfm_rank_by_rid: dict, pfm_score_by_rid: dict, target_date: str,
                      bush_keys: set | None = None):
    """Yields (runner_dict, extra) for every runner that qualifies for
    Tracker A and/or Tracker B on target_date - `extra["include_in_a"]`/
    `extra["include_in_b"]` say which (a runner can be in one, the other,
    or both; see the solo-only comment above for why they're independent,
    not "B implies A"). bush_keys (optional): {(date, venue)} to skip
    entirely - computed once via _bush_meeting_keys() and passed in rather
    than recomputed per call."""
    if bush_keys is None:
        bush_keys = _bush_meeting_keys(data)
    for r in data.get("RACES", []):
        if r.get("date") != target_date:
            continue
        if (r.get("date"), r.get("venue")) in bush_keys:
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

        # Collect every base-rule qualifier in this race first, rather than
        # yielding as each one is found - solo-only means Tracker A stays
        # silent on this race unless exactly one runner clears every base
        # condition.
        race_qualifiers = []
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

            race_qualifiers.append((u, tag, gap, jw, price))

        if not race_qualifiers:
            continue

        # Tracker B's rating-agreement condition, checked independently
        # against its OWN solo requirement - NOT coupled to whether A fired
        # on this race. A 3-horse base-qualifier race silences A entirely,
        # but if exactly one of those 3 also happens to be #1 by both
        # TopRate rating and form-factor, B still fires for that one -
        # each tracker only ever needs ITS OWN rule to be unambiguous, not
        # the other tracker's.
        info_by_rid = {}
        b_pool = []
        for (u, tag, gap, jw, price) in race_qualifiers:
            rid = str(u.get("rid", ""))
            trr_rank = _rank_desc(u.get("trr"), trr_vals)
            pfm_rank = pfm_rank_by_rid.get(rid)
            info_by_rid[rid] = (u, tag, gap, jw, price, trr_rank, pfm_rank)
            if trr_rank == 1 and pfm_rank == 1:
                b_pool.append(rid)

        include_a_rid = str(race_qualifiers[0][0].get("rid", "")) if len(race_qualifiers) == 1 else None
        include_b_rid = b_pool[0] if len(b_pool) == 1 else None

        for rid in {x for x in (include_a_rid, include_b_rid) if x is not None}:
            u, tag, gap, jw, price, trr_rank, pfm_rank = info_by_rid[rid]
            yield r, u, {
                "tag": tag, "gap": gap, "jw": jw, "price": price,
                "trr_rank_1": trr_rank == 1, "pfm_rank_1": pfm_rank == 1,
                "include_in_a": rid == include_a_rid,
                "include_in_b": rid == include_b_rid,
                "wpr_prediction": u.get("wpjp"),
                "toprate_rating": u.get("trr"),
                "form_factor": pfm_score_by_rid.get(rid),
                "start_time": r.get("start_time"),
                "silk_url": u.get("sk"),
            }


def capture_new_picks(data: dict, pfm_rank_by_rid: dict, pfm_score_by_rid: dict, target_date: str | None = None):
    """target_date defaults to today (the normal daily-pipeline call).
    Passing an explicit past date is how the one-off historical backfill
    (see backfill_tracker_history.py, not part of the daily pipeline)
    captures what the rule would have picked on a day before this script
    existed - reconcile_results() then fills in the real result for free
    since those races are already resulted in toprate_data.json."""
    target_date = target_date or _melbourne_today()
    log_a = _load_log(TRACKER_A_CSV)
    log_b = _load_log(TRACKER_B_CSV)
    captured_at = datetime.now(ZoneInfo("Australia/Melbourne")).isoformat()

    new_a = new_b = 0
    for r, u, extra in build_candidates(data, pfm_rank_by_rid, pfm_score_by_rid, target_date):
        run_id = str(u.get("rid", ""))
        if not run_id:
            continue
        row = {
            "run_id": run_id,
            "race_id": r.get("race_id"),
            "date": r.get("date"),
            "venue": r.get("venue"),
            "race_no": r.get("race"),
            "start_time": extra["start_time"],
            "tab": u.get("tab"),
            "horse": u.get("h"),
            "silk_url": extra["silk_url"] or "",
            "tag": extra["tag"],
            "wpr_prediction": extra["wpr_prediction"],
            "gap_wpr": round(extra["gap"], 2),
            "toprate_rating": extra["toprate_rating"],
            "form_factor": extra["form_factor"],
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
        if extra["include_in_a"] and run_id not in log_a:
            log_a[run_id] = row
            new_a += 1
        if extra["include_in_b"] and run_id not in log_b:
            log_b[run_id] = dict(row)
            new_b += 1

    _write_log(TRACKER_A_CSV, log_a)
    _write_log(TRACKER_B_CSV, log_b)
    print(f"  captured {new_a} new high-volume picks, {new_b} new low-volume picks "
          f"for {target_date}")


# Enrichment fields that are safe to backfill onto an already-logged row
# whenever they're still blank (e.g. rows logged before these columns
# existed) - never overwrites a value that's already there, since these
# are meant to be frozen at capture time like everything else in the log.
_ENRICHABLE = ("start_time", "silk_url", "wpr_prediction", "toprate_rating", "form_factor")


def reconcile_results(data: dict, pfm_rank_by_rid: dict, pfm_score_by_rid: dict):
    """Fills in the outcome for any previously-logged pick whose race has
    since resulted, by run_id. Never re-evaluates whether it still
    qualifies - a logged pick's rule inputs are frozen at capture time.
    Also backfills any of _ENRICHABLE that are blank on an older row
    (added after this script's first version shipped) whenever the run_id
    is still findable in today's data - never touches a value already
    present."""
    by_run_id = {}
    for r in data.get("RACES", []):
        for u in r.get("runners", []):
            rid = str(u.get("rid", ""))
            if rid:
                by_run_id[rid] = (r, u)

    for path in (TRACKER_A_CSV, TRACKER_B_CSV):
        log = _load_log(path)
        if not log:
            continue
        n_filled = 0
        n_enriched = 0
        for run_id, row in log.items():
            found = by_run_id.get(run_id)
            if found is not None:
                r, u = found
                if not row.get("start_time"):
                    row["start_time"] = r.get("start_time")
                    n_enriched += 1
                if not row.get("silk_url"):
                    row["silk_url"] = u.get("sk") or ""
                if not row.get("wpr_prediction"):
                    row["wpr_prediction"] = u.get("wpjp")
                if not row.get("toprate_rating"):
                    row["toprate_rating"] = u.get("trr")
                if not row.get("form_factor"):
                    row["form_factor"] = pfm_score_by_rid.get(run_id)

            if row.get("resulted") == "True":
                continue
            if found is None or found[1].get("f") is None:
                continue
            u = found[1]
            row["resulted"] = True
            row["finish_position"] = u.get("f")
            row["won"] = int(u.get("won") == 1)
            row["price_final"] = u.get("sp") if u.get("sp") is not None else row["price_at_pick"]
            n_filled += 1
        _write_log(path, log)
        print(f"  {path.name}: reconciled {n_filled} newly-resulted pick(s), "
              f"enriched {n_enriched} older row(s)")


def main():
    if not DATA_JSON.exists():
        print(f"speedmap_jockey_tracker: {DATA_JSON.name} not found, skipping")
        return
    with open(DATA_JSON) as f:
        data = json.load(f)
    pfm_rank_by_rid, pfm_score_by_rid = _load_pfm_lookup()

    print("Reconciling previously-logged picks...")
    reconcile_results(data, pfm_rank_by_rid, pfm_score_by_rid)
    print("Capturing today's new picks...")
    capture_new_picks(data, pfm_rank_by_rid, pfm_score_by_rid)


if __name__ == "__main__":
    main()
