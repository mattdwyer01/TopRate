"""
backfill_atw_historical.py
---------------------------
Adds `atw` (TopRate's actual weight-adjusted WPR) to race_results_YYYY.csv.gz,
keyed by run_id. race_results_*.csv.gz's own `wpr` column is the RAW WFA
(weight-for-age) rating - confirmed directly against toprate.au by the user,
Sep 2026 (e.g. Grafton R1 7/9/2026, Latin Lights: WPR 73.0, ATW 72.4). For
future race prediction, a horse's WFA rating needs converting to what it
would be at the ACTUAL weight it carries (net of any apprentice claim) - atw
is TopRate's own precomputed answer to exactly that, so this backfill's job
is to capture it historically, not to reverse-engineer an approximation.

WHY A SEPARATE SCRIPT FROM backfill_atw.py
  backfill_atw.py already does something similar, but only for races that
  have a row in toprate_runners.csv (the live daily-fetch pipeline's own
  coverage window) and writes to that file's wpr_actual column. This script
  instead covers the FULL 10-year race_results_*.csv.gz backfill and writes
  a new `atw` column onto race_results_YYYY.csv.gz itself, keyed by run_id
  (confirmed 100% unique across all 1,346,041 rows in that dataset - unlike
  wpr_form_history.csv.gz's run_id, which is NOT a safe per-row key there,
  see build_training_frame's own wpr_nett-merge docstring for that history).

SCALE (Sep 2026 count, see chat)
  152,355 distinct races across 10 years -> 152,355 API calls for full
  coverage (one call per RACE via get_race_results, not per runner, and NOT
  per meeting like backfill_race_results.py's bulk endpoint - ~7.9x the call
  volume of that script's 19,320 meetings for the same date range).

PHASING (deliberately scoped smallest-clean-signal-first, not "--all" head on)
  weight_restriction=SW (Set Weight) + jockey_restriction="Apprentices Can
  Claim" is the cleanest subset for actually LEARNING the weight-to-rating
  relationship: Set Weight means every horse of the same age/sex carries the
  same base weight by race condition (unlike Handicap, where weight is
  ASSIGNED based on rating - a real confound for any regression using
  weightCarried as an input). With claims allowed, the only weight variation
  left is the claim itself - a clean, mostly-unconfounded signal. 27,816 of
  29,930 SW races allow claims (93%). Pure WFA-restriction races are far
  fewer (598) and almost never pair with claims (1/598) - not a useful
  primary source on their own.

  Use --restriction SW to start there (Phase 1, ~27,816 races once claim-
  filtered downstream in analysis - restriction filtering is done AT FETCH
  time on weight_restriction only, since jockey_restriction doesn't change
  which races need fetching, just which ones matter for the eventual fit).
  --restriction SW,WFA,HCP,... or --all for broader coverage once Phase 1
  has actually validated the signal is worth having broadly.

SAFETY (same lessons as backfill_race_results.py - see that module's own
SAFETY docstring for the full incident writeup this mirrors)
  - Fetch phase never touches race_results_YYYY.csv.gz or the checkpoint.
  - Checkpoint is committed ONLY inside the merge step, in the SAME git
    operation as the CSV writes - never as an earlier separate step (a
    checkpoint-then-separately-merge ordering already caused permanent data
    loss once in this codebase, see backfill_race_results.py's docstring).
  - --diagnose-one first: confirms get_race_results' real runner-list shape
    (which key holds run_id, which holds atw) before trusting a real run.

USAGE
  python backfill_atw_historical.py --diagnose-one 12345678
  python backfill_atw_historical.py --fetch-only atw.json --restriction SW --limit 50
  python backfill_atw_historical.py --merge-only atw.json --commit
"""
import argparse
import json
import shutil
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path

import pandas as pd

import toprate_daily as td

_DIR = Path(__file__).parent
CHECKPOINT_FILE = _DIR / "backfill_atw_historical.checkpoint"


def _race_results_path(year):
    return _DIR / f"race_results_{year}.csv.gz"


def fetch_race_atw(jwt, race_id):
    """{run_id: atw} for one race, via the same get_race_results RPC
    backfill_atw.py already validated. Returns {} on any missing/empty
    response rather than raising - the caller treats that as "no atw for
    this race" (still checkpointed, so a race genuinely without atw isn't
    endlessly retried)."""
    res = td.api_race_results(jwt, int(race_id)) or {}
    runners = res.get("runners", []) if isinstance(res, dict) else []
    out = {}
    for r in runners:
        run_id = str(r.get("runId", ""))
        atw = r.get("atw")
        if run_id and atw is not None:
            out[run_id] = round(float(atw), 1)
    return out


def diagnose_one(race_id):
    jwt = td.login()
    res = td.api_race_results(jwt, int(race_id)) or {}
    print(json.dumps(res, indent=2, default=str)[:6000])
    runners = res.get("runners", []) if isinstance(res, dict) else []
    print(f"\n{len(runners)} runners in response")
    for r in runners[:5]:
        print(f"  runId={r.get('runId')!r}  atw={r.get('atw')!r}  "
              f"horse={r.get('horseName') or r.get('horse')!r}")


def _select_race_ids(args):
    """race_id/date/weight_restriction from every race_results_*.csv.gz
    file on disk, deduped to one row per race. Filtered by --restriction
    (weight_restriction codes, comma-separated) unless --all, then by
    --since/--limit, minus whatever this script's own checkpoint already
    covers."""
    frames = []
    for f in sorted(_DIR.glob("race_results_*.csv.gz")):
        frames.append(pd.read_csv(
            f, usecols=["race_id", "date", "weight_restriction"],
            dtype={"race_id": str}, low_memory=False))
    if not frames:
        print("::error::No race_results_*.csv.gz files found - nothing to scope from.")
        sys.exit(1)
    races = pd.concat(frames, ignore_index=True).drop_duplicates(subset=["race_id"])

    if not args.all:
        restrictions = [r.strip() for r in (args.restriction or "").split(",") if r.strip()]
        if not restrictions:
            print("::error::One of --restriction, --all must be set - refusing to guess the scope.")
            sys.exit(1)
        races = races[races["weight_restriction"].isin(restrictions)]

    if args.since:
        races = races[races["date"] >= args.since]

    races = races.sort_values("date", ascending=False)
    race_ids = races["race_id"].tolist()

    checkpoint = set()
    if CHECKPOINT_FILE.exists():
        checkpoint = set(CHECKPOINT_FILE.read_text().split())
        print(f"  Resuming: {len(checkpoint):,} races already fetched per checkpoint")
    race_ids = [r for r in race_ids if r not in checkpoint]

    if args.limit:
        race_ids = race_ids[:args.limit]
    return race_ids


def run_fetch_phase(race_ids, workers):
    """Fetch every race_id, return {race_id: {run_id: atw}}. Does NOT
    touch the checkpoint (see module SAFETY docstring)."""
    jwt = td.login()
    n_ok = n_empty = n_fail = 0
    t0 = time.time()
    results = {}

    def _one(rid):
        try:
            return rid, fetch_race_atw(jwt, rid)
        except Exception:
            return rid, None

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(_one, rid): rid for rid in race_ids}
        done = 0
        for fut in as_completed(futures):
            done += 1
            if done % 500 == 0:
                elapsed = time.time() - t0
                rate = done / elapsed if elapsed else 0
                eta = (len(race_ids) - done) / rate if rate else float("nan")
                print(f"  ... {done}/{len(race_ids)} races "
                      f"({elapsed:.0f}s, ETA {eta:.0f}s)")
            rid, atw_map = fut.result()
            if atw_map is None:
                n_fail += 1
                continue
            if not atw_map:
                n_empty += 1
                continue
            n_ok += 1
            results[rid] = atw_map
            # Token can expire on long runs (same lesson backfill_atw.py's
            # own loop already applies) - _one closes over `jwt`, so
            # reassigning it here is picked up by any not-yet-started
            # queued call, no need to resubmit anything.
            if done % 500 == 0:
                jwt = td.login()

    print(f"\nFetch done in {time.time()-t0:.0f}s.")
    print(f"  races: {n_ok:,} with atw, {n_empty:,} empty/no atw, {n_fail:,} failed")
    print(f"  {sum(len(v) for v in results.values()):,} runner atw values collected")
    return results


def write_checkpoint(race_ids):
    """Union race_ids into CHECKPOINT_FILE. Call ONLY after merge_atw has
    successfully written the corresponding rows - a race with no atw in
    the response is ALSO checkpointed (empty dict still counts as
    "fetched") so it is not endlessly retried."""
    if not race_ids:
        return
    existing = set()
    if CHECKPOINT_FILE.exists():
        existing = set(CHECKPOINT_FILE.read_text().split())
    combined = existing | {str(r) for r in race_ids}
    CHECKPOINT_FILE.write_text("\n".join(sorted(combined)))
    print(f"  checkpoint: {len(combined) - len(existing):,} new race_ids added "
          f"({len(combined):,} total)")


def merge_atw(fetched, commit, backup=True):
    """fetched: {race_id: {run_id: atw}}. Unlike merge_race_results (which
    only APPENDS new rows), this UPDATES an existing atw column on
    race_results_YYYY.csv.gz by run_id - never overwrites a run_id's atw
    that's already on file (so a re-run with overlapping scope is a safe
    no-op for rows already merged, only fills genuinely new/missing
    values). Returns total run_ids updated across all years."""
    run_id_to_atw = {}
    for race_id, atw_map in fetched.items():
        run_id_to_atw.update(atw_map)
    if not run_id_to_atw:
        print("  no atw values to merge")
        return 0

    total_updated = 0
    for path in sorted(_DIR.glob("race_results_*.csv.gz")):
        existing = pd.read_csv(path, low_memory=False,
                               dtype={"race_id": str, "horse_id": str,
                                      "meeting_id": str, "run_id": str})
        if "atw" not in existing.columns:
            existing["atw"] = pd.NA

        mapped = existing["run_id"].map(run_id_to_atw)
        # Only fill rows that (a) have a fetched atw AND (b) don't already
        # have one on file - never clobber a value a prior merge already
        # wrote, even if this run's fetch happens to disagree (shouldn't,
        # atw is a settled post-race figure, but never overwrite silently).
        fillable = mapped.notna() & existing["atw"].isna()
        n_new = int(fillable.sum())
        if n_new == 0:
            continue
        existing.loc[fillable, "atw"] = mapped[fillable]
        total_updated += n_new
        print(f"  {path.name}: {n_new:,} run_ids newly filled with atw")

        if not commit:
            continue
        if backup:
            bkp = f"{path}.pre_atw_merge_{datetime.now():%Y%m%d_%H%M%S}"
            shutil.copy(path, bkp)
            print(f"    backed up to {bkp}")
        existing.to_csv(path, index=False)
        print(f"    wrote {path}")

    if not commit and total_updated:
        print("DRY RUN - nothing written. Pass --commit to save for real.")
    return total_updated


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--diagnose-one", metavar="RACE_ID", default=None)
    ap.add_argument("--restriction", default=None,
                    help="Comma-separated weight_restriction codes to scope to "
                         "(e.g. SW, or SW,WFA). Start with SW - see module docstring.")
    ap.add_argument("--all", action="store_true",
                    help="Every race on file regardless of weight_restriction "
                         "(152,355 races - only after --restriction SW has "
                         "validated the signal).")
    ap.add_argument("--since", default=None, help="YYYY-MM-DD date floor")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--fetch-only", metavar="OUTFILE", default=None)
    ap.add_argument("--merge-only", metavar="OUTFILE", default=None)
    ap.add_argument("--commit", action="store_true")
    args = ap.parse_args()

    if args.diagnose_one:
        diagnose_one(args.diagnose_one)
        return

    if args.merge_only:
        fetched = json.loads(Path(args.merge_only).read_text())
        n = merge_atw(fetched, commit=args.commit)
        if args.commit and n:
            write_checkpoint(list(fetched.keys()))
        return

    race_ids = _select_race_ids(args)
    print(f"{len(race_ids):,} races to fetch")
    if not race_ids:
        return
    fetched = run_fetch_phase(race_ids, args.workers)

    if args.fetch_only:
        Path(args.fetch_only).write_text(json.dumps(fetched))
        print(f"wrote {args.fetch_only}")
        return

    # Combined fetch+merge (local/manual use only - the GH Action always
    # uses the --fetch-only/--merge-only split, see module SAFETY docstring).
    n = merge_atw(fetched, commit=args.commit)
    if args.commit and n:
        write_checkpoint(list(fetched.keys()))


if __name__ == "__main__":
    main()
