"""One-time backfill: pull Form Factor Score/Rank (pfm_score, pfm_score_rank)
for races already in toprate_runners.csv, going back N days.

WHY
  toprate_daily.py only started capturing pfm_score/pfm_score_rank from
  get_race_detail going forward (21 Aug 2026). Every race fetched before
  that has run_id rows with the columns blank. get_race_detail is a
  per-race call (not per-runner), so this re-fetches it once per race
  still in the lookback window and fills in every runner in that race from
  the one response.

  UNVERIFIED ASSUMPTION: whether TopRate's API still returns full field
  data for a RESULTED (already-run) race, or only for races that haven't
  jumped yet. This script finds out empirically - if get_race_detail comes
  back empty for old resulted races, that will show up immediately as a
  near-zero fill rate in the first handful of races, and the run should be
  stopped (ctrl-C) rather than ground through the whole window for nothing.

USAGE
  python backfill_pfm_score.py                # last 30 days, dry run
  python backfill_pfm_score.py --days 14       # different window
  python backfill_pfm_score.py --write         # actually update the CSV

SAFE
  - Dry run by default.
  - Only ever fills pfm_score/pfm_score_rank where they are currently
    blank - never overwrites a value the daily pipeline already captured.
  - Backs up toprate_runners.csv before writing.
  - Skips races with no runners currently blank (nothing to gain from
    re-fetching them).

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import shutil
import time

import pandas as pd

import toprate_daily as td


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--days", type=int, default=30,
                    help="how many days back to backfill (default 30)")
    ap.add_argument("--write", action="store_true",
                    help="actually update toprate_runners.csv (default: dry run)")
    args = ap.parse_args()

    df = pd.read_csv(td.RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                     low_memory=False)
    print(f"Loaded {len(df):,} runners across {df['race_id'].nunique():,} races")

    for col in ["pfm_score", "pfm_score_rank"]:
        if col not in df.columns:
            df[col] = pd.NA

    # Parse into a separate series for the window filter only - df["date"]
    # itself stays as the original string so the CSV format is untouched
    # when we save later.
    parsed_date = pd.to_datetime(df["date"], errors="coerce")
    cutoff = pd.Timestamp.now().normalize() - pd.Timedelta(days=args.days)
    in_window = df[parsed_date >= cutoff]
    print(f"{len(in_window):,} runners in the last {args.days} days "
          f"(since {cutoff.date()})")

    # Only races that still have at least one runner missing pfm_score -
    # no point re-fetching a race the daily pipeline already fully captured.
    missing_mask = in_window["pfm_score"].isna()
    races_needing = in_window.loc[missing_mask, "race_id"].dropna().unique()
    print(f"{len(races_needing):,} races have at least one runner missing "
          f"pfm_score - these will be re-fetched")
    if len(races_needing) == 0:
        print("Nothing to backfill.")
        return

    jwt = td.login()

    pfm_by_runid = {}
    n_fetched = n_empty = n_fail = 0
    t0 = time.time()
    for i, rid in enumerate(races_needing, 1):
        if i % 50 == 0 or i == 1:
            elapsed = time.time() - t0
            print(f"  ... {i}/{len(races_needing)} races "
                  f"({elapsed:.0f}s, {len(pfm_by_runid):,} runners filled so far, "
                  f"{n_empty} races returned empty, {n_fail} failed)")
        try:
            detail = td.api_race_detail(jwt, int(rid)) or []
        except Exception as e:
            n_fail += 1
            if n_fail <= 5:
                print(f"  ! race {rid} fetch failed: {e}")
            continue
        if not detail:
            n_empty += 1
            continue
        n_fetched += 1
        for d in detail:
            run_id = str(d.get("runId", ""))
            score = d.get("pfmScore")
            rank = d.get("pfmScoreRank")
            if run_id and (score is not None or rank is not None):
                pfm_by_runid[run_id] = (score, rank)
        # token can expire on a long run; refresh hourly (roughly every
        # 500-800 races at TopRate's per-request pace)
        if i % 500 == 0:
            jwt = td.login()

        # First 10 races: bail early and loudly if EVERY one comes back
        # empty - almost certainly means the API does not serve field data
        # for resulted races, and grinding through the rest is pointless.
        if i == 10 and n_fetched == 0:
            print("\n  ALL of the first 10 races returned empty field data.")
            print("  This strongly suggests get_race_detail does not serve")
            print("  resulted/past races - stopping early rather than")
            print(f"  burning the rest of the {len(races_needing):,}-race window.")
            break

    print(f"\nFetched {n_fetched:,} races with data, {n_empty:,} empty, "
          f"{n_fail:,} failed ({time.time()-t0:.0f}s)")
    print(f"{len(pfm_by_runid):,} runners have a pfm_score/pfm_score_rank to apply")

    if not pfm_by_runid:
        print("Nothing to apply. Exiting without writing.")
        return

    changed = 0
    for idx in df.index:
        run_id = str(df.at[idx, "run_id"])
        if run_id in pfm_by_runid and pd.isna(df.at[idx, "pfm_score"]):
            score, rank = pfm_by_runid[run_id]
            df.at[idx, "pfm_score"] = score
            df.at[idx, "pfm_score_rank"] = rank
            changed += 1

    print(f"{changed:,} rows would be filled")
    print(f"pfm_score non-null after: {df['pfm_score'].notna().sum():,} "
          f"/ {len(df):,} total runners")

    if not args.write:
        print("\nDRY RUN - nothing written. Re-run with --write to apply.")
        return

    backup = str(td.RUNNERS_CSV) + ".pre_pfm_backfill"
    shutil.copy(td.RUNNERS_CSV, backup)
    print(f"\nBacked up to {backup}")
    td.save_runners(df)
    print(f"Wrote {td.RUNNERS_CSV}")


if __name__ == "__main__":
    main()
