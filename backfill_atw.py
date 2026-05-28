"""One-time backfill: fill wpr_actual from the result feed's `atw` field.

WHY
  wpr_actual used to be sourced from the form-history `wpr` column, which is
  the RAW run-day WPR. The actual we want is `atw` (weight-adjusted), which
  aligns to the projection's weight basis. `atw` only exists on the result
  feed (get_race_results), not in the form history. update_results() now
  captures atw for newly-resulted races, but already-resulted races still
  carry the old raw-wpr actuals. This script re-fetches results for every
  resulted race once and overwrites wpr_actual with atw.

USAGE
  python backfill_atw.py            # dry run: report only, writes nothing
  python backfill_atw.py --write    # actually update toprate_runners.csv

SAFE
  - Dry run by default.
  - Only touches wpr_actual (and recomputes wpr_actual_rank). No other column.
  - A race whose result feed lacks atw is left unchanged.
  - Backs up toprate_runners.csv to toprate_runners.csv.pre_atw_backfill before
    writing.
"""
import sys
import time
import shutil
import pandas as pd
import toprate_daily as td


def main():
    write = "--write" in sys.argv

    df = pd.read_csv(td.RUNNERS_CSV,
                     dtype={"run_id": str, "race_id": str},
                     low_memory=False)
    print(f"Loaded {len(df):,} runners across "
          f"{df['race_id'].nunique():,} races")

    for col in ["wpr_actual", "wpr_actual_rank"]:
        if col not in df.columns:
            df[col] = None

    resulted = df[df.get("resulted") == 1]
    race_ids = resulted["race_id"].dropna().astype(str).unique()
    print(f"{len(race_ids):,} resulted races to re-fetch for atw")

    jwt = td.login()

    # run_id -> atw across all re-fetched races
    atw_by_runid = {}
    n_fetched = n_with_atw = n_fail = 0
    t0 = time.time()
    for i, rid in enumerate(race_ids, 1):
        if i % 100 == 0:
            print(f"  ... {i}/{len(race_ids)} "
                  f"({time.time()-t0:.0f}s, {n_with_atw:,} runners with atw)")
        try:
            res = td.api_race_results(jwt, int(rid)) or {}
        except Exception as e:
            n_fail += 1
            continue
        runners = res.get("runners", []) if isinstance(res, dict) else []
        if not runners:
            continue
        n_fetched += 1
        for r in runners:
            run_id = str(r.get("runId", ""))
            atw = r.get("atw")
            if run_id and atw is not None:
                atw_by_runid[run_id] = round(float(atw), 1)
                n_with_atw += 1
        # token can expire on long runs; refresh hourly
        if i % 500 == 0:
            jwt = td.login()

    print(f"\nFetched {n_fetched:,} races, "
          f"{len(atw_by_runid):,} runners have atw, {n_fail} fetch failures "
          f"({time.time()-t0:.0f}s)")

    # apply atw to wpr_actual
    changed = 0
    for idx in df.index:
        run_id = str(df.at[idx, "run_id"])
        if run_id in atw_by_runid:
            new_val = atw_by_runid[run_id]
            old_val = df.at[idx, "wpr_actual"]
            if pd.isna(old_val) or round(float(old_val), 1) != new_val:
                df.at[idx, "wpr_actual"] = new_val
                changed += 1

    print(f"{changed:,} wpr_actual values would change to atw")
    print(f"wpr_actual non-null after: "
          f"{df['wpr_actual'].notna().sum():,}")

    # recompute wpr_actual_rank within each resulted race
    df["wpr_actual_rank"] = None
    ranked = 0
    for race_id, race in df[df.get("resulted") == 1].groupby("race_id"):
        actuals = race["wpr_actual"].dropna()
        if len(actuals) < 2:
            continue
        order = actuals.sort_values(ascending=False)
        for rk, i in enumerate(order.index, start=1):
            df.at[i, "wpr_actual_rank"] = rk
        ranked += 1
    print(f"{ranked:,} races re-ranked on atw")

    if not write:
        print("\nDRY RUN - nothing written. Re-run with --write to apply.")
        return

    backup = str(td.RUNNERS_CSV) + ".pre_atw_backfill"
    shutil.copy(td.RUNNERS_CSV, backup)
    print(f"\nBacked up to {backup}")
    df.to_csv(td.RUNNERS_CSV, index=False)
    print(f"Wrote {td.RUNNERS_CSV}")


if __name__ == "__main__":
    main()
