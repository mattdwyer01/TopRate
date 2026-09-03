"""
wpr_race_speed_backfill_labels.py - backfills rs_score/rs_label for every
resulted race in toprate_runners.csv under the corrected calibration
(pred_te instead of pred_tr, recency-restricted to May 2026 onward - see
race_speed_estimate.py's _tempo_label/train() docstrings for the full
history). compute_race_speed() in toprate_daily.py only ever touches
TODAY's races (same "only touch today" pattern already found and fixed
for wprp_proj/wprp_edge this session) - past races' rs_label/rs_score
are frozen at whatever was live on the day they were originally fetched,
so this fix would otherwise never show up for any already-resulted race
on the dashboard.

Memory-safe by construction: loops per race with pmeans cached per day
(same approach wpr_race_speed_calibration_check.py/wpr_race_speed_
requantile_lean.py already used successfully) rather than building one
giant DataFrame up front the way race_speed_estimate.py's own train()
does - that OOM-killed in this environment at ~14GB.

Does NOT touch wprp_proj/wprp_edge or anything from the base-tier fix -
entirely separate columns (rs_score/rs_label), no interaction risk.

USAGE
  python wpr_race_speed_backfill_labels.py

Writes toprate_runners.csv in place. Does NOT rebuild toprate_data.json -
run toprate_daily.py's rebuild_html() (or --rebuild-only) separately after.

NO EM DASHES policy: hyphens only in this file.
"""
import time

import pandas as pd

import race_speed_estimate as rse
from toprate_daily import load_runners, save_runners


def run():
    print("Loading runners_df...")
    runners_df = load_runners()
    for col in ["rs_score", "rs_label"]:
        if col not in runners_df.columns:
            runners_df[col] = None

    resulted_mask = pd.to_numeric(runners_df.get("resulted"), errors="coerce") == 1
    runners_df["date"] = pd.to_datetime(runners_df["date"], errors="coerce")
    target = runners_df[resulted_mask & runners_df["date"].notna()]
    print(f"Resulted rows to backfill: {len(target):,} across "
          f"{target['race_id'].nunique():,} races")

    print("Loading form history (once)...")
    fh = rse._load_form()

    race_groups = list(target.groupby("race_id"))
    n_races = len(race_groups)
    t0 = time.time()
    pmeans_by_date = {}
    done = 0
    errors = 0

    for gi, (race_id, race) in enumerate(race_groups):
        if gi > 0 and gi % 500 == 0:
            elapsed = time.time() - t0
            eta = elapsed / gi * (n_races - gi)
            print(f"  ... {gi:,}/{n_races:,} races ({elapsed:.0f}s elapsed, ~{eta:.0f}s remaining)")
        race_date = race["date"].iloc[0]
        day = race_date.normalize()
        if day not in pmeans_by_date:
            pmeans_by_date[day] = rse._prior_means(fh, day)
        try:
            res = rse.estimate_race_speed(race, race_date, fh, pmeans=pmeans_by_date[day])
        except Exception as e:
            errors += 1
            continue
        idx = race.index
        runners_df.loc[idx, "rs_score"] = res.get("score")
        runners_df.loc[idx, "rs_label"] = res.get("label")
        done += 1

    elapsed = time.time() - t0
    print(f"\nDone in {elapsed:.0f}s: {done:,} races backfilled, {errors:,} errors, "
          f"across {n_races:,} races")

    from collections import Counter
    new_labels = runners_df.loc[resulted_mask, "rs_label"].dropna()
    counts = Counter(new_labels)
    print(f"New label distribution across all resulted rows: {counts}")
    total = sum(counts.values())
    print(f"  as %: {{{', '.join(f'{k}: {v/total*100:.0f}%' for k, v in counts.items())}}}")

    save_runners(runners_df)
    print("Saved toprate_runners.csv")


if __name__ == "__main__":
    run()
