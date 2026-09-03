"""
wpr_race_speed_true_calibration.py - the actual root-cause fix. Traced
the "all Hot/Fast" symptom through three layers:
  1. Quantile thresholds were fit on the model's TRAINING predictions
     (pred_tr) instead of held-out predictions (pred_te) - real bug,
     fixed in race_speed_estimate.py.
  2. Suspected temporal drift within the held-out period - recalibrated
     to a recent window. Did NOT actually fix anything in production
     (verified via the real backfill: Hot stayed ~50% every month).
  3. ROOT CAUSE: all prior calibration attempts scored races by
     enumerating them from wpr_form_history.csv.gz's own race_key
     grouping (track|date|raceNumber). That population does NOT match
     what's actually served (toprate_runners.csv's own race_id
     population) - confirmed directly: August 2026 has 1,547 races in
     toprate_runners.csv vs only 1,083 in wpr_form_history.csv.gz's own
     grouping, with just 930 exact matches. The mismatched races are
     disproportionately synthetic/all-weather meetings under different
     name strings (e.g. "Gold Coast Poly" vs "Gold Coast"). A single
     race scored via EITHER path gives an IDENTICAL prediction (verified
     directly, race_id 1756812) - this was never a feature-computation
     bug, purely a "calibrated the thresholds against the wrong sample
     of races" bug.

FIX: fit quantile thresholds directly from estimate_race_speed()
predictions on toprate_runners.csv's own race population (the real
served population), with a genuine chronological hold-out split (not
just eyeballing the fit set) to confirm the calibration generalizes.

NO EM DASHES policy: hyphens only in this file.
"""
import time
from collections import Counter

import numpy as np
import pandas as pd

import race_speed_estimate as rse
from toprate_daily import load_runners, save_runners

CONFIG_PATH = "race_speed_config.json"
FIT_FRACTION = 0.70  # matches train()'s own 70/30 convention


def score_all(runners_df, fh):
    resulted_mask = pd.to_numeric(runners_df.get("resulted"), errors="coerce") == 1
    runners_df["date"] = pd.to_datetime(runners_df["date"], errors="coerce")
    target = runners_df[resulted_mask & runners_df["date"].notna()]
    race_groups = list(target.groupby("race_id"))
    n_races = len(race_groups)
    print(f"Scoring {n_races:,} real races via the LIVE estimate_race_speed() call path...")

    t0 = time.time()
    pmeans_by_date = {}
    rows = []  # (race_id, date, predicted_rse)
    for gi, (race_id, race) in enumerate(race_groups):
        if gi > 0 and gi % 1000 == 0:
            elapsed = time.time() - t0
            eta = elapsed / gi * (n_races - gi)
            print(f"  ... {gi:,}/{n_races:,} ({elapsed:.0f}s elapsed, ~{eta:.0f}s remaining)")
        race_date = race["date"].iloc[0]
        day = race_date.normalize()
        if day not in pmeans_by_date:
            pmeans_by_date[day] = rse._prior_means(fh, day)
        try:
            res = rse.estimate_race_speed(race, race_date, fh, pmeans=pmeans_by_date[day])
        except Exception:
            continue
        rows.append((race_id, race_date, res["predicted_rse"]))
    print(f"Scored {len(rows):,} races in {time.time()-t0:.0f}s.")
    return pd.DataFrame(rows, columns=["race_id", "date", "predicted_rse"])


def label_of(p, hot, fast, even, slow):
    if p <= hot:
        return "Slow"
    if p <= fast:
        return "Even"
    if p <= even:
        return "Fast"
    return "Hot"


def run():
    print("Loading model + form history...")
    rse._load_model()
    fh = rse._load_form()

    print("Loading runners_df...")
    runners_df = load_runners()
    scored = score_all(runners_df, fh)
    scored = scored.sort_values("date").reset_index(drop=True)

    cut = int(len(scored) * FIT_FRACTION)
    fit_set = scored.iloc[:cut]
    check_set = scored.iloc[cut:]
    print(f"\nFit set: {len(fit_set):,} races ({fit_set['date'].min().date()} to "
          f"{fit_set['date'].max().date()})")
    print(f"Check set (held out): {len(check_set):,} races ({check_set['date'].min().date()} to "
          f"{check_set['date'].max().date()})")

    hot, fast, even, slow = np.quantile(fit_set["predicted_rse"], [0.10, 0.35, 0.65, 0.90])
    print(f"\nNew y_quantiles (fit on toprate_runners.csv's own real population): "
          f"hot={hot:.4f} fast={fast:.4f} even={even:.4f} slow={slow:.4f}")

    fit_labels = Counter(label_of(p, hot, fast, even, slow) for p in fit_set["predicted_rse"])
    check_labels = Counter(label_of(p, hot, fast, even, slow) for p in check_set["predicted_rse"])
    print(f"\nLabel split on FIT set (n={len(fit_set):,}): {dict(fit_labels)}")
    print(f"  as %: {{{', '.join(f'{k}: {v/len(fit_set)*100:.0f}%' for k, v in fit_labels.items())}}}")
    print(f"\nLabel split on HELD-OUT check set (n={len(check_set):,}): {dict(check_labels)}")
    print(f"  as %: {{{', '.join(f'{k}: {v/len(check_set)*100:.0f}%' for k, v in check_labels.items())}}}")

    print("\nIf the held-out split is close to the fit split (both near the ~35/30/25/10% design "
          "intent), the calibration genuinely generalizes this time - unlike the wpr_form_history.csv.gz "
          "-based attempts, which looked right on their own fit population but never matched what's "
          "actually served.")

    import json
    cfg = json.load(open(CONFIG_PATH))
    cfg["y_quantiles"] = {"hot": float(hot), "fast": float(fast),
                          "even": float(even), "slow": float(slow)}
    with open(CONFIG_PATH, "w") as f:
        json.dump(cfg, f, indent=2)
    print(f"\nWrote updated y_quantiles to {CONFIG_PATH}.")

    print("\nBackfilling rs_score/rs_label for all resulted races with the new thresholds...")
    scored_map = {rid: p for rid, p in zip(scored["race_id"], scored["predicted_rse"])}
    for col in ["rs_score", "rs_label"]:
        if col not in runners_df.columns:
            runners_df[col] = None
    resulted_mask = pd.to_numeric(runners_df.get("resulted"), errors="coerce") == 1
    for race_id, p in scored_map.items():
        label = label_of(p, hot, fast, even, slow)
        score = float(rse._score_from_rse(p))
        idx = runners_df.index[(runners_df["race_id"] == race_id) & resulted_mask]
        runners_df.loc[idx, "rs_score"] = round(score, 3)
        runners_df.loc[idx, "rs_label"] = label

    final_labels = Counter(runners_df.loc[resulted_mask, "rs_label"].dropna())
    print(f"Final all-resulted-rows label distribution: {dict(final_labels)}")
    total = sum(final_labels.values())
    print(f"  as %: {{{', '.join(f'{k}: {v/total*100:.0f}%' for k, v in final_labels.items())}}}")

    save_runners(runners_df)
    print("Saved toprate_runners.csv")


if __name__ == "__main__":
    run()
