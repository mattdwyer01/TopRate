"""
wpr_race_speed_requantile_lean.py - patches race_speed_config.json's
y_quantiles WITHOUT a full retrain, since the model weights are unchanged
by this fix (only which predictions get quantiled). A full `train()`
run OOM-killed in this environment (hit ~14GB building both the 18,398-
race training set AND the 7,905-race held-out set as big DataFrames in
memory at once via race-speed_estimate.py's build_rows()).

This reuses the same memory-safe approach wpr_race_speed_calibration_
check.py already used successfully (looping estimate_race_speed() per
race with pmeans cached per day, not building one giant DataFrame up
front) over a large held-out sample (races on/after train()'s own
2026-03-01 test cutoff, so this is the genuinely out-of-sample period,
matching what pred_te would have been), then overwrites ONLY y_quantiles
in the existing config - features/medians/model weights untouched.

NO EM DASHES policy: hyphens only in this file.
"""
import json

import numpy as np
import pandas as pd

import race_speed_estimate as rse

FORM_CSV = "wpr_form_history.csv.gz"
TEST_CUTOFF = "2026-03-01"  # matches train()'s own date-based split
CONFIG_PATH = "race_speed_config.json"


def run():
    print("Loading model + form history...")
    rse._load_model()
    fh = rse._load_and_prep_form()
    fh = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"])
    fh["race_key"] = (fh["track"].astype(str) + "|" + fh["date"].astype(str)
                      + "|" + fh["raceNumber"].astype(str))

    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), rse_actual=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4]
    test_races = race_meta[race_meta["date"] >= pd.Timestamp(TEST_CUTOFF)]
    print(f"Held-out (test) races on/after {TEST_CUTOFF}: {len(test_races):,}")

    fh_by_race = fh.groupby("race_key")
    pmeans_by_date = {}
    predicted = []
    actual = []
    for i, (_, r) in enumerate(test_races.iterrows()):
        if i % 1000 == 0:
            print(f"  ... {i}/{len(test_races)}")
        day = r["date"].normalize()
        if day not in pmeans_by_date:
            pmeans_by_date[day] = rse._prior_means(fh, day)
        runners = fh_by_race.get_group(r["race_key"])
        try:
            res = rse.estimate_race_speed(runners, r["date"], fh, pmeans=pmeans_by_date[day])
        except Exception:
            continue
        predicted.append(res["predicted_rse"])
        actual.append(r["rse_actual"])

    predicted = np.array(predicted)
    actual = np.array(actual)
    print(f"\nScored {len(predicted):,} held-out races.")

    heldout_corr = float(np.corrcoef(predicted, actual)[0, 1])
    heldout_mae = float(np.abs(actual - predicted).mean())
    print(f"held-out correlation: {heldout_corr:+.3f}  (previous config: "
          f"{rse._CFG['heldout_corr']:+.3f})")
    print(f"held-out MAE: {heldout_mae:.3f}")

    hot, fast, even, slow = np.quantile(predicted, [0.10, 0.35, 0.65, 0.90])
    print(f"\nNew y_quantiles (fit on held-out predictions): "
          f"hot={hot:.4f} fast={fast:.4f} even={even:.4f} slow={slow:.4f}")
    print(f"Old y_quantiles: {rse._CFG['y_quantiles']}")

    from collections import Counter

    def label(p):
        if p <= hot:
            return "Slow"
        if p <= fast:
            return "Even"
        if p <= even:
            return "Fast"
        return "Hot"

    counts = Counter(label(p) for p in predicted)
    print(f"Label split under NEW thresholds (on this same held-out sample): {counts}")
    print(f"  as %: {{{', '.join(f'{k}: {v/len(predicted)*100:.0f}%' for k, v in counts.items())}}}")

    cfg = json.load(open(CONFIG_PATH))
    cfg["y_quantiles"] = {"hot": float(hot), "fast": float(fast),
                          "even": float(even), "slow": float(slow)}
    cfg["heldout_corr"] = heldout_corr
    with open(CONFIG_PATH, "w") as f:
        json.dump(cfg, f, indent=2)
    print(f"\nWrote updated y_quantiles to {CONFIG_PATH} (model weights untouched).")


if __name__ == "__main__":
    run()
