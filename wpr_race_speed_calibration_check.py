"""
wpr_race_speed_calibration_check.py - user-flagged: "all races in the
dashboard are predicted to have a hot or fast race speed". Live label
distribution (toprate_data.json, 1,728 races) is Hot=48%/Fast=32%/
Even=16%/Slow=4%, vs the design intent baked into race_speed_config.json
(fit via train()'s "hot,fast,even,slow = quantile(pred_tr, [.10,.35,.65,
.90])") of roughly Slow=10%/Even=25%/Fast=30%/Hot=35%.

The quantile-order bug and the label-inversion bug (both real, both
already fixed per race_speed_estimate.py's own docstring history) are
NOT this - both would already show up as literally impossible splits
(100% one label, or a clean swap), not a skew in every DIRECTION of
severity like this. The remaining candidate, per the exact same failure
mode as the WPR base tiered regression: the quantile cutpoints were fit
on the model's TRAINING SET predictions (pred_tr), then applied to score
GENUINELY LIVE, out-of-sample predictions (estimate_race_speed(), called
by toprate_daily.py's compute_race_speed() for every race that gets
fetched). If the model's predictions on live/unseen races differ
systematically (level shift, not just narrower spread) from its own
predictions on the training rows it was fit to, the quantile buckets
computed from training predictions will not actually split live
predictions the way they were designed to.

METHOD: recompute estimate_race_speed()'s LIVE predicted_rse for a large
sample of real historical races (using the exact same call path
toprate_daily.py uses), and compare that distribution's own quantiles
directly against race_speed_config.json's stored y_quantiles (fit on
pred_tr, the training predictions) - a level shift or spread mismatch
between the two would confirm the same class of bug already fixed once
in wpr_projection.py's own base tiers.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import race_speed_estimate as rse

FORM_CSV = "wpr_form_history.csv.gz"
RUNNERS_CSV = "toprate_runners.csv"


def run():
    print("Loading config + model...")
    rse._load_model()
    cfg_q = rse._CFG["y_quantiles"]
    print(f"Stored config quantiles (fit on TRAINING predictions, pred_tr): {cfg_q}")

    print("\nLoading form history + runners...")
    fh = rse._load_form()
    rdf = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    rdf["distance"] = pd.to_numeric(rdf["distance"], errors="coerce")
    rdf["barrier"] = pd.to_numeric(rdf["barrier"], errors="coerce")
    rdf["date"] = pd.to_datetime(rdf["date"], errors="coerce")
    resulted = pd.to_numeric(rdf.get("resulted"), errors="coerce") == 1
    rdf = rdf[resulted].dropna(subset=["date"])

    # sample the most recent ~1500 races actually served (mirrors what
    # the live dashboard is showing right now), grouped by race_id
    race_ids = rdf.sort_values("date")["race_id"].drop_duplicates().tail(1500).tolist()
    print(f"Scoring {len(race_ids):,} real races via the LIVE estimate_race_speed() call path...")

    races_by_id = {rid: g for rid, g in rdf[rdf["race_id"].isin(race_ids)].groupby("race_id")}
    # pmeans only depends on race_date (see _prior_means docstring) - every
    # race on the same day shares one, so compute it once per unique date
    # instead of once per race (the exact inefficiency estimate_race_speed's
    # own docstring warns about for multi-race callers).
    pmeans_by_date = {}
    predicted = []
    labels = []
    for i, rid in enumerate(race_ids):
        if i % 300 == 0:
            print(f"  ... {i}/{len(race_ids)}")
        race = races_by_id.get(rid)
        if race is None or len(race) < 4:
            continue
        race_date = race["date"].iloc[0]
        if race_date not in pmeans_by_date:
            pmeans_by_date[race_date] = rse._prior_means(fh, race_date)
        try:
            res = rse.estimate_race_speed(race, race_date, fh, pmeans=pmeans_by_date[race_date])
        except Exception:
            continue
        predicted.append(res["predicted_rse"])
        labels.append(res["label"])

    predicted = np.array(predicted)
    print(f"\nScored {len(predicted):,} races live.")
    print(f"\nLIVE predicted_rse distribution:")
    print(f"  min={predicted.min():.3f}  p10={np.percentile(predicted,10):.3f}  "
          f"p35={np.percentile(predicted,35):.3f}  p50={np.percentile(predicted,50):.3f}  "
          f"p65={np.percentile(predicted,65):.3f}  p90={np.percentile(predicted,90):.3f}  "
          f"max={predicted.max():.3f}")
    print(f"\nSTORED CONFIG quantiles (from training-set pred_tr):")
    print(f"  hot(p10)={cfg_q['hot']:.3f}  fast(p35)={cfg_q['fast']:.3f}  "
          f"even(p65)={cfg_q['even']:.3f}  slow(p90)={cfg_q['slow']:.3f}")

    from collections import Counter
    print(f"\nLive label distribution (n={len(labels)}): {Counter(labels)}")
    print(f"  as %: {{{', '.join(f'{k}: {v/len(labels)*100:.0f}%' for k,v in Counter(labels).items())}}}")

    print(f"\nWhat live predicted_rse quantiles WOULD produce if used as thresholds instead:")
    live_hot, live_fast, live_even, live_slow = np.percentile(predicted, [10, 35, 65, 90])
    print(f"  hot(p10)={live_hot:.3f}  fast(p35)={live_fast:.3f}  "
          f"even(p65)={live_even:.3f}  slow(p90)={live_slow:.3f}")

    print("\nIf the live quantiles above differ substantially from the stored config quantiles, "
          "that confirms a level-shift/mismatch between the model's training-set predictions "
          "(what the thresholds were calibrated on) and its live out-of-sample predictions "
          "(what's actually being bucketed) - the same class of bug as the WPR base tiers, "
          "just in a different subsystem.")


if __name__ == "__main__":
    run()
