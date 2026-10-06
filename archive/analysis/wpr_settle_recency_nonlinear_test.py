"""
wpr_settle_recency_nonlinear_test.py - two more candidates for the settling
estimate, continuing the "keep refining until reliable" push. Both reuse
the exact data pipeline already built and validated today (load_and_prep,
add_trailing_run_style, add_trailing_sect_early, add_race_relative_sect_rank)
- no new plumbing, just testing whether more can be squeezed from the
same ingredients (or one new, cheap one).

CANDIDATE 1: recency-weighted tendency. The shipped model uses a flat
ALL-TIME mean of a horse's own relative settle. A horse maturing
tactically, or a stable change in riding instructions, shows up in RECENT
runs before it moves a flat all-time average. Tests a last-5-run trailing
mean, and a blend of it with the all-time mean, against the all-time-only
baseline (with barrier_nudge + sect_nudge held fixed - already validated -
so only the tendency ingredient itself is being tested).

CANDIDATE 2: non-linear combination. Everything shipped so far combines
(tendency, draw_signal, sect_signal) with a straight-line formula. Fits a
small LightGBM regressor on the SAME three inputs (plus last-5 mean and
field_size) to predict actual_rel directly - tests whether the linear
form is leaving real accuracy on the table, independent of adding any new
information.

Both tested bidirectionally, same bar as everything else today.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import settling_estimate as se
from wpr_settle_barrier_nudge_calibration_test import load_and_prep, add_trailing_run_style, verify_against_slow_method
from wpr_settle_sectional_test import add_trailing_sect_early, add_race_relative_sect_rank


def add_last5_tendency(fh):
    """Trailing (strictly prior) mean relative settle over a horse's last
    5 runs only, via groupby-rolling-shift - same efficiency discipline
    (verified, not assumed) as add_trailing_run_style's all-time version."""
    settle = fh["positionSettled"]
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)
    fh["_rel_for_roll"] = rel_valid
    g = fh.groupby("horse_lc")["_rel_for_roll"]
    fh["last5_tendency"] = g.transform(lambda s: s.rolling(5, min_periods=1).mean().shift(1))
    fh = fh.drop(columns=["_rel_for_roll"])
    return fh


def verify_last5_against_slow(fh, n_check=20):
    """Same discipline as verify_against_slow_method - spot-check against
    an obviously-correct (if slow) reference before trusting at scale."""
    sample = fh[fh["last5_tendency"].notna()].sample(n=min(n_check, len(fh)), random_state=7)
    max_diff = 0.0
    for _, row in sample.iterrows():
        prior = fh[(fh["horse_lc"] == row["horse_lc"]) & (fh["date"] < row["date"])].tail(5)
        settle = prior["positionSettled"]
        fs = prior["field_size"]
        valid = (settle > 0) & (fs > 0)
        rel = (settle[valid] / fs[valid]).clip(0, 1)
        if len(rel) == 0:
            continue
        slow_val = float(rel.mean())
        diff = abs(slow_val - row["last5_tendency"])
        max_diff = max(max_diff, diff)
    print(f"  last5 verification: max |fast - slow| over {len(sample)} spot-checks = {max_diff:.6f}")
    if max_diff > 1e-6:
        raise RuntimeError("last5_tendency does not match the slow reference - do not trust results.")


def fit_ols(X, y):
    coef, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def run():
    print("Loading and preparing form history...")
    fh = load_and_prep()
    fh = add_trailing_run_style(fh)
    verify_against_slow_method(fh)
    fh = add_trailing_sect_early(fh)
    fh = add_race_relative_sect_rank(fh)
    fh = add_last5_tendency(fh)
    verify_last5_against_slow(fh)
    print(f"  last5_tendency coverage: {fh['last5_tendency'].notna().mean()*100:.1f}%")

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    fh["sect_signal"] = (fh["sect_rank_in_race"] - 0.5) * 2

    usable = fh.dropna(subset=["run_style_tendency", "actual_rel", "draw_signal",
                               "sect_signal", "last5_tendency"]).copy()
    print(f"\nUsable rows (all ingredients present): {len(usable):,}")

    q70, q85 = usable["date"].quantile([0.70, 0.85])
    trn_a = usable[usable["date"] < q70]
    te_a = usable[usable["date"] >= q85]
    q30, q15 = usable["date"].quantile([0.30, 0.15])
    trn_b = usable[usable["date"] > q30]
    te_b = usable[usable["date"] <= q15]

    # Current shipped formula, exactly (fixed coefficients, not refit here -
    # this run's baseline must match what's actually live).
    def shipped_predict(frame):
        nudge = frame["draw_signal"] * se.SECT_NUDGE_DRAW_SLOPE + frame["sect_signal"] * se.SECT_NUDGE_COEF
        return (frame["run_style_tendency"] + nudge).clip(0, 1)

    print("\n=== CANDIDATE 1: recency-weighted tendency ===")
    for direction, (trn, te) in [("A (forward)", (trn_a, te_a)), ("B (reversed)", (trn_b, te_b))]:
        base_mae = (shipped_predict(te) - te["actual_rel"]).abs().mean()

        # last5-only: same nudge, swap in last5_tendency for run_style_tendency
        pred_last5 = (te["last5_tendency"] + te["draw_signal"] * se.SECT_NUDGE_DRAW_SLOPE
                     + te["sect_signal"] * se.SECT_NUDGE_COEF).clip(0, 1)
        mae_last5 = (pred_last5 - te["actual_rel"]).abs().mean()

        # blended: fit the blend weight on trn (alpha*all_time + (1-alpha)*last5)
        Xb = np.column_stack([trn["run_style_tendency"], trn["last5_tendency"]])
        yb = trn["actual_rel"] - (trn["draw_signal"] * se.SECT_NUDGE_DRAW_SLOPE
                                  + trn["sect_signal"] * se.SECT_NUDGE_COEF)
        alpha, beta = fit_ols(Xb, yb)
        pred_blend = (te["run_style_tendency"] * alpha + te["last5_tendency"] * beta
                     + te["draw_signal"] * se.SECT_NUDGE_DRAW_SLOPE
                     + te["sect_signal"] * se.SECT_NUDGE_COEF).clip(0, 1)
        mae_blend = (pred_blend - te["actual_rel"]).abs().mean()

        print(f"  direction {direction}: n_te={len(te):,}  "
              f"shipped(all-time) MAE={base_mae:.4f}  "
              f"last5-only MAE={mae_last5:.4f} ({mae_last5 - base_mae:+.4f})  "
              f"blend(alpha={alpha:.2f},beta={beta:.2f}) MAE={mae_blend:.4f} ({mae_blend - base_mae:+.4f})")

    print("\n=== CANDIDATE 2: non-linear (LightGBM) combination of the SAME inputs ===")
    features = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal", "field_size"]
    for direction, (trn, te) in [("A (forward)", (trn_a, te_a)), ("B (reversed)", (trn_b, te_b))]:
        base_mae = (shipped_predict(te) - te["actual_rel"]).abs().mean()
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(trn[features], trn["actual_rel"])
        pred = model.predict(te[features])
        mae_lgb = mean_absolute_error(te["actual_rel"], pred)
        print(f"  direction {direction}: n_trn={len(trn):,} n_te={len(te):,}  "
              f"shipped(linear) MAE={base_mae:.4f}  LightGBM MAE={mae_lgb:.4f} "
              f"({mae_lgb - base_mae:+.4f}, {'better' if mae_lgb < base_mae else 'worse'})")

    print("\nDone.")


if __name__ == "__main__":
    run()
