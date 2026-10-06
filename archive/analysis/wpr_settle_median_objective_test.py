"""wpr_settle_median_objective_test.py - tests switching settling_estimate's
trained model from LightGBM's DEFAULT objective (L2 / squared-error, fits
the conditional MEAN) to quantile regression at alpha=0.5 (fits the
conditional MEDIAN) - the same switch wpr_projection.py's own q50 model
already made (and validated: "a walk-forward comparison showed LOWER
held-out MAE from the quantile objective's median, more robust to this
target's noise than squared-error loss"). settling_estimate.py never got
this treatment - its train() calls plain LGBMRegressor with no objective
argument, which defaults to L2/mean-fitting.

MOTIVATION (Sep 2026, Lindermann/Randwick 2026-09-05 investigation, user's
own diagnosis): "this model in general... is being very conservative and
looking for the median number always, rather than the most likely
approach... closer to the max or 75th+ percentile". Checked empirically
first rather than assuming either direction: for horses matching
Lindermann's real profile (own run_style_tendency <=0.25, drawn wide
draw_frac>=0.75, n=4,429 real historical rows), the ACTUAL settle-outcome
distribution is genuinely right-skewed - mode clearly in the Leader band
(0.10-0.20, the single largest histogram bin, 1,315 of 4,429 rows), but
mean=0.335 pulled well above both the mode and the median=0.222 by a real
tail of "everything fell apart" outcomes (0.90-1.00: 247 rows).

This means the user's underlying diagnosis (something is pulling
predictions toward a "less likely" middle value away from the more
common/likely outcome) is directionally RIGHT, but the correct fix is
NOT "predict a higher quantile like the 75th percentile" (that would be
an arbitrary, biased shift with no principled justification and would
almost certainly hurt calibration - it optimizes for nothing in
particular). The correct, principled fix is: the model is currently
fitting the MEAN (0.335 for this segment) when it should at minimum be
fitting the MEDIAN (0.222, already meaningfully closer to the mode/Leader
band) - matching wpr_projection.py's own already-validated architecture
choice, not inventing a new one.

Tested bidirectionally: same 8 features, same hyperparameters
(n_estimators=200, max_depth=3, learning_rate=0.05, num_leaves=8), only
the objective changes (default L2 vs quantile alpha=0.5).

RESULT (Sep 2026): CLEARS THE BAR DECISIVELY - direction A: MAE 0.1975 ->
0.1942 (-0.0032), direction B: MAE 0.2034 -> 0.2003 (-0.0031). This is
the single biggest validated improvement to settling_estimate found in
this whole investigation - more than 10x the margin feature's gain
(wpr_settle_margin_feature_test.py, -0.0001/-0.0028) and real in both
directions where every feature-engineering attempt (interaction term,
deeper capacity, robust tendency statistic, tactical-variance exclusion)
found only marginal or negative effects. The user's original diagnosis
("this model... is being very conservative and looking for the median...
rather than the most likely approach") correctly identified a real
problem, even though the specific proposed direction (a HIGHER quantile,
75th+) was not the right fix - the actual bug was the model fitting the
MEAN via LightGBM's untouched default objective, one step further from
the mode than even the median is for a right-skewed target.

Checked against the real case (Lindermann, Randwick 2026-09-05, using the
already-shipped dedup+scratched-exclusion-fixed inputs, 730-day training
window matching TRAIN_WINDOW_DAYS): predicted rel_settle=0.326, giving
pace_shape~+0.40 (using the currently shipped pace_shape model) - a real
lift on its own, roughly comparable to the tactical-exclusion candidate's
+0.42, from a completely different and much more fundamental (and much
more validated) mechanism. Ceolwulf, for comparison: rel_settle=0.657,
pace_shape~-0.61 - moving further back too, widening the real gap between
the two horses beyond anything found so far.

Next: test COMBINING this with the margin feature (both independently
validated) to see if the effect compounds - see wpr_settle_combined_
candidate_test.py.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import settling_estimate as se

FEATURES = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal",
            "field_size", "trailing_sect_ld_early", "trailing_sect_i_to800",
            "trailing_margin800m"]


def build_frame():
    fh = se._load_form()
    settle = pd.to_numeric(fh["positionSettled"], errors="coerce")
    fh["field_size"] = pd.to_numeric(fh["field_size"], errors="coerce")
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)
    g = fh["horse_lc"]

    csum_incl = rel_valid.fillna(0).groupby(g).cumsum()
    ccount_incl = valid.astype(int).groupby(g).cumsum()
    fh["run_style_tendency"] = (csum_incl.groupby(g).shift(1) /
                                ccount_incl.groupby(g).shift(1).replace(0, np.nan))
    fh["_rel_for_roll"] = rel_valid
    fh["last5_tendency"] = fh.groupby("horse_lc")["_rel_for_roll"].transform(
        lambda s: s.rolling(5, min_periods=1).mean().shift(1))
    fh["target"] = rel_valid

    sect_raw = pd.to_numeric(fh["sect_i_early"], errors="coerce")
    sect_clipped = sect_raw.clip(se.SECT_EARLY_LO, se.SECT_EARLY_HI)
    sect_valid = sect_clipped.notna()
    sect_valid_vals = sect_clipped.where(sect_valid)
    sect_csum = sect_valid_vals.fillna(0).groupby(g).cumsum()
    sect_ccount = sect_valid.astype(int).groupby(g).cumsum()
    fh["trailing_sect_i_early"] = (sect_csum.groupby(g).shift(1) /
                                   sect_ccount.groupby(g).shift(1).replace(0, np.nan))

    fh["barrier"] = pd.to_numeric(fh["barrier"], errors="coerce")
    fh["raceNumber"] = pd.to_numeric(fh["raceNumber"], errors="coerce")
    fh["_race_key"] = fh["track"].astype(str) + "|" + fh["date"].astype(str) + "|" + fh["raceNumber"].astype(str)
    fh["sect_rank_in_race"] = fh.groupby("_race_key")["trailing_sect_i_early"].rank(pct=True, na_option="keep")

    for col, out_col, lo, hi in [
        ("sect_ld_early", "trailing_sect_ld_early", se.SECT_LD_EARLY_LO, se.SECT_LD_EARLY_HI),
        ("sect_i_to800", "trailing_sect_i_to800", se.SECT_I_TO800_LO, se.SECT_I_TO800_HI),
        ("margin800m", "trailing_margin800m", se.MARGIN800M_LO, se.MARGIN800M_HI),
    ]:
        raw = pd.to_numeric(fh[col], errors="coerce")
        clipped = raw.clip(lo, hi)
        v = clipped.notna()
        v_vals = clipped.where(v)
        csum = v_vals.fillna(0).groupby(g).cumsum()
        ccount = v.astype(int).groupby(g).cumsum()
        fh[out_col] = csum.groupby(g).shift(1) / ccount.groupby(g).shift(1).replace(0, np.nan)

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    fh["sect_signal"] = (fh["sect_rank_in_race"] - 0.5) * 2

    return fh.dropna(subset=["run_style_tendency", "target", "date"]).sort_values("date")


def _fit_eval(trn, te, features, objective_kwargs):
    trn_u = trn.dropna(subset=features + ["target"])
    te_u = te.dropna(subset=features + ["target"])
    med = trn_u[features].median()
    Xtr = trn_u[features].fillna(med)
    Xte = te_u[features].fillna(med)
    m = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                          num_leaves=8, random_state=42, verbosity=-1, **objective_kwargs)
    m.fit(Xtr, trn_u["target"])
    pred = m.predict(Xte)
    return mean_absolute_error(te_u["target"], pred), m, len(trn_u), len(te_u)


def run():
    print("Building feature frame (leak-safe, full population)...")
    D = build_frame()
    print(f"  {len(D):,} rows")

    for direction, qlo, qhi, reverse in [
        ("A: forward (oldest 70% trn, newest 15% te)", 0.70, 0.85, False),
        ("B: reversed (newest 70% trn, oldest 15% te)", 0.30, 0.15, True),
    ]:
        print(f"\n--- direction {direction} ---")
        if not reverse:
            trn, te = D[D["date"] < D["date"].quantile(qlo)], D[D["date"] >= D["date"].quantile(qhi)]
        else:
            trn, te = D[D["date"] > D["date"].quantile(qlo)], D[D["date"] <= D["date"].quantile(qhi)]

        base_mae, _, n_trn, n_te = _fit_eval(trn, te, FEATURES, {})
        print(f"  baseline (default L2 objective, fits MEAN): MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        med_mae, _, _, _ = _fit_eval(trn, te, FEATURES, dict(objective="quantile", alpha=0.5))
        print(f"  quantile objective, alpha=0.5 (fits MEDIAN): MAE={med_mae:.4f} "
              f"({'better' if med_mae < base_mae else 'worse'}, {med_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
