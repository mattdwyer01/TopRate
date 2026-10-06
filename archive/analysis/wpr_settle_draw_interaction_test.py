"""wpr_settle_draw_interaction_test.py - tests whether settling_estimate's
trained model correctly captures a real interaction found in the data (Sep
2026, investigating a specific complaint: Lindermann, Randwick 2026-09-05,
drawn 9 of 9, but settled 1st/2nd from similarly wide gates twice in his
last 6 runs - the shipped model still predicted him back to On-pace/
Midfield, not Leader):

REAL DATA EVIDENCE (see wpr_settle_draw_interaction_test.py's own
diagnostic run, 227,920 rows): a wide draw pushes the WHOLE population back
by +0.119 average rel-settle (Good->Wide), but confirmed leader-type
horses (own run_style_tendency <=0.20) are barely affected: only +0.038 -
about 1/3 the population effect. run_style_tendency and last5_tendency are
also 90.5% correlated, which understates "own history"'s true combined
feature importance in the current model (they split credit between
themselves).

Two candidates tested, both bidirectionally, against the CURRENTLY SHIPPED
config (n_estimators=200, max_depth=3, learning_rate=0.05, num_leaves=8) as
baseline:
  1. Same hyperparams, + one explicit interaction feature:
     draw_x_tendency = draw_signal * run_style_tendency
  2. Same 8 features, but more model capacity (max_depth=4, num_leaves=16)
     to let the model find nonlinear interactions itself without needing
     an explicit feature.

RESULT (Sep 2026): both "deeper capacity" variants improve held-out MAE in
BOTH directions (A: -0.0005/-0.0005, B: -0.0002/-0.0003) - technically
clears the bidirectional bar. The explicit draw_x_tendency feature ALONE
does nothing (+0.0000 both directions) - LightGBM can already express a
multiplicative interaction via successive splits given enough depth, so
adding it explicitly to an already-adequate-depth model is redundant.

BUT the improvement is tiny (~0.25% relative MAE) and, checked directly
against the actual motivating case (Lindermann, Randwick 2026-09-05,
race_id 1758501): the deeper+interaction model predicts 0.447 vs the
shipped model's 0.444 - essentially UNCHANGED. The tiny population-level
MAE gain is NOT coming from fixing extreme cases like this one; it is
coming from small improvements elsewhere in the distribution. Model
CAPACITY was not the bottleneck for this case.

NOT ADOPTED - see wpr_settle_margin_feature_test.py for the follow-up that
found the actual bottleneck (sect_signal is a percentile RANK, which
cannot distinguish "narrowly 2nd-best" from "several lengths clear of
everyone else" - exactly Lindermann's situation in this field).
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
    fh["target"] = rel_valid   # this run's actual outcome

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
    fh["draw_x_tendency"] = fh["draw_signal"] * fh["run_style_tendency"]

    return fh.dropna(subset=["run_style_tendency", "target", "date"]).sort_values("date")


def _fit_eval(trn, te, features, **lgb_kwargs):
    trn_u = trn.dropna(subset=features + ["target"])
    te_u = te.dropna(subset=features + ["target"])
    med = trn_u[features].median()
    Xtr = trn_u[features].fillna(med)
    Xte = te_u[features].fillna(med)
    m = lgb.LGBMRegressor(random_state=42, verbosity=-1, **lgb_kwargs)
    m.fit(Xtr, trn_u["target"])
    pred = m.predict(Xte)
    return mean_absolute_error(te_u["target"], pred), len(trn_u), len(te_u)


def run():
    print("Building feature frame (leak-safe, full population)...")
    D = build_frame()
    print(f"  {len(D):,} rows")

    baseline_kwargs = dict(n_estimators=200, max_depth=3, learning_rate=0.05, num_leaves=8)
    deeper_kwargs = dict(n_estimators=200, max_depth=4, learning_rate=0.05, num_leaves=16)

    for direction, (trn, te) in [
        ("A: forward (oldest 70% trn, newest 15% te)",
         (D[D["date"] < D["date"].quantile(0.70)],
          D[D["date"] >= D["date"].quantile(0.85)])),
        ("B: reversed (newest 70% trn, oldest 15% te)",
         (D[D["date"] > D["date"].quantile(0.30)],
          D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        print(f"\n--- direction {direction} ---")
        base_mae, n_trn, n_te = _fit_eval(trn, te, FEATURES, **baseline_kwargs)
        print(f"  baseline (shipped config, 8 features): MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        int_mae, _, _ = _fit_eval(trn, te, FEATURES + ["draw_x_tendency"], **baseline_kwargs)
        print(f"  + draw_x_tendency interaction feature: MAE={int_mae:.4f} "
              f"({'better' if int_mae < base_mae else 'worse'}, {int_mae - base_mae:+.4f})")

        deep_mae, _, _ = _fit_eval(trn, te, FEATURES, **deeper_kwargs)
        print(f"  deeper capacity (depth=4, leaves=16), same features: MAE={deep_mae:.4f} "
              f"({'better' if deep_mae < base_mae else 'worse'}, {deep_mae - base_mae:+.4f})")

        deep_int_mae, _, _ = _fit_eval(trn, te, FEATURES + ["draw_x_tendency"], **deeper_kwargs)
        print(f"  deeper capacity + interaction feature: MAE={deep_int_mae:.4f} "
              f"({'better' if deep_int_mae < base_mae else 'worse'}, {deep_int_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
