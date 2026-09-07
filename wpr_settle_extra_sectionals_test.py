"""
wpr_settle_extra_sectionals_test.py - tests whether feeding the trained
settling model MORE of the sectional features race_speed_estimate.py
already uses (sect_ld_early, sect_i_to800, margin800m) helps, following
up on "keep refining until reliable" after the model rebuild found the
non-linear architecture itself was the big lever (not more hand-picked
features). This tests the natural next question: does the model find
more signal if given more of the same KIND of information it already
uses well (sect_i_early), rather than a different kind (jockey tendency,
track history - both already tried and rejected for race_speed_estimate).

Three new candidate trailing features, all already used elsewhere in this
codebase (race_speed_estimate.py's own _prior_means), winsorized at their
own 1st/99th percentile bounds (same discipline as sect_i_early):
  - sect_ld_early ("leaderEarlySpeed"): how fast did the LEADER go early
    in this horse's past races - context for interpreting sect_i_early.
  - sect_i_to800: an early sectional split further into the race.
  - margin800m: how far behind at the 800m in past races.

Reuses the exact validated pipeline (load_and_prep, add_trailing_run_style,
add_trailing_sect_early, add_race_relative_sect_rank, add_last5_tendency)
- no changes to what's already shipped, just testing additions on top.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

from wpr_settle_barrier_nudge_calibration_test import load_and_prep, add_trailing_run_style, verify_against_slow_method
from wpr_settle_sectional_test import add_trailing_sect_early, add_race_relative_sect_rank
from wpr_settle_recency_nonlinear_test import add_last5_tendency


def add_trailing_winsorized(fh, col, out_col):
    raw = pd.to_numeric(fh[col], errors="coerce")
    lo, hi = raw.quantile([0.01, 0.99])
    clipped = raw.clip(lo, hi)
    valid = clipped.notna()
    val_valid = clipped.where(valid)
    g = fh["horse_lc"]
    csum_incl = val_valid.fillna(0).groupby(g).cumsum()
    ccount_incl = valid.astype(int).groupby(g).cumsum()
    fh[out_col] = (csum_incl.groupby(g).shift(1) / ccount_incl.groupby(g).shift(1).replace(0, np.nan))
    print(f"  {out_col}: winsorized to [{lo:.2f}, {hi:.2f}], "
          f"coverage {fh[out_col].notna().mean()*100:.1f}%")
    return fh


def run():
    print("Loading and preparing form history...")
    fh = load_and_prep()
    fh = add_trailing_run_style(fh)
    verify_against_slow_method(fh)
    fh = add_trailing_sect_early(fh)
    fh = add_race_relative_sect_rank(fh)
    fh = add_last5_tendency(fh)

    fh = add_trailing_winsorized(fh, "sect_ld_early", "trailing_sect_ld_early")
    fh = add_trailing_winsorized(fh, "sect_i_to800", "trailing_sect_i_to800")
    fh = add_trailing_winsorized(fh, "margin800m", "trailing_margin800m")

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    fh["sect_signal"] = (fh["sect_rank_in_race"] - 0.5) * 2

    baseline_features = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal", "field_size"]
    extra_features = ["trailing_sect_ld_early", "trailing_sect_i_to800", "trailing_margin800m"]
    all_features = baseline_features + extra_features

    usable = fh.dropna(subset=all_features + ["actual_rel"]).copy()
    print(f"\nUsable rows (baseline + all 3 extras present): {len(usable):,}")

    q70, q85 = usable["date"].quantile([0.70, 0.85])
    trn_a = usable[usable["date"] < q70]
    te_a = usable[usable["date"] >= q85]
    q30, q15 = usable["date"].quantile([0.30, 0.15])
    trn_b = usable[usable["date"] > q30]
    te_b = usable[usable["date"] <= q15]

    def fit_and_score(feats, trn, te, label):
        model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1)
        model.fit(trn[feats], trn["actual_rel"])
        pred = model.predict(te[feats])
        mae = mean_absolute_error(te["actual_rel"], pred)
        print(f"  [{label}] n_trn={len(trn):,} n_te={len(te):,} MAE={mae:.4f}")
        return mae

    print("\n=== Baseline (5 features, currently shipped) vs + 3 extra sectionals ===")
    for direction, (trn, te) in [("A (forward)", (trn_a, te_a)), ("B (reversed)", (trn_b, te_b))]:
        base_mae = fit_and_score(baseline_features, trn, te, f"baseline, direction {direction}")
        all_mae = fit_and_score(all_features, trn, te, f"+3 extras, direction {direction}")
        print(f"    direction {direction}: {base_mae:.4f} -> {all_mae:.4f} "
              f"({all_mae - base_mae:+.4f}, {'better' if all_mae < base_mae else 'worse'})")

    # Also test each extra feature individually, in case one helps and the
    # others just add noise that masks it in the combined test.
    print("\n=== Each extra feature added individually ===")
    for feat in extra_features:
        print(f"\n  --- + {feat} only ---")
        for direction, (trn, te) in [("A", (trn_a, te_a)), ("B", (trn_b, te_b))]:
            base_mae = fit_and_score(baseline_features, trn, te, f"baseline {direction}")
            one_mae = fit_and_score(baseline_features + [feat], trn, te, f"+{feat} {direction}")
            print(f"      direction {direction}: {base_mae:.4f} -> {one_mae:.4f} "
                  f"({one_mae - base_mae:+.4f}, {'better' if one_mae < base_mae else 'worse'})")

    print("\nDone.")


if __name__ == "__main__":
    run()
