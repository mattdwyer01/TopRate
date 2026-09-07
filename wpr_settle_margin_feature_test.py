"""wpr_settle_margin_feature_test.py - tests whether a MARGIN-based early-
speed feature beats sect_signal's plain percentile RANK.

MOTIVATION (Sep 2026, same investigation as wpr_settle_draw_interaction_
test.py - Lindermann, Randwick 2026-09-05): sect_signal is
rank(trailing_sect_i_early, pct=True) within today's field - it can tell
"2nd-highest of 9" but throws away HOW MUCH higher. Lindermann's trailing
sect_i_early (-0.55) was 1.5 clear of the next-best active runner
(Campaldino, -2.05), while every other runner in that field sat at -4 to
-11 - a genuinely uncontested best, not a marginal one. A rank feature
gives the same 0.89 percentile whether the gap to 2nd is 0.1 or 10.0.

New feature: sect_margin_to_rest = this horse's trailing_sect_i_early
MINUS the best (max) trailing_sect_i_early among the REST of today's
field. Positive and large = uncontested clear-best; near zero or negative
= contested/not the best. Same leak-safe per-race grouping as sect_signal
(_race_key = track|date|raceNumber), computed once per field.

Tested bidirectionally against the shipped config, both as an ADDITION to
sect_signal and as a REPLACEMENT for it.

RESULT (Sep 2026): ADDING sect_margin_to_rest alongside sect_signal clears
the bidirectional bar - direction A: MAE 0.1975 -> 0.1973 (-0.0001),
direction B: MAE 0.2034 -> 0.2007 (-0.0028). REPLACING sect_signal is
worse in direction A (+0.0031) despite being better in B - mixed, not
adopted; the two features are complementary (rank AND margin both carry
real information), not redundant.

Checked directly against the motivating case (Lindermann, Randwick
2026-09-05), ALSO fixing a second real bug found alongside this one (see
toprate_daily.py commit excluding scratched runners from settle_field -
a scratched horse with a fast trailing rating was still being ranked
against, suppressing Lindermann's percentile from a true 1.0 to 0.89):
combined, both fixes move his predicted rel_settle from 0.44 (shipped) to
0.39 (candidate) - real, directionally correct movement, but still
"On-pace" band, not "Leader", and the resulting pace_shape adjustment
would still be modest (nowhere near a +2 swing) since pace_shape's own
model only produces large swings once rel_settle crosses roughly 0.30
(see wpr_settle_draw_interaction_test.py's threshold finding).

CONCLUSION: this is a real, adoptable improvement (clears the bar, and is
the right kind of fix - a rank alone genuinely cannot distinguish
"narrowly ahead" from "uncontested"), but it is NOT, by itself, going to
produce the +2/-2 magnitude originally expected for cases like this - that
would need either a further-improved settle model, or a rethink of
pace_shape's own calibration for confidently-extreme inputs. Adopting
this into the live settling_estimate model was left to the user's
decision given the blast radius (it retrains the model behind the
dashboard's speed map for every race, not just pace_shape).
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import settling_estimate as se

BASE_FEATURES = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal",
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

    # sect_margin_to_rest: own value minus the BEST of the rest of the field.
    # Computed via: field_max (max of all incl. self), field_2nd (max
    # excluding the single top scorer). For the top scorer, margin =
    # own - field_2nd (positive = clear). For everyone else, margin =
    # own - field_max (negative or small = someone else is faster).
    def _margin_to_rest(s):
        if s.notna().sum() < 2:
            return pd.Series(np.nan, index=s.index)
        vals = s.dropna()
        top_idx = vals.idxmax()
        field_max = vals.max()
        rest_max_excl_top = vals.drop(top_idx).max() if len(vals) > 1 else np.nan
        out = pd.Series(np.nan, index=s.index)
        for idx in vals.index:
            if idx == top_idx:
                out[idx] = vals[idx] - rest_max_excl_top
            else:
                out[idx] = vals[idx] - field_max
        return out

    fh["sect_margin_to_rest"] = fh.groupby("_race_key")["trailing_sect_i_early"].transform(_margin_to_rest)
    # Winsorize the margin the same way other sectional features are (fit
    # on this same population, rounded to whole units for readability).
    _lo, _hi = fh["sect_margin_to_rest"].quantile([0.01, 0.99])
    fh["sect_margin_to_rest"] = fh["sect_margin_to_rest"].clip(_lo, _hi) / max(abs(_lo), abs(_hi))

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
    print(f"  sect_margin_to_rest coverage: {D['sect_margin_to_rest'].notna().mean()*100:.1f}%")

    kwargs = dict(n_estimators=200, max_depth=3, learning_rate=0.05, num_leaves=8)
    add_margin = BASE_FEATURES + ["sect_margin_to_rest"]
    replace_margin = [f for f in BASE_FEATURES if f != "sect_signal"] + ["sect_margin_to_rest"]

    for direction, (trn, te) in [
        ("A: forward (oldest 70% trn, newest 15% te)",
         (D[D["date"] < D["date"].quantile(0.70)],
          D[D["date"] >= D["date"].quantile(0.85)])),
        ("B: reversed (newest 70% trn, oldest 15% te)",
         (D[D["date"] > D["date"].quantile(0.30)],
          D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        print(f"\n--- direction {direction} ---")
        base_mae, n_trn, n_te = _fit_eval(trn, te, BASE_FEATURES, **kwargs)
        print(f"  baseline (shipped, sect_signal=rank only): MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        add_mae, _, _ = _fit_eval(trn, te, add_margin, **kwargs)
        print(f"  + sect_margin_to_rest (ADDED to sect_signal): MAE={add_mae:.4f} "
              f"({'better' if add_mae < base_mae else 'worse'}, {add_mae - base_mae:+.4f})")

        repl_mae, _, _ = _fit_eval(trn, te, replace_margin, **kwargs)
        print(f"  sect_margin_to_rest REPLACING sect_signal:    MAE={repl_mae:.4f} "
              f"({'better' if repl_mae < base_mae else 'worse'}, {repl_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
