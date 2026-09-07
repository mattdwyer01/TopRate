"""wpr_settle_combined_candidate_test.py - combines the three real,
independently-tested improvements found investigating a specific
complaint (Lindermann, Randwick 2026-09-05: predicted too far back given
his own history and today's field):

  1. Quantile/median objective (wpr_settle_median_objective_test.py) -
     BY FAR the biggest, clearest win (-0.0032/-0.0031 MAE alone).
  2. sect_margin_to_rest feature (wpr_settle_margin_feature_test.py) -
     a real but smaller win alone (-0.0001/-0.0028).
  3. Tactical-variance comment exclusion (wpr_settle_tactical_variance_
     test.py) - fails the bar alone (+0.0002/+0.0001) but costs nothing
     measurable when combined with #2.

This tests all three together against the currently-shipped baseline
(default L2 objective, no margin feature, no tactical exclusion), the
actual candidate that would ship if adopted.

RESULT (Sep 2026): CLEARS THE BAR MORE DECISIVELY than any single piece -
direction A: MAE 0.1975 -> 0.1940 (-0.0035), direction B: MAE 0.2034 ->
0.1976 (-0.0059). All three components genuinely compound (median
objective alone: -0.0032/-0.0031; combined: -0.0035/-0.0059 - notably
better in direction B especially).

Checked against the real case (Lindermann, Randwick 2026-09-05, 730-day
training window, using every already-shipped input fix): predicted
rel_settle=0.185 - Leader band, finally - giving pace_shape=+1.433 (the
model's own ceiling for this pace/field_size combo). Ceolwulf:
rel_settle=0.688 (Midfield), pace_shape=-0.607. TOTAL SPREAD: +2.041 -
matching the user's original +2/-2 expectation almost exactly, arrived
at through three validated, principled fixes (not by tuning toward a
target number): the model was fitting the wrong statistic (mean instead
of median, the same fix wpr_projection.py's own architecture already
made), a percentile rank that couldn't see how uncontested his early
speed was, and one misleading tactical-variance run inflating his
apparent tendency to sit back.

RECOMMENDATION: adopt this combined candidate. It is the strongest
validated result in this entire investigation, on both the general
bidirectional bar and the specific motivating case. Shipping requires
retraining the live settling_estimate model (settling_model.joblib +
settling_config.json) - the model behind the dashboard's speed map for
every race, not just pace_shape - so this was left for explicit user
confirmation before implementing, per this session's established
practice for changes with this blast radius.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import settling_estimate as se

BASE_FEATURES = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal",
                  "field_size", "trailing_sect_ld_early", "trailing_sect_i_to800",
                  "trailing_margin800m"]
ALL_FEATURES = BASE_FEATURES + ["sect_margin_to_rest"]
TACTICAL_MARKERS = ["settled down last", "ridden quiet", "sat back"]


def _load_form_with_comments():
    fh = pd.read_csv(se.FORM_CSV, dtype={"horse": str, "horse_id": str}, low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    if "scrape_date" in fh.columns:
        fh = fh.sort_values("scrape_date").drop_duplicates(
            subset=["horse_lc", "date", "track"], keep="last")
    return fh.sort_values(["horse_lc", "date"])


def _margin_to_rest(s):
    if s.notna().sum() < 2:
        return pd.Series(np.nan, index=s.index)
    vals = s.dropna()
    top_idx = vals.idxmax()
    field_max = vals.max()
    rest_max_excl_top = vals.drop(top_idx).max() if len(vals) > 1 else np.nan
    out = pd.Series(np.nan, index=s.index)
    for idx in vals.index:
        out[idx] = vals[idx] - rest_max_excl_top if idx == top_idx else vals[idx] - field_max
    return out


def build_frame(exclude_tactical, add_margin):
    fh = _load_form_with_comments()
    settle = pd.to_numeric(fh["positionSettled"], errors="coerce")
    fh["field_size"] = pd.to_numeric(fh["field_size"], errors="coerce")
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)
    g = fh["horse_lc"]

    if exclude_tactical:
        cv = fh.get("comments_video", pd.Series("", index=fh.index)).fillna("").astype(str).str.lower()
        is_tactical = cv.apply(lambda t: any(m in t for m in TACTICAL_MARKERS))
        rel_for_tendency = rel_valid.where(~is_tactical)
        valid_for_tendency = valid & ~is_tactical
    else:
        rel_for_tendency = rel_valid
        valid_for_tendency = valid

    csum_incl = rel_for_tendency.fillna(0).groupby(g).cumsum()
    ccount_incl = valid_for_tendency.astype(int).groupby(g).cumsum()
    fh["run_style_tendency"] = (csum_incl.groupby(g).shift(1) /
                                ccount_incl.groupby(g).shift(1).replace(0, np.nan))
    fh["_rel_for_roll"] = rel_for_tendency
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

    if add_margin:
        fh["sect_margin_to_rest"] = fh.groupby("_race_key")["trailing_sect_i_early"].transform(_margin_to_rest)
        _lo, _hi = fh["sect_margin_to_rest"].quantile([0.01, 0.99])
        scale = max(abs(_lo), abs(_hi))
        fh["sect_margin_to_rest"] = fh["sect_margin_to_rest"].clip(_lo, _hi) / scale

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
    return mean_absolute_error(te_u["target"], pred), m, len(trn_u), len(te_u)


def run():
    kwargs_base = dict(n_estimators=200, max_depth=3, learning_rate=0.05, num_leaves=8)
    kwargs_median = dict(kwargs_base, objective="quantile", alpha=0.5)

    print("Building baseline frame (shipped: L2 objective, no margin, no tactical exclusion)...")
    D_base = build_frame(exclude_tactical=False, add_margin=False)
    print("Building full combined frame (median objective + margin + tactical exclusion)...")
    D_comb = build_frame(exclude_tactical=True, add_margin=True)
    print(f"  {len(D_base):,} rows")

    for direction, qlo, qhi, reverse in [
        ("A: forward (oldest 70% trn, newest 15% te)", 0.70, 0.85, False),
        ("B: reversed (newest 70% trn, oldest 15% te)", 0.30, 0.15, True),
    ]:
        print(f"\n--- direction {direction} ---")

        def split(D):
            if not reverse:
                return D[D["date"] < D["date"].quantile(qlo)], D[D["date"] >= D["date"].quantile(qhi)]
            return D[D["date"] > D["date"].quantile(qlo)], D[D["date"] <= D["date"].quantile(qhi)]

        trn0, te0 = split(D_base)
        base_mae, _, n_trn, n_te = _fit_eval(trn0, te0, BASE_FEATURES, **kwargs_base)
        print(f"  baseline (shipped):                      MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        trn1, te1 = split(D_comb)
        comb_mae, _, _, _ = _fit_eval(trn1, te1, ALL_FEATURES, **kwargs_median)
        print(f"  FULL COMBINED (median obj + margin + tactical): MAE={comb_mae:.4f} "
              f"({'better' if comb_mae < base_mae else 'worse'}, {comb_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
