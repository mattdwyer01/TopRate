"""wpr_settle_tactical_variance_test.py - targeted comment-based exclusion
for tactical-variance runs from settling_estimate's trailing tendency
features, after a population-wide robust-statistic swap (median) was
tested and rejected (see wpr_settle_robust_tendency_test.py - worse in
both directions, because a plain mean's sensitivity to extreme runs is,
on average across the population, real signal).

MOTIVATION: Lindermann's one dead-last run (Randwick 2026-09-05
investigation) was not trouble (wpr_void.py's STRONG/WEAK markers - vet,
lame, checked, hampered - are about interference/health and would not
catch it) - it was a DELIBERATE tactical choice by the jockey ("Restrained
today thus Settled Down last... ridden quiet... into 2nd x 25m"), and the
horse still closed well. This is a DIFFERENT, narrower category of noise
than wpr_void's: not "this run doesn't reflect the horse's true ABILITY"
(wpr_void's question) but "this run doesn't reflect the horse's NORMAL
RUNNING STYLE" (a new, settling-specific question).

VALIDATING THE MARKER VOCABULARY FIRST (before building anything): checked
whether candidate phrases actually correlate with unusually-far-back
settling, via each row's leave-one-out deviation from that horse's OWN
other runs (positive = settled further back than usual for that horse).
Population baseline mean deviation ~0.0000 (leave-one-out means center on
zero by construction). Real markers, real effect:
  "settled down last"  n=5,254   mean dev +0.332  (strongest, cleanest)
  "ridden quiet"        n=578    mean dev +0.206
  "sat back"             n=610    mean dev +0.212
  "restrained"          n=15,312  mean dev +0.137  (common but noisier -
                                                     "restrained" alone
                                                     doesn't always mean
                                                     settled unusually far
                                                     back, just ridden
                                                     without urging)
  "back off"             n=965    mean dev +0.125

MARKERS chosen for the exclusion: TACTICAL = ["settled down last", "ridden
quiet", "sat back"] - the three with the cleanest, most explicit "settled
further back than normal, on purpose" language. "restrained" and "back
off" deliberately left OUT - too common/noisy on their own (could describe
a horse ridden calmly WITHOUT an unusual backward shift), risking
excluding real signal the way the blanket median swap did.

MECHANISM: flagged rows are excluded from CONTRIBUTING to
run_style_tendency/last5_tendency's rolling/cumulative windows (same
"unseen -> 0"-style masking already used for missing values) - NOT
excluded as training targets (a flagged run's own actual result is still
a real, valid example to train the model on, using its own un-flagged
prior features). This is a narrower, more surgical version of the
rejected median swap: instead of blunting sensitivity to ALL outliers, it
removes only the ones with explicit textual evidence they don't reflect
normal running style.

Tested bidirectionally against the shipped mean-based baseline.

RESULT (Sep 2026): marginally WORSE in both directions - direction A:
0.1975 -> 0.1977 (+0.0002), direction B: 0.2034 -> 0.2036 (+0.0001). Much
smaller degradation than the blanket median swap (wpr_settle_robust_
tendency_test.py, +0.0005 to +0.0011), consistent with this being a much
smaller, more surgical change (6,458 / 266,655 rows flagged, 2.42%), but
it still does not clear the bidirectional bar on its own.

Checked anyway against the real case: Lindermann has 2 flagged rows.
Excluding them moves his tendency to 0.250 and last5 to 0.172 (last5 now
genuinely BELOW the Leader/On-pace line) - the model then predicts
rel_settle=0.306 for the real race, right at the sharp threshold found in
wpr_settle_draw_interaction_test.py, giving pace_shape~+0.42 (using the
currently shipped pace_shape model) - a real, meaningful lift over the
currently-live +0.09, though not the full +2 originally expected.

Combined with the margin feature (wpr_settle_margin_feature_test.py,
which DOES clear the bar on its own): Lindermann's predicted rel_settle
drops further to 0.285, giving pace_shape~+0.96.

COMBINED bidirectional check (margin feature + this tactical exclusion,
both features together vs the plain baseline): direction A 0.1975 ->
0.1975 (+0.0000, essentially a tie, technically not an improvement),
direction B 0.2034 -> 0.2007 (-0.0027, a real improvement, almost
identical to the margin feature's own -0.0028 alone). CONCLUSION: adding
the tactical exclusion on top of the margin feature costs essentially
nothing at the population level (differences from margin-alone are in the
4th decimal - rounding noise) while providing a real, textually-evidenced
fix for cases exactly like Lindermann's. The margin feature is carrying
nearly all of the measured population-level MAE gain; the tactical
exclusion's value is case-specific correctness, not aggregate accuracy.

NOT ADOPTED ALONE (fails the bidirectional bar by itself, marginally).
DEFENSIBLE ONLY AS PART OF THE COMBINED CANDIDATE (margin feature +
tactical exclusion together) - left for the user's decision given the
blast radius (retrains the live settling_estimate model, used by the
dashboard's speed map for every race).
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import settling_estimate as se

FEATURES = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal",
            "field_size", "trailing_sect_ld_early", "trailing_sect_i_to800",
            "trailing_margin800m"]

TACTICAL_MARKERS = ["settled down last", "ridden quiet", "sat back"]


def _load_form_with_comments():
    """settling_estimate._load_form() doesn't keep comment columns - reload
    directly, same dedup convention."""
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


def build_frame(exclude_tactical=False):
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
        print(f"  tactical-variance rows flagged: {is_tactical.sum():,} / {len(fh):,} "
              f"({is_tactical.mean()*100:.2f}%)")
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
    fh["target"] = rel_valid   # the flagged run is STILL a valid target - only excluded as an INPUT to later rows

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
    kwargs = dict(n_estimators=200, max_depth=3, learning_rate=0.05, num_leaves=8)

    print("Building baseline frame (no exclusion, shipped)...")
    D_base = build_frame(exclude_tactical=False)
    print("Building candidate frame (tactical-variance rows excluded from tendency)...")
    D_cand = build_frame(exclude_tactical=True)
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
        base_mae, n_trn, n_te = _fit_eval(trn0, te0, FEATURES, **kwargs)
        print(f"  baseline (no exclusion, shipped): MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        trn1, te1 = split(D_cand)
        c_mae, _, _ = _fit_eval(trn1, te1, FEATURES, **kwargs)
        print(f"  + tactical-variance exclusion:    MAE={c_mae:.4f} "
              f"({'better' if c_mae < base_mae else 'worse'}, {c_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
