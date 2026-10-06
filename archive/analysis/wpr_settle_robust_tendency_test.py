"""wpr_settle_robust_tendency_test.py - tests whether a ROBUST statistic
(median / trimmed) for run_style_tendency and last5_tendency beats the
shipped plain MEAN, after finding a real cause of a bad prediction (Sep
2026, Lindermann/Randwick 2026-09-05 investigation):

settling_estimate.py applies NO void/trouble filtering at all (unlike
wpr_projection.py, which excludes STRONG/WEAK trouble-comment runs before
training - see wpr_void.py). Worse, this specific case isn't even
"trouble" in wpr_void's sense: Lindermann's one dead-last (positionSettled
7/7) run in his last 6 has a video comment reading "Restrained today thus
Settled Down last... ridden quiet... Straightening Up into 3rd x 300m,
into 2nd x 25m" - a DELIBERATE one-off tactical variation (his jockey
deliberately rode him differently that day), not his normal running
style, and he still closed into 2nd near the line. wpr_void's STRONG/WEAK
markers (vet, lame, checked, hampered, etc.) are about interference/health
trouble and would not catch a deliberate tactical change - this is a
different, new category of noise.

Rather than building a fragile comment-parser for "tactical variance"
(hard to validate, easy to miss variants), this tests the more general,
statistically-justified fix: a MEAN is not robust to a single extreme
outlier regardless of WHY it's extreme (trouble, tactics, or a genuinely
bad run) - a robust statistic (median, or a trimmed mean) is exactly built
for this. Real numbers for Lindermann: last5 mean=0.339 (Midfield-ish) vs
last5 median=0.20 (the Leader/On-pace boundary) - a large, real difference
driven entirely by that one outlier run.

Candidates (both replacing ONLY run_style_tendency/last5_tendency, all
other 6 features unchanged), tested bidirectionally against the shipped
mean-based baseline:
  1. last5_tendency as a rolling(5) MEDIAN instead of mean (run_style_
     tendency left as the full-career mean - it's less outlier-sensitive
     with 40 runs behind it than last5 is with only 5).
  2. Both run_style_tendency (expanding MEDIAN) and last5_tendency
     (rolling(5) MEDIAN).

RESULT (Sep 2026): REJECTED - both candidates are WORSE in BOTH
directions. Direction A: baseline 0.1975 -> candidate1 0.1985 (+0.0011),
candidate2 0.1986 (+0.0011). Direction B: baseline 0.2034 -> candidate1
0.2039 (+0.0005), candidate2 0.2042 (+0.0008). A population-wide switch
to median makes the model measurably worse - whatever a mean captures
from occasional extreme runs (troubled, tactical, or genuinely bad) is,
on average across the whole population, real predictive signal, even
though it was specifically misleading for Lindermann's one restrained/
tactical run.

Checked anyway against the motivating case: even with BOTH features
correctly reading Lindermann as much more forward (tendency 0.225,
last5 0.20 - right at the Leader/On-pace line, vs the mean's 0.286/0.339),
the model trained on this median-based data only predicts rel_settle=0.36
for him - barely moved from the margin-feature candidate's 0.39, and
still well short of confident "Leader" territory. The model's LEARNED
weighting (fit on the whole median-based population, which is itself
worse-calibrated) does not translate an individually-more-accurate input
into a big shift for this one horse.

CONCLUSION: a blanket robust-statistic swap is not the fix. The real
remaining gap looks like some mix of (a) draw_signal genuinely pulling
even strong leader profiles back somewhat (real in the data, see
wpr_settle_draw_interaction_test.py), and (b) the model reasonably
declining to fully commit to "confirmed Leader" for a horse whose barrier
(9 of 9, the widest possible) is itself a real, historically-relevant
risk factor - not obviously a remaining bug. If the misleading tactical
run specifically still needs excluding, the targeted (but fragile) fix
would be a comment-based exclusion list for tactical-variance runs
(distinct from wpr_void.py's trouble/interference markers), validated
the same bidirectional way before shipping - not attempted here given
this session's "comment-parsing is fragile, easy to miss variants" own
caution, and given the population-level median swap it would have
motivated already failed validation.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import settling_estimate as se

FEATURES = ["run_style_tendency", "last5_tendency", "draw_signal", "sect_signal",
            "field_size", "trailing_sect_ld_early", "trailing_sect_i_to800",
            "trailing_margin800m"]


def build_frame(last5_stat="mean", tendency_stat="mean"):
    fh = se._load_form()
    settle = pd.to_numeric(fh["positionSettled"], errors="coerce")
    fh["field_size"] = pd.to_numeric(fh["field_size"], errors="coerce")
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)
    g = fh["horse_lc"]

    if tendency_stat == "mean":
        csum_incl = rel_valid.fillna(0).groupby(g).cumsum()
        ccount_incl = valid.astype(int).groupby(g).cumsum()
        fh["run_style_tendency"] = (csum_incl.groupby(g).shift(1) /
                                    ccount_incl.groupby(g).shift(1).replace(0, np.nan))
    else:
        fh["run_style_tendency"] = rel_valid.groupby(g).transform(
            lambda s: s.expanding().median().shift(1))

    fh["_rel_for_roll"] = rel_valid
    if last5_stat == "mean":
        fh["last5_tendency"] = fh.groupby("horse_lc")["_rel_for_roll"].transform(
            lambda s: s.rolling(5, min_periods=1).mean().shift(1))
    else:
        fh["last5_tendency"] = fh.groupby("horse_lc")["_rel_for_roll"].transform(
            lambda s: s.rolling(5, min_periods=1).median().shift(1))
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

    print("Building baseline frame (mean/mean, shipped)...")
    D_base = build_frame("mean", "mean")
    print("Building candidate 1 frame (last5=median, tendency=mean)...")
    D_c1 = build_frame("median", "mean")
    print("Building candidate 2 frame (last5=median, tendency=median)...")
    D_c2 = build_frame("median", "median")
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
        print(f"  baseline (mean/mean, shipped): MAE={base_mae:.4f}  n_trn={n_trn:,} n_te={n_te:,}")

        trn1, te1 = split(D_c1)
        c1_mae, _, _ = _fit_eval(trn1, te1, FEATURES, **kwargs)
        print(f"  candidate 1 (last5=median):    MAE={c1_mae:.4f} "
              f"({'better' if c1_mae < base_mae else 'worse'}, {c1_mae - base_mae:+.4f})")

        trn2, te2 = split(D_c2)
        c2_mae, _, _ = _fit_eval(trn2, te2, FEATURES, **kwargs)
        print(f"  candidate 2 (both=median):     MAE={c2_mae:.4f} "
              f"({'better' if c2_mae < base_mae else 'worse'}, {c2_mae - base_mae:+.4f})")


if __name__ == "__main__":
    run()
