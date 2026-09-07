"""
wpr_pace_adjustment_continuous_test.py - a genuinely DIFFERENT mechanism
for a race-shape-based WPR rating adjustment, after pace_style (a
discrete population lookup on Hot/Fast/Even/Slow x Leader/On-pace/
Midfield/Back) was rejected TWICE (wpr_pace_style_adj_term_test.py,
wpr_pace_style_v2_better_settle_test.py) - the second time WORSE despite
an objectively better settle-side input, real evidence the bottleneck
was not input accuracy.

WHAT'S DIFFERENT HERE: today's single biggest lesson (the settling
estimate rebuild, see settling_estimate.py's own module docstring) was
that a TRAINED MODEL beats a HAND-TUNED FORMULA on the same information,
by roughly 10x. pace_style never got that treatment - it discretized two
already-noisy continuous signals into 4 coarse bands each BEFORE
averaging, which throws away exactly the nuance a population lookup
needs many horses per cell to average out. This tests the analogous fix:
skip the discretization entirely and feed the CONTINUOUS signals into a
small trained model.

Inputs (both continuous, not banded):
  - predicted_rel_settle: the settling model's own raw 0-1 prediction
    (0 = leads, 1 = last) - same leak-safe historical reconstruction as
    wpr_pace_style_v2_better_settle_test.py, but keeping the raw float
    instead of banding it into 4 categories.
  - pace_score: race_speed_estimate.py's own raw 0-1 continuous score
    (1 = hottest) - the SAME model as before (still only +0.29 held-out
    correlation, unimproved), but using its continuous output instead of
    the coarser Hot/Fast/Even/Slow label.
  - interaction = (predicted_rel_settle - 0.5) * (pace_score - 0.5) -
    the textbook mechanism made explicit: a low rel_settle (forward-
    running) combined with a high pace_score (hot early tempo) should be
    a genuinely bad combination (leaders get run down); high combined
    with low should be genuinely good (uncontested lead in a slow race).
  - field_size.

Two candidates tested, both bidirectionally:
  1. A single OLS coefficient on the interaction term alone (cheapest
     possible continuous version - still a "formula", but continuous
     rather than discretized).
  2. A small LightGBM model on all 4 inputs, predicting the residual
     directly - the actual "different mechanism" this script is named
     for, mirroring the settling model's own successful rebuild.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
import race_speed_estimate as rse
import settling_estimate as se
from wpr_void_expansion_bidirectional_test import fit_track_barrier, fit_pace_baseline_reversed, additive_predict

FORM_CSV = "wpr_form_history.csv.gz"


def build_race_speed_scores(since):
    """Leak-safe CONTINUOUS pace score (0-1, 1=hottest) per race_id -
    same method as wpr_own_pace_backtest.build_race_speed_labels (same
    day-by-day prior_means, same model), just keeping res['score']
    instead of discarding it for res['label']."""
    fh = rse._load_and_prep_form()
    rse._load_model()
    scoped = fh[(fh["date"] >= since) & fh["race_id"].notna()]
    dates = sorted(scoped["date"].dt.date.unique())
    print(f"  Building leak-safe pace SCORES for {len(dates)} race days "
          f"({scoped['race_id'].nunique():,} races) since {since}...")
    race_id_to_score = {}
    for i, d in enumerate(dates):
        if i % 40 == 0:
            print(f"    ... {i}/{len(dates)} days")
        day_races = scoped[scoped["date"].dt.date == d]
        pmeans = rse._prior_means(fh, pd.Timestamp(d))
        for race_id, race_runners in day_races.groupby("race_id"):
            try:
                res = rse.estimate_race_speed(race_runners, pd.Timestamp(d), fh, pmeans)
            except Exception:
                continue
            race_id_to_score[race_id] = res["score"]
    print(f"    scored {len(race_id_to_score):,} races")
    return race_id_to_score


def build_settle_score_lookup(since):
    """Leak-safe CONTINUOUS predicted_rel_settle (0-1, 0=lead) per
    (horse_lc, date) - identical feature computation to
    wpr_pace_style_v2_better_settle_test.build_settle_band_lookup, but
    keeps the raw model prediction instead of banding it."""
    print("  Building predicted_rel_settle (continuous) from the trained settling model...")
    fh = se._load_form()
    fh = fh[fh["date"] >= pd.Timestamp(since)].copy()
    fh = fh.sort_values(["horse_lc", "date"]).reset_index(drop=True)

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
    fh = fh.drop(columns=["_rel_for_roll"])

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

    se._load_model()
    features = se._CFG["features"]
    has_tend = fh["run_style_tendency"].notna()
    med = se._CFG["medians"]
    feat_df = fh[features].apply(lambda col: col.fillna(med.get(col.name, 0.0)))
    pred = np.clip(se._MODEL.predict(feat_df), 0.0, 1.0)
    pred = pd.Series(pred, index=fh.index).where(has_tend)

    lookup = {}
    for hlc, date, p in zip(fh["horse_lc"], fh["date"], pred):
        if pd.notna(p):
            lookup[(hlc, date)] = float(p)
    print(f"    built lookup for {len(lookup):,} (horse, date) rows")
    return lookup


def prepare_frame(race_id_to_score, settle_score_lookup):
    print("  building training frame (build_features)...")
    D = wpr.build_training_frame(FORM_CSV, n_jobs=-1).dropna(subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} training rows")

    D["pace_score"] = D["race_id"].map(race_id_to_score)

    _name_map, _tj_lookup = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    D["horse_lc"] = _tj_names.astype(str).str.lower()
    D["predicted_rel_settle"] = [settle_score_lookup.get((h, d)) for h, d in zip(D["horse_lc"], D["date"])]
    print(f"  pace_score coverage: {D['pace_score'].notna().mean()*100:.1f}%")
    print(f"  predicted_rel_settle coverage: {D['predicted_rel_settle'].notna().mean()*100:.1f}%")

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        n_void = int(sum(void_mask))
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: excluded {n_void:,} compromised runs, {len(D):,} rows remain")

    if "going" in D.columns:
        g_ = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g_.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} blank-going rows, {len(D):,} remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()

    D["settle_signal"] = (D["predicted_rel_settle"] - 0.5) * 2
    D["pace_signal"] = (D["pace_score"] - 0.5) * 2
    D["interaction"] = D["settle_signal"] * D["pace_signal"]
    return D


def fit_ols(X, y):
    coef, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def held_out_mae_both_directions(D):
    trainer_edges, trainer_lookup = wpr._fit_merit_lookup(D, "trainer_win_pct_365d")
    jockey_edges, jockey_lookup = wpr._fit_merit_lookup(D, "jockey_win_pct_90d")

    results = {}
    for direction, (trn, te) in [
        ("A: forward (oldest 70% trn, newest 15% te)",
         (D[D["date"] < D["date"].quantile(0.70)],
          D[D["date"] >= D["date"].quantile(0.85)])),
        ("B: reversed (newest 70% trn, oldest 15% te)",
         (D[D["date"] > D["date"].quantile(0.30)],
          D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        te = te.copy()
        tb_lookup = fit_track_barrier(trn)
        te["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, tb_lookup)
            for trk, dist, bar, fs in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])
        ]
        te["trainer_merit"] = [wpr._merit_term(wpr._merit_bucket(v, trainer_edges), trainer_lookup)
                                for v in te["trainer_win_pct_365d"]]
        te["jockey_merit"] = [wpr._merit_term(wpr._merit_bucket(v, jockey_edges), jockey_lookup)
                               for v in te["jockey_win_pct_90d"]]
        cutoff = trn["date"].min() if "reversed" in direction else trn["date"].max()
        pace_lookup_fn = fit_pace_baseline_reversed if "reversed" in direction else \
            (lambda c: wpr._fit_pace_baseline(FORM_CSV, c))
        pb_lookup = pace_lookup_fn(cutoff)
        te["closing_merit"] = [wpr._closing_merit_term(p, pb_lookup) for p in te["closing_pairs"]]

        scored = te.dropna(subset=["_base"] + wpr.ADJ_TERMS)
        baseline_mae = mean_absolute_error(scored["target"], additive_predict(scored))

        usable_mask = scored[["settle_signal", "pace_signal", "interaction"]].notna().all(axis=1)
        trn_usable = trn.dropna(subset=["settle_signal", "pace_signal", "interaction", "target", "career_avg"])

        # Candidate 1: single OLS coefficient on the interaction term alone.
        X1 = trn_usable[["interaction"]].to_numpy()
        y1 = (trn_usable["target"] - trn_usable["career_avg"]).to_numpy()
        (c1,) = fit_ols(X1, y1)
        pace_adj_1 = pd.Series(0.0, index=scored.index)
        pace_adj_1[usable_mask] = scored.loc[usable_mask, "interaction"] * c1
        pred1 = scored["_base"].to_numpy() + wpr._cap_adj_sum(
            scored[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) + pace_adj_1.to_numpy()
        mae1 = mean_absolute_error(scored["target"], pred1)

        # Candidate 2: small LightGBM model on the 3 continuous inputs + field_size.
        feats2 = ["settle_signal", "pace_signal", "interaction", "field_size"]
        model2 = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                                   num_leaves=8, random_state=42, verbosity=-1)
        y2 = trn_usable["target"] - trn_usable["career_avg"]
        model2.fit(trn_usable[feats2], y2)
        pace_adj_2 = pd.Series(0.0, index=scored.index)
        pace_adj_2[usable_mask] = model2.predict(scored.loc[usable_mask, feats2])
        pred2 = scored["_base"].to_numpy() + wpr._cap_adj_sum(
            scored[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) + pace_adj_2.to_numpy()
        mae2 = mean_absolute_error(scored["target"], pred2)

        print(f"  direction {direction}: n_trn_usable={len(trn_usable):,} n_te={len(scored):,} "
              f"(usable in te: {usable_mask.sum():,})")
        print(f"    baseline (no pace term)     MAE={baseline_mae:.4f}")
        print(f"    +interaction (OLS, fit c={c1:+.4f}) MAE={mae1:.4f} "
              f"({'better' if mae1 < baseline_mae else 'worse'}, {mae1 - baseline_mae:+.4f})")
        print(f"    +LightGBM (continuous)      MAE={mae2:.4f} "
              f"({'better' if mae2 < baseline_mae else 'worse'}, {mae2 - baseline_mae:+.4f})")
        results[direction] = (baseline_mae, mae1, mae2)
    return results


def run():
    since = (pd.Timestamp.today() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    print("Building leak-safe historical pace SCORES (continuous)...")
    race_id_to_score = build_race_speed_scores(since)

    settle_score_lookup = build_settle_score_lookup(since)

    print("\nPreparing training frame...")
    D = prepare_frame(race_id_to_score, settle_score_lookup)

    since_ts = pd.Timestamp(since)
    n_before = len(D)
    D = D[D["date"] >= since_ts].copy()
    print(f"  bounded D to the scored window ({since} onward): {n_before:,} -> {len(D):,} rows")

    print("\n=== Continuous pace-adjustment test, both directions ===")
    res = held_out_mae_both_directions(D)

    print("\n=== SUMMARY ===")
    base_a, i1_a, m2_a = res["A: forward (oldest 70% trn, newest 15% te)"]
    base_b, i1_b, m2_b = res["B: reversed (newest 70% trn, oldest 15% te)"]
    for label, a, b in [("interaction (OLS)", i1_a, i1_b), ("LightGBM (continuous)", m2_a, m2_b)]:
        da, db = a - base_a, b - base_b
        both = da < 0 and db < 0
        print(f"  {label}: direction A {da:+.4f}, direction B {db:+.4f}  "
              f"{'BOTH IMPROVED' if both else 'not both improved'}")

    print("\nDone.")


if __name__ == "__main__":
    run()
