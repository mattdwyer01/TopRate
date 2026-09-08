"""wpr_adj_term_ablation_test.py - does each individual ADJ_TERM actually
earn its keep in the live sum (user request, Sep 2026, after the trained-
model rework and the whole-field-bias bug fix)? Also tests gear_change as
a CANDIDATE 12th term - it has a fully trained, fitted model
(pop_adj_models.joblib) but was never actually added to ADJ_TERMS, so it
is computed and then silently discarded every single time (dead code,
not a "0 contribution" - genuinely never summed or shown).

Methodology: bidirectional leak-free half-split (matching every other
term-adoption decision this session - track_barrier/pace_shape/closing_
merit/gear_change were each judged the same way before shipping). Fit
every population term's model on one half, apply to the other (own_*
terms need no fitting - see build_training_frame), then for EACH term T:
  MAE_with_T    = MAE(base + cap_sum(ALL terms))
  MAE_without_T = MAE(base + cap_sum(ALL terms except T, T zeroed))
delta = MAE_without_T - MAE_with_T. Positive delta = removing T makes
MAE worse = T is earning its keep. A term only "passes" if delta > 0 in
BOTH split directions - the same bidirectional bar this session used to
adopt every term in the first place.

USAGE
  python wpr_adj_term_ablation_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error
import joblib

import wpr_projection as wpr

FORM_CSV = "wpr_form_history.csv.gz"

# Candidate set: every LIVE ADJ_TERM plus gear_change (fitted but unused).
ALL_CANDIDATES = list(wpr.ADJ_TERMS) + ["gear_change"]


def build_frame():
    print("Building training frame...")
    D = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1).dropna(
        subset=["target", "date", "career_avg"]).sort_values("date").reset_index(drop=True)
    print(f"  {D.shape[0]:,} rows")

    print("  merging trainer/jockey trailing win-rate...")
    name_map, tj_lookup = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    tj_names = D["horse_id"].map(name_map)
    tj_vals = [tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(tj_names, tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in tj_vals]
    D["horse_lc"] = tj_names.astype(str).str.lower()

    from wpr_void import void_from_comment_only
    cv = D.get("comments_video")
    cs = D.get("comments_steward")
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: {len(D):,} rows remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()

    D["gear_bucket"] = D["gear_changes"].apply(wpr._gear_change_bucket)

    print("  building pace_shape ingredients once (leak-safe, since last 365 days)...")
    since = (D["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    D["pace_score"] = D["race_id"].map(race_id_to_score)
    D["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(D["horse_lc"], D["date"])]
    D["settle_signal"] = (D["predicted_rel_settle"] - 0.5) * 2
    D["pace_signal"] = (D["pace_score"] - 0.5) * 2
    D["interaction"] = D["settle_signal"] * D["pace_signal"]
    D["_pace_shape_since"] = since
    return D


def fit_and_apply_all_terms(fit_data, held_out, since_pace_shape):
    """Fits every population term's model on fit_data, applies (with
    per-race demeaning, matching live serving) to held_out. own_* terms
    already exist as columns (no fitting needed)."""
    fit_data = fit_data.copy()
    held_out = held_out.copy()

    track_categories = sorted(fit_data["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    fit_data["track_code"] = fit_data["track"].map(track_code_map).fillna(-1).astype(int)
    tb_model = wpr._fit_simple_adj_model(fit_data, wpr._TRACK_BARRIER_FEATURES, "track_barrier")

    trm_trn = wpr._fit_coverage_aware_trn(fit_data, ["trainer_win_pct_365d"])
    trm_model = wpr._fit_simple_adj_model(trm_trn, wpr._TRAINER_MERIT_FEATURES, "trainer_merit")
    jm_trn = wpr._fit_coverage_aware_trn(fit_data, ["jockey_win_pct_90d"])
    jm_model = wpr._fit_simple_adj_model(jm_trn, wpr._JOCKEY_MERIT_FEATURES, "jockey_merit")

    fit_data["gear_code"] = fit_data["gear_bucket"].map(wpr._GEAR_BUCKET_CODE).fillna(0).astype(int)
    gc_model = wpr._fit_simple_adj_model(fit_data, wpr._GEAR_CHANGE_FEATURES, "gear_change")

    pace_baseline_lookup = wpr._fit_pace_baseline(FORM_CSV, fit_data["date"].max())

    def _closing_raw_resid_one(pairs):
        vals = []
        for sect, bucket in pairs:
            exp = pace_baseline_lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)

    fit_data["closing_raw_resid"], fit_data["closing_n_pairs"] = zip(
        *[_closing_raw_resid_one(p) for p in fit_data["closing_pairs"]])
    cm_model = wpr._fit_simple_adj_model(fit_data, wpr._CLOSING_MERIT_FEATURES, "closing_merit")

    print("  fitting pace_shape model...")
    since = fit_data["_pace_shape_since"].iloc[0]
    pace_feats = ["settle_signal", "pace_signal", "interaction", "field_size"]
    cov = fit_data[fit_data["date"] >= pd.Timestamp(since)].dropna(
        subset=pace_feats + ["target", "career_avg"])
    pace_model = None
    if len(cov) >= 200:
        import lightgbm as lgb
        cutoff = cov["date"].quantile(0.70)
        cov_trn = cov[cov["date"] < cutoff]
        if len(cov_trn) >= 200:
            pace_model = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                                           num_leaves=8, random_state=42, verbosity=-1,
                                           objective="quantile", alpha=0.5)
            pace_model.fit(cov_trn[pace_feats], cov_trn["target"] - cov_trn["career_avg"])
    print(f"    pace_shape: {'fitted on ' + str(len(cov_trn)) + ' rows' if pace_model is not None else 'skipped (insufficient coverage)'}")

    for f in (held_out,):
        f["track_code"] = f["track"].map(track_code_map).fillna(-1).astype(int)
        f["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, track_code_map, tb_model)
            for trk, dist, bar, fs in zip(f["track"], f["cur_distance"], f["barrier"], f["field_size"])
        ]
        f["trainer_merit"] = [
            wpr._merit_term(v, fs, trm_model, wpr._TRAINER_MERIT_FEATURES)
            for v, fs in zip(f["trainer_win_pct_365d"], f["field_size"])
        ]
        f["jockey_merit"] = [
            wpr._merit_term(v, fs, jm_model, wpr._JOCKEY_MERIT_FEATURES)
            for v, fs in zip(f["jockey_win_pct_90d"], f["field_size"])
        ]
        f["gear_code"] = f["gear_bucket"].map(wpr._GEAR_BUCKET_CODE).fillna(0).astype(int)
        f["gear_change"] = [
            wpr._gear_change_term(b, fs, fu, su, nr, gc_model)
            for b, fs, fu, su, nr in zip(f["gear_bucket"], f["field_size"], f["first_up"], f["second_up"], f["n_runs"])
        ]
        _computed = [_closing_raw_resid_one(p) for p in f["closing_pairs"]]
        f["closing_raw_resid"] = [c[0] for c in _computed]
        f["closing_n_pairs"] = [c[1] for c in _computed]
        f["closing_merit"] = [
            wpr._closing_merit_term(pairs, pace_baseline_lookup, fs, cm_model)
            for pairs, fs in zip(f["closing_pairs"], f["field_size"])
        ]
        for term in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit", "gear_change"):
            f[term] = f[term] - f.groupby("race_id")[term].transform("mean")

        # pace_score/predicted_rel_settle already exist as columns (computed
        # once on the full frame in build_frame(), inherited by this slice) -
        # NOT recomputed here, unlike every other term above, since they are
        # already leak-safe per-row (each derived strictly from PRIOR data
        # relative to that row's own date - see _build_pace_shape_race_scores/
        # _build_pace_shape_settle_lookup).
        f["pace_shape"] = [
            wpr._pace_shape_term(ps, prs, fs, pace_model)
            for ps, prs, fs in zip(f["pace_score"], f["predicted_rel_settle"], f["field_size"])
        ]
    return held_out


def ablate(held_out, candidates):
    """Returns {term: (mae_with, mae_without, delta)} for each candidate,
    holding every OTHER term fixed at its actual computed value (own_*
    terms already columns; population terms already applied above)."""
    all_terms_full = wpr.ADJ_TERMS  # excludes gear_change - the live sum
    d = held_out.dropna(subset=list(set(all_terms_full + candidates)) + ["target"]).copy()

    def predict(term_list):
        return d["_base"].to_numpy() + wpr._cap_adj_sum(d[term_list].to_numpy()).sum(axis=1)

    mae_full = mean_absolute_error(d["target"], predict(all_terms_full))
    results = {}
    for term in candidates:
        if term in all_terms_full:
            without = [t for t in all_terms_full if t != term]
            mae_without = mean_absolute_error(d["target"], predict(without))
        else:
            # gear_change: candidate to ADD - "with" means adding it to the live set
            with_added = all_terms_full + [term]
            mae_with_added = mean_absolute_error(d["target"], predict(with_added))
            results[term] = (mae_full, mae_with_added, mae_full - mae_with_added)
            continue
        results[term] = (mae_full, mae_without, mae_without - mae_full)
    return results, len(d)


def run():
    D = build_frame()
    mid = D["date"].quantile(0.5)
    h1, h2 = D[D["date"] < mid].copy(), D[D["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows, H2: {len(h2):,} rows")

    print("\n=== Direction A: fit H1, ablate on H2 ===")
    h2_scored = fit_and_apply_all_terms(h1, h2, h1["date"].max())
    results_a, n_a = ablate(h2_scored, ALL_CANDIDATES)

    print("\n=== Direction B: fit H2, ablate on H1 ===")
    h1_scored = fit_and_apply_all_terms(h2, h1, h2["date"].max())
    results_b, n_b = ablate(h1_scored, ALL_CANDIDATES)

    print(f"\n{'='*80}\nRESULTS (positive delta = term is earning its keep)\n{'='*80}")
    print(f"{'term':<16} {'A: with':>9} {'A: w/o':>9} {'A delta':>9}   "
          f"{'B: with':>9} {'B: w/o':>9} {'B delta':>9}   verdict")
    for term in ALL_CANDIDATES:
        mw_a, mwo_a, d_a = results_a[term]
        mw_b, mwo_b, d_b = results_b[term]
        both_positive = d_a > 0 and d_b > 0
        verdict = "KEEP (helps both)" if both_positive else "REVIEW (does not help both ways)"
        print(f"{term:<16} {mw_a:>9.4f} {mwo_a:>9.4f} {d_a:>+9.4f}   "
              f"{mw_b:>9.4f} {mwo_b:>9.4f} {d_b:>+9.4f}   {verdict}")


if __name__ == "__main__":
    run()
