"""wpr_adj_full_trained_model_test.py - validates converting EVERY
population-lookup ADJ_TERM (track_barrier, trainer_merit, jockey_merit,
gear_change, closing_merit) into a trained per-row model, and validates
removing _CALIB_ADJ_SLOPE entirely once they are - the two changes the user
asked to ship together (Sep 2026).

track_barrier was already validated as a trained-model win in isolation
(wpr_adj_slope_and_bucket_model_test.py). This script (1) extends the same
methodology to the other four population terms, and (2) checks the combined
effect: does the FULL additive projection (all five terms as trained models,
slope removed) beat the currently-shipped architecture (five lookup tables,
slope=0.1791) on held-out MAE, bidirectionally.

Same bidirectional bar as every other change this session: a candidate must
win in BOTH directions of a swapped chronological split.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error
import json

import wpr_projection as wpr


def build_frame():
    print("Building training frame (expensive step)...")
    D = wpr.build_training_frame("wpr_form_history.csv.gz", n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date").reset_index(drop=True)
    print(f"  {len(D):,} rows")

    print("  merging trainer/jockey trailing win-rate...")
    name_map, tj_lookup = wpr._load_trainer_jockey_by_horse_date("wpr_form_history.csv.gz")
    tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    tj_names = D["horse_id"].map(name_map)
    tj_vals = [tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(tj_names, tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in tj_vals]
    D["horse_lc"] = tj_names.astype(str).str.lower()

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: {len(D):,} rows remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base", "career_avg"]).copy()
    D["gear_bucket"] = D["gear_changes"].apply(wpr._gear_change_bucket)
    D["gear_code"] = D["gear_bucket"].astype("category").cat.codes
    D["track_code"] = D["track"].astype("category").cat.codes
    return D


def eval_term(name, D, feat_cols, cat_cols, build_lookup_pred, splits, coverage_aware=False):
    """build_lookup_pred(trn, te) -> te's shipped-lookup prediction (residual
    scale). splits: list of (label, trn, te) tuples.

    coverage_aware: for columns only populated in the last ~year of history
    (trainer_win_pct_365d/jockey_win_pct_90d), the global date-quantile
    splits leave one direction's trn or te empty (all the coverage sits in
    the recent tail). When set, ignore the passed-in splits entirely and
    instead build forward/reversed splits from the COVERED subset's own
    date range - same "own coverage-aware cutoff" pattern _fit_merit_lookup
    already uses in production, just applied bidirectionally here."""
    print(f"\n=== {name}: trained model vs shipped lookup ===")
    all_feats = feat_cols
    Dt = D.dropna(subset=all_feats + ["target", "career_avg"]).copy()
    if coverage_aware:
        q70, q85, q15, q30 = Dt["date"].quantile([0.70, 0.85, 0.15, 0.30])
        splits = [
            ("A forward (own coverage window)", Dt[Dt["date"] < q70], Dt[Dt["date"] >= q85]),
            ("B reversed (own coverage window)", Dt[Dt["date"] > q30], Dt[Dt["date"] <= q15]),
        ]
    for label, trn, te in splits:
        trn = Dt.loc[Dt.index.intersection(trn.index)]
        te = Dt.loc[Dt.index.intersection(te.index)]
        if len(trn) < 200 or len(te) < 50:
            print(f"  [{label}] insufficient rows ({len(trn)}/{len(te)}), skipping")
            continue
        resid_trn = trn["target"] - trn["career_avg"]
        resid_te = te["target"] - te["career_avg"]

        lookup_pred = build_lookup_pred(trn, te)
        mae_lookup = mean_absolute_error(resid_te, lookup_pred)

        model = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                                  num_leaves=8, random_state=42, verbosity=-1,
                                  objective="quantile", alpha=0.5)
        model.fit(trn[all_feats], resid_trn)
        pred_model = model.predict(te[all_feats])
        mae_model = mean_absolute_error(resid_te, pred_model)
        print(f"  [{label}] residual MAE: shipped={mae_lookup:.4f}  trained={mae_model:.4f} "
              f"({'better' if mae_model < mae_lookup else 'worse'}, {mae_model - mae_lookup:+.4f})")


def make_splits(D):
    q70, q85, q15, q30 = D["date"].quantile([0.70, 0.85, 0.15, 0.30])
    fwd = (D[D["date"] < q70], D[D["date"] >= q85])
    rev = (D[D["date"] > q30], D[D["date"] <= q15])
    return [("A forward", *fwd), ("B reversed", *rev)]


def main():
    D = build_frame()
    with open("wpr_models/config.json") as f:
        cfg = json.load(f)
    splits = make_splits(D)

    # --- track_barrier (re-confirm) ---
    def tb_lookup(trn, te):
        return [wpr._track_barrier_term(t, d, b, f, cfg.get("track_barrier_lookup"))
                for t, d, b, f in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])]
    eval_term("track_barrier", D, ["cur_distance", "barrier", "field_size", "track_code"], [],
              tb_lookup, splits)

    # --- trainer_merit ---
    def trainer_lookup(trn, te):
        return [wpr._merit_term(wpr._merit_bucket(v, cfg.get("trainer_merit_edges")), cfg.get("trainer_merit_lookup"))
                for v in te["trainer_win_pct_365d"]]
    eval_term("trainer_merit", D, ["trainer_win_pct_365d", "field_size"], [],
              trainer_lookup, splits, coverage_aware=True)

    # --- jockey_merit ---
    def jockey_lookup(trn, te):
        return [wpr._merit_term(wpr._merit_bucket(v, cfg.get("jockey_merit_edges")), cfg.get("jockey_merit_lookup"))
                for v in te["jockey_win_pct_90d"]]
    eval_term("jockey_merit", D, ["jockey_win_pct_90d", "field_size"], [],
              jockey_lookup, splits, coverage_aware=True)

    # --- gear_change ---
    def gear_lookup(trn, te):
        return [wpr._gear_change_term(b, cfg.get("gear_change_lookup")) for b in te["gear_bucket"]]
    eval_term("gear_change", D, ["gear_code", "field_size", "first_up", "second_up", "n_runs"], [],
              gear_lookup, splits)

    # --- closing_merit ---
    def closing_lookup(trn, te):
        return [wpr._closing_merit_term(pairs, cfg.get("pace_baseline_lookup")) for pairs in te["closing_pairs"]]
    D["closing_own_mean"] = D["closing_pairs"].apply(
        lambda pairs: float(np.mean([s for s, b in pairs])) if pairs else np.nan)
    D["closing_n_pairs"] = D["closing_pairs"].apply(len)
    # own-history shrunk residual using the SHIPPED baseline (an
    # already-computed, leak-safe input - same "reuse a validated fixed
    # input" pattern pace_shape's own two ingredients use) as the model's
    # own feature, letting the model learn the right amount of shrinkage/
    # nonlinearity by n_pairs instead of the fixed _shrink() formula.
    def _raw_closing_resid(pairs, lookup):
        if not pairs or not lookup:
            return np.nan
        vals = []
        for sect, bucket in pairs:
            exp = lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return float(np.mean(vals)) if vals else np.nan
    D["closing_raw_resid"] = D["closing_pairs"].apply(
        lambda pairs: _raw_closing_resid(pairs, cfg.get("pace_baseline_lookup")))
    eval_term("closing_merit", D, ["closing_raw_resid", "closing_n_pairs", "field_size"], [],
              closing_lookup, splits)

    print("\n=== Combined: full additive MAE, all 5 as trained models, slope removed ===")
    # Fit each term's model on trn (forward split only, mirroring live
    # train_wpr_projection's own trn/cf/te convention) and compare the FULL
    # additive projection (base + sum(ADJ_TERMS)) against the shipped
    # architecture on the same held-out te.
    q1, q2 = D["date"].quantile([0.70, 0.85])
    trn = D[D["date"] < q1].dropna(subset=["target", "career_avg"])
    te = D[D["date"] >= q2].copy()

    def fit(fit_frame, feats):
        d = fit_frame.dropna(subset=feats + ["target", "career_avg"])
        m = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                              num_leaves=8, random_state=42, verbosity=-1,
                              objective="quantile", alpha=0.5)
        m.fit(d[feats], d["target"] - d["career_avg"])
        return m

    tb_feats = ["cur_distance", "barrier", "field_size", "track_code"]
    trm_feats = ["trainer_win_pct_365d", "field_size"]
    jm_feats = ["jockey_win_pct_90d", "field_size"]
    gc_feats = ["gear_code", "field_size", "first_up", "second_up", "n_runs"]
    cm_feats = ["closing_raw_resid", "closing_n_pairs", "field_size"]

    # trainer_merit/jockey_merit: coverage only exists in the last ~year of
    # history (see eval_term's coverage_aware note) - fit on the COVERED
    # subset's own trn cutoff, not the global trn (which is almost entirely
    # uncovered and crashes on an empty frame), same as production
    # _fit_merit_lookup already does.
    trm_cov = D.dropna(subset=trm_feats + ["target", "career_avg"])
    jm_cov = D.dropna(subset=jm_feats + ["target", "career_avg"])
    trm_trn = trm_cov[trm_cov["date"] < trm_cov["date"].quantile(0.70)]
    jm_trn = jm_cov[jm_cov["date"] < jm_cov["date"].quantile(0.70)]

    m_tb = fit(trn, tb_feats)
    m_trm = fit(trm_trn, trm_feats)
    m_jm = fit(jm_trn, jm_feats)
    m_gc = fit(trn, gc_feats)
    m_cm = fit(trn, cm_feats)

    def pred_or_zero(model, frame, feats):
        ok = frame[feats].notna().all(axis=1)
        out = pd.Series(0.0, index=frame.index)
        if ok.any():
            out.loc[ok] = model.predict(frame.loc[ok, feats])
        return out

    te["track_barrier"] = pred_or_zero(m_tb, te, tb_feats)
    te["trainer_merit"] = pred_or_zero(m_trm, te, trm_feats)
    te["jockey_merit"] = pred_or_zero(m_jm, te, jm_feats)
    te["gear_change"] = pred_or_zero(m_gc, te, gc_feats)
    te["closing_merit"] = pred_or_zero(m_cm, te, cm_feats)
    # pace_shape and own_* terms: use the SHIPPED, already-fitted values
    # (unchanged by this test) - te already carries these from build_
    # training_frame/build_features directly. pace_shape needs its own
    # model applied since it is not a plain feature column.
    since = (D["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    te["pace_score"] = te["race_id"].map(race_id_to_score)
    te["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(te["horse_lc"], te["date"])]
    import joblib
    pace_model = joblib.load("wpr_models/pace_shape.joblib")
    te["pace_shape"] = [
        wpr._pace_shape_term(ps, prs, fs, pace_model)
        for ps, prs, fs in zip(te["pace_score"], te["predicted_rel_settle"], te["field_size"])
    ]

    new_terms = wpr.ADJ_TERMS
    new_sum = wpr._cap_adj_sum(te[new_terms].to_numpy()).sum(axis=1)
    pred_new_noslope = te["_base"] + new_sum
    mae_new_noslope = mean_absolute_error(te["target"], pred_new_noslope)

    # shipped comparison: same te rows, shipped lookup terms + shipped slope
    te["track_barrier_shipped"] = tb_lookup(trn, te)
    te["trainer_merit_shipped"] = trainer_lookup(trn, te)
    te["jockey_merit_shipped"] = jockey_lookup(trn, te)
    te["gear_change_shipped"] = gear_lookup(trn, te)
    te["closing_merit_shipped"] = closing_lookup(trn, te)
    shipped_terms = ["own_distance", "own_going", "own_first_up", "own_second_up",
                     "own_trend", "own_long_spell", "track_barrier_shipped",
                     "closing_merit_shipped", "trainer_merit_shipped",
                     "jockey_merit_shipped", "pace_shape"]
    shipped_sum = wpr._cap_adj_sum(te[shipped_terms].to_numpy()).sum(axis=1)
    pred_shipped = te["_base"] + shipped_sum * wpr._CALIB_ADJ_SLOPE
    mae_shipped = mean_absolute_error(te["target"], pred_shipped)

    # also: new trained terms, but keeping the slope (in case removing the
    # slope is the wrong call even with better terms)
    pred_new_withslope = te["_base"] + new_sum * wpr._CALIB_ADJ_SLOPE
    mae_new_withslope = mean_absolute_error(te["target"], pred_new_withslope)

    print(f"  shipped (5 lookups + slope {wpr._CALIB_ADJ_SLOPE}): MAE={mae_shipped:.4f}")
    print(f"  new trained terms, NO slope (slope=1.0):            MAE={mae_new_noslope:.4f}")
    print(f"  new trained terms, WITH shipped slope:               MAE={mae_new_withslope:.4f}")


if __name__ == "__main__":
    main()
