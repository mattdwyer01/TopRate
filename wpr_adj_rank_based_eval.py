"""wpr_adj_rank_based_eval.py - re-evaluates the "all population ADJ_TERMS
as trained models, slope removed" question using RANK-based MAE instead of
full-field MAE (user request, Sep 2026): full-field MAE weights every
runner in every race equally, including the also-rans nobody would ever bet
on - a model can look identical on full-field MAE while being meaningfully
better or worse specifically on the runners that matter (the top of the
market). This re-scores the SAME shipped-vs-new-architecture comparison
wpr_adj_full_trained_model_test.py made, but restricted to, per race:
  - rank 1 only (the single top-projected runner)
  - top 4 by projected WPR
  - top half by projected WPR (ceil(field_size_in_sample / 2))
Ranking is by each architecture's OWN projected WPR (not the actual
outcome) - this is "how accurate is the model about the runners IT would
tell you to look at", the honest question for a tool whose output drives
selection.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.metrics import mean_absolute_error
import json
import joblib

import wpr_projection as wpr
from wpr_adj_full_trained_model_test import build_frame


def rank_mae(frame, pred_col, target_col="target"):
    """MAE at rank1 / top4 / top-half, ranking by pred_col descending
    within race_id groups present in frame."""
    f = frame[["race_id", pred_col, target_col]].dropna().copy()
    f["rank"] = f.groupby("race_id")[pred_col].rank(ascending=False, method="first")
    f["grp_n"] = f.groupby("race_id")[pred_col].transform("count")
    f["half_cut"] = np.ceil(f["grp_n"] / 2)

    top1 = f[f["rank"] == 1]
    top4 = f[f["rank"] <= 4]
    tophalf = f[f["rank"] <= f["half_cut"]]

    def mae(d):
        return mean_absolute_error(d[target_col], d[pred_col]) if len(d) else float("nan")

    return {
        "n_races": f["race_id"].nunique(),
        "top1_mae": mae(top1), "top1_n": len(top1),
        "top4_mae": mae(top4), "top4_n": len(top4),
        "tophalf_mae": mae(tophalf), "tophalf_n": len(tophalf),
        "fullfield_mae": mae(f),
    }


def main():
    D = build_frame()
    with open("wpr_models/config.json") as f:
        cfg = json.load(f)

    def tb_lookup(te):
        return [wpr._track_barrier_term(t, d, b, fs, cfg.get("track_barrier_lookup"))
                for t, d, b, fs in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])]

    def trainer_lookup(te):
        return [wpr._merit_term(wpr._merit_bucket(v, cfg.get("trainer_merit_edges")), cfg.get("trainer_merit_lookup"))
                for v in te["trainer_win_pct_365d"]]

    def jockey_lookup(te):
        return [wpr._merit_term(wpr._merit_bucket(v, cfg.get("jockey_merit_edges")), cfg.get("jockey_merit_lookup"))
                for v in te["jockey_win_pct_90d"]]

    def gear_lookup(te):
        return [wpr._gear_change_term(b, cfg.get("gear_change_lookup")) for b in te["gear_bucket"]]

    def closing_lookup(te):
        return [wpr._closing_merit_term(pairs, cfg.get("pace_baseline_lookup")) for pairs in te["closing_pairs"]]

    def _raw_closing_resid(pairs, lookup):
        if not pairs or not lookup:
            return np.nan
        vals = []
        for sect, bucket in pairs:
            exp = lookup.get(bucket)
            if exp is not None and sect is not None and sect == sect:
                vals.append(float(sect) - float(exp))
        return float(np.mean(vals)) if vals else np.nan

    D["closing_raw_resid"] = D["closing_pairs"].apply(lambda p: _raw_closing_resid(p, cfg.get("pace_baseline_lookup")))
    D["closing_n_pairs"] = D["closing_pairs"].apply(len)

    tb_feats = ["cur_distance", "barrier", "field_size", "track_code"]
    trm_feats = ["trainer_win_pct_365d", "field_size"]
    jm_feats = ["jockey_win_pct_90d", "field_size"]
    gc_feats = ["gear_code", "field_size", "first_up", "second_up", "n_runs"]
    cm_feats = ["closing_raw_resid", "closing_n_pairs", "field_size"]

    def fit(trn, feats):
        d = trn.dropna(subset=feats + ["target", "career_avg"])
        m = lgb.LGBMRegressor(n_estimators=150, max_depth=3, learning_rate=0.05,
                              num_leaves=8, random_state=42, verbosity=-1,
                              objective="quantile", alpha=0.5)
        m.fit(d[feats], d["target"] - d["career_avg"])
        return m

    def pred_or_zero(model, frame, feats):
        ok = frame[feats].notna().all(axis=1)
        out = pd.Series(0.0, index=frame.index)
        if ok.any():
            out.loc[ok] = model.predict(frame.loc[ok, feats])
        return out

    since = (D["date"].max() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    print("  building pace_shape ingredients once...")
    race_id_to_score = wpr._build_pace_shape_race_scores(since)
    settle_lookup = wpr._build_pace_shape_settle_lookup(since)
    pace_model = joblib.load("wpr_models/pace_shape.joblib")

    q70, q85, q15, q30 = D["date"].quantile([0.70, 0.85, 0.15, 0.30])
    splits = [
        ("A forward", D[D["date"] < q70], D[D["date"] >= q85].copy()),
        ("B reversed", D[D["date"] > q30], D[D["date"] <= q15].copy()),
    ]

    for label, trn, te in splits:
        print(f"\n=== {label}: trn={len(trn):,} te={len(te):,} ===")
        m_tb, m_trm, m_jm, m_gc, m_cm = (
            fit(trn, tb_feats), fit(trn, trm_feats), fit(trn, jm_feats),
            fit(trn, gc_feats), fit(trn, cm_feats))

        te["track_barrier"] = pred_or_zero(m_tb, te, tb_feats)
        te["trainer_merit"] = pred_or_zero(m_trm, te, trm_feats)
        te["jockey_merit"] = pred_or_zero(m_jm, te, jm_feats)
        te["gear_change"] = pred_or_zero(m_gc, te, gc_feats)
        te["closing_merit"] = pred_or_zero(m_cm, te, cm_feats)
        te["pace_score"] = te["race_id"].map(race_id_to_score)
        te["predicted_rel_settle"] = [settle_lookup.get((h, d)) for h, d in zip(te["horse_lc"], te["date"])]
        te["pace_shape"] = [
            wpr._pace_shape_term(ps, prs, fs, pace_model)
            for ps, prs, fs in zip(te["pace_score"], te["predicted_rel_settle"], te["field_size"])
        ]

        new_sum = wpr._cap_adj_sum(te[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)
        te["pred_new_noslope"] = te["_base"] + new_sum
        te["pred_new_withslope"] = te["_base"] + new_sum * wpr._CALIB_ADJ_SLOPE

        te["track_barrier_shipped"] = tb_lookup(te)
        te["trainer_merit_shipped"] = trainer_lookup(te)
        te["jockey_merit_shipped"] = jockey_lookup(te)
        te["gear_change_shipped"] = gear_lookup(te)
        te["closing_merit_shipped"] = closing_lookup(te)
        shipped_terms = ["own_distance", "own_going", "own_first_up", "own_second_up",
                         "own_trend", "own_long_spell", "track_barrier_shipped",
                         "closing_merit_shipped", "trainer_merit_shipped",
                         "jockey_merit_shipped", "pace_shape"]
        shipped_sum = wpr._cap_adj_sum(te[shipped_terms].to_numpy()).sum(axis=1)
        te["pred_shipped"] = te["_base"] + shipped_sum * wpr._CALIB_ADJ_SLOPE
        # base-only baseline: is the whole adjustment layer (either version)
        # even earning its keep on the runners that matter, or is it a wash?
        te["pred_base_only"] = te["_base"]

        for name, col in [("shipped (lookups + slope)", "pred_shipped"),
                          ("new terms, no slope", "pred_new_noslope"),
                          ("new terms, with slope", "pred_new_withslope"),
                          ("base only (no adjustment layer)", "pred_base_only")]:
            r = rank_mae(te, col)
            print(f"  [{name}] races={r['n_races']}  "
                  f"top1 MAE={r['top1_mae']:.4f} (n={r['top1_n']})  "
                  f"top4 MAE={r['top4_mae']:.4f} (n={r['top4_n']})  "
                  f"tophalf MAE={r['tophalf_mae']:.4f} (n={r['tophalf_n']})  "
                  f"fullfield MAE={r['fullfield_mae']:.4f}")


if __name__ == "__main__":
    main()
