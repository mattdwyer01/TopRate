"""
wpr_interim_trial_scoping_check.py - extends the trials/jumpouts
investigation (debut case already shipped) to horses that ALREADY have
real race history: does a trial/jumpout run BETWEEN a horse's last real
run and its next real run carry incremental signal, for two cases -
(a) first-up: the intervening gap is a genuine spell (>_SPELL_GAP_DAYS)
and a trial preceded the first-up return, (b) mid-prep: a normal short
gap between real runs, with a freshen-up trial squeezed in between.

DIFFERENT QUESTION from the debut case: there the horse had ZERO real
history, so the trial estimate WAS the base rating. Here the horse
already has a real projection from its own career history (ewm3,
career_avg, etc, all UNCHANGED) - the question is whether the trial adds
INCREMENTAL signal on top of what the existing model already knows, not
whether it can replace missing history.

METHOD (scoping only, not yet leak-free K-fold validated): for every
resulted real row in the training frame with first_up==1 or a normal-gap
mid-prep return, find any trial/jumpout rows strictly between the
horse's PRIOR real run and THIS run, using the same raw wpr_form_history
read as the debut scoping check. Compute the same trial-feature summary
(avg_finish_pct, won_a_trial, n_trials, avg_margin, days_since_last_
trial) and correlate against the residual of the CURRENT (unchanged)
model's own projection for that row - not the raw target, so this
isolates what the trial adds BEYOND the existing model's own signal.

RESULT: first-up + intervening trial (n=2,852) shows a real, sensible
pattern - the model already over-predicts first-up runners on average
(known behaviour), but that over-prediction shrinks sharply with better
trial form: bottom trial-finish quartile resid=-1.92, top quartile
resid=-0.05; won-a-trial resid=-0.13 vs didn't-win resid=-0.997.
Mid-prep + freshen-up trial (n=774) shows no useful pattern - near-zero
correlations, non-monotonic quartiles. Follow-up (K=4-fold leak-free
validated correction): wpr_first_up_trial_correction_kfold_test.py.

NO EM DASHES policy: hyphens only in this file.
"""
import json
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base

FORM_CSV = "wpr_form_history.csv.gz"
CACHE_PATH = "/tmp/wpr_full_training_frame_cache.pkl"


def build_trial_intervals():
    """Per horse, every trial/jumpout row with its date - used to find
    trials strictly between two given dates for that horse."""
    df = pd.read_csv(FORM_CSV, low_memory=False,
                      usecols=["horse_id", "date", "isBarrierTrial", "is_jumpout",
                               "positionFinish", "field_size", "marginFinish"])
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df = df.dropna(subset=["date", "horse_id"])
    df["is_trial"] = (df["isBarrierTrial"] == True) | (df["is_jumpout"] == True)
    trials = df[df["is_trial"]].sort_values(["horse_id", "date"])
    return dict(tuple(trials.groupby("horse_id")))


def trial_features(trial_group, lo_date, hi_date):
    """Trials for one horse strictly between lo_date (exclusive) and
    hi_date (exclusive)."""
    if trial_group is None:
        return None
    t = trial_group[(trial_group["date"] < hi_date) & (trial_group["date"] > lo_date)]
    if len(t) == 0:
        return None
    pos = pd.to_numeric(t["positionFinish"], errors="coerce")
    fs = pd.to_numeric(t["field_size"], errors="coerce")
    valid = pos.notna() & fs.notna() & (fs > 0)
    if not valid.any():
        return None
    pos, fs, t = pos[valid], fs[valid], t[valid]
    finish_pct = 1 - (pos - 1) / fs
    margin = pd.to_numeric(t["marginFinish"], errors="coerce")
    return {
        "n_trials": len(t),
        "avg_finish_pct": float(finish_pct.mean()),
        "best_finish_pct": float(finish_pct.max()),
        "won_a_trial": float((pos == 1).max()),
        "avg_margin": float(margin.mean()) if margin.notna().any() else np.nan,
        "days_since_last_trial": float((hi_date - t["date"].max()).days),
    }


def run():
    with open(CACHE_PATH, "rb") as fh:
        _, full = pickle.load(fh)
    full = full.drop(columns=["_base"], errors="ignore")
    full = add_base(full)

    with open("wpr_models/config.json") as f:
        cfg = json.load(f)
    tb_lookup = cfg["track_barrier_lookup"]
    full["track_barrier"] = [
        wpr._track_barrier_term(t, d, b, fs, tb_lookup)
        for t, d, b, fs in zip(full["track"], full["cur_distance"], full["barrier"], full["field_size"])
    ]
    pb_lookup = cfg["pace_baseline_lookup"]
    full["closing_merit"] = [wpr._closing_merit_term(pairs, pb_lookup) for pairs in full["closing_pairs"]]
    tm_edges, tm_lookup = cfg["trainer_merit_edges"], cfg["trainer_merit_lookup"]
    jm_edges, jm_lookup = cfg["jockey_merit_edges"], cfg["jockey_merit_lookup"]
    full["trainer_merit"] = [wpr._merit_term(wpr._merit_bucket(v, tm_edges), tm_lookup)
                              for v in full["trainer_win_pct_365d"]]
    full["jockey_merit"] = [wpr._merit_term(wpr._merit_bucket(v, jm_edges), jm_lookup)
                             for v in full["jockey_win_pct_90d"]]

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                      if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg", "first_up", "days_since", "n_runs"] +
                        non_pop_terms + ["barrier", "field_size", "track", "cur_distance",
                                          "trainer_win_pct_365d", "jockey_win_pct_90d"])
    full["_base_calib"] = full["_base"].apply(wpr._calibrate_base)
    full["adj_total"] = wpr._cap_adj_sum(full[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
    full["proj"] = full["_base_calib"] + full["adj_total"]
    full["resid"] = full["target"] - full["proj"]
    print(f"scoped rows: {len(full):,}")

    trial_by_horse = build_trial_intervals()

    # last real run date = today's date minus days_since (both already
    # leak-safe, pre-race-known quantities in the training frame).
    full["last_real_date"] = full["date"] - pd.to_timedelta(full["days_since"], unit="D")

    def _get_feat(row):
        tg = trial_by_horse.get(row["horse_id"])
        return trial_features(tg, row["last_real_date"], row["date"])

    print("Computing intervening-trial features per row (this scans every eligible row)...")
    feats = full.apply(_get_feat, axis=1)
    has_trial = feats.notna()
    print(f"rows with an intervening trial/jumpout: {has_trial.sum():,} / {len(full):,}")

    feat_df = pd.DataFrame(list(feats[has_trial]), index=full.index[has_trial])
    feat_df = feat_df.add_prefix("trial_")
    scoped = full.loc[has_trial].join(feat_df)

    first_up_grp = scoped[scoped["first_up"] == 1]
    mid_prep_grp = scoped[(scoped["first_up"] == 0) & (scoped["n_runs"] >= 1)]

    for grp, label in [(first_up_grp, "FIRST-UP with intervening trial"),
                        (mid_prep_grp, "MID-PREP with intervening trial (freshen-up)")]:
        print(f"\n=== {label} (n={len(grp):,}) ===")
        if len(grp) < 30:
            print("  too few rows to say anything reliable")
            continue
        for feat in ["trial_avg_finish_pct", "trial_best_finish_pct", "trial_won_a_trial",
                     "trial_n_trials", "trial_days_since_last_trial"]:
            corr = grp[feat].corr(grp["resid"])
            print(f"  corr({feat}, resid) = {corr:.4f}")
        print(f"  mean resid by avg_finish_pct quartile:")
        g2 = grp.dropna(subset=["trial_avg_finish_pct"]).copy()
        if len(g2) >= 20:
            g2["_q"] = pd.qcut(g2["trial_avg_finish_pct"], 4, duplicates="drop")
            print(g2.groupby("_q", observed=True)["resid"].agg(["mean", "count"]))
        print(f"  mean resid: won a trial={grp[grp['trial_won_a_trial']==1]['resid'].mean():.3f} "
              f"(n={ (grp['trial_won_a_trial']==1).sum() })  "
              f"did not={grp[grp['trial_won_a_trial']==0]['resid'].mean():.3f} "
              f"(n={ (grp['trial_won_a_trial']==0).sum() })")


if __name__ == "__main__":
    run()
