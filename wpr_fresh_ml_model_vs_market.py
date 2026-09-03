"""
wpr_fresh_ml_model_vs_market.py - "starting fresh": can a genuinely
different modelling approach (a real gradient-boosted classifier
trained directly on win/loss, not WPR's hand-crafted additive
base+adjustment regression) beat the market favourite on strike rate or
ROI, using the SAME underlying data this whole investigation has used?

WHY THIS IS A GENUINELY DIFFERENT ATTEMPT, NOT MORE OF THE SAME: every
test so far (edge-vs-market, isotonic recalibration, top-pick-margin,
rank hit-rate, price steam/drift) used WPR's OWN projected_wpr as the
starting signal, then asked whether some transformation or selection
rule on top of it could find profit. This instead throws that away and
trains a fresh LightGBM binary classifier directly on won/lost, given
the same rich per-runner feature set wpr.build_training_frame() already
computes (own-history rolling stats, sectional-time/pace features,
class-move, settle-position tendencies, trainer/jockey win rates,
barrier, field size, race class, going) - i.e. does a model that lets
gradient boosting find its own feature interactions and nonlinearities,
rather than a hand-tuned additive formula, do any better.

WHAT'S DELIBERATELY EXCLUDED FROM FEATURES (to keep this a fair,
non-circular test): fixed_win_price, starting_price_sp, pfm_score (any
price-derived signal) - the whole question is whether a model built
from FORM DATA ALONE can match or beat what the market's price already
implies, not whether stacking more stuff on top of the market price
can nudge it slightly - same standard wpr_projection.py itself has
always been held to (it never uses price as an input either). Also
excluded: identifiers (race_id, horse_id, horse, run_id), the raw date,
free-text comment fields (comments_video/comments_steward - would need
NLP, out of scope here), and `target` (the actual dependent variable
build_training_frame() computes for WPR's own regression - using it as
a FEATURE would be pure leakage of the answer).

METHOD: K=4 chronological folds (train on 3, predict the 4th, rotate) -
LightGBM binary classifier (objective=binary, native categorical
support for race_class/going/state, native missing-value handling, no
manual imputation needed). Held-out predictions pooled, then scored
with the EXACT SAME methodology as every other script this session:
per-race renormalised probability, Brier score / calibration table
(market as the sanity baseline), ROI by edge-magnitude bucket at
beta-equivalent softmax=identity (predicted prob used directly, no
extra scaling needed since it's already a calibrated-by-training
probability), and the same top-pick win-rate/place-rate/rank comparison
against the market favourite as wpr_rank_margin_detail_stats.py.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
import time
from pathlib import Path

import numpy as np
import pandas as pd
import lightgbm as lgb
from sklearn.isotonic import IsotonicRegression

import wpr_projection as wpr
from wpr_own_pace_backtest import merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date
from wpr_bet_selection_post_retrain import merge_price_pfm, RUNNERS_CSV

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
N_FOLDS = 4
RETURN_UNITS = 4
PRICE_CAP = 26.0
EDGE_THRESHOLD = 0.05

EXCLUDE_COLS = {
    "target", "won", "race_id", "horse_id", "horse", "run_id", "date",
    "comments_video", "comments_steward", "fixed_win_price", "starting_price_sp",
    "pfm_score", "track",
    # closing_pairs is a raw list-of-tuples (internal input to closing_merit's
    # own fitted lookup, not a usable scalar feature) - excluded rather than
    # engineered further here, out of scope for this first attempt.
    "closing_pairs",
    # LEAK, confirmed by direct inspection (Sep 2026): build_training_frame()'s
    # own internal wpr_nett merge (wpr_projection.py ~line 2905) joins on
    # run_id, which is NOT a per-historical-row race identifier - every row
    # in a horse's scraped history batch shares the run_id of whichever race
    # triggered that scrape, so ALL of a horse's historical rows get stamped
    # with the SAME wpr_nett value (whatever TopRate's rating was as of the
    # LATEST scrape), not that row's own point-in-time pre-race rating.
    # Verified directly: horse_id 300668 shows wpr_nett=84.1 identically
    # across 12 rows spanning 2026-04-27 to 2026-08-28. This is real look-
    # ahead leakage for offline analysis (a horse's April row sees its
    # September rating) - NOT a live-serving bug, since project_race()'s
    # own live path reads cur_wpr_nett fresh from today's own runners.csv
    # row, never a historical merge. Excluded here; a first (implausibly
    # good: Brier beats market, +54.6% ROI t=17.72) run of this exact
    # script WITH wpr_nett included is what surfaced the leak - wpr_nett
    # was the dominant feature by a wide margin (1045 vs race_class's 749).
    "wpr_nett",
}
CATEGORICAL_COLS = ["race_class", "going", "state", "cur_settle_band"]


def build_full():
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            return full
        print("Cache is stale - rebuilding.")
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return full


def merge_extra(full):
    tr = pd.read_csv(RUNNERS_CSV, dtype={"race_id": str}, low_memory=False,
                      usecols=["race_id", "horse", "date", "state", "prize_money", "finish_position"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr = tr.dropna(subset=["date"]).drop_duplicates(subset=["horse", "date", "race_id"], keep="first")
    full = full.merge(tr, on=["race_id", "horse", "date"], how="left")
    return full


def run():
    full = build_full()
    full["date"] = pd.to_datetime(full["date"])
    full = merge_extra(full)

    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["price"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["price", "won", "date"])
    full = full[full["price"] > 1.0]
    full["won"] = pd.to_numeric(full["won"], errors="coerce").fillna(0).astype(int)
    full = full.sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}  ({full['date'].min().date()} to {full['date'].max().date()})")

    # gear_changes is a JSON-stringified list of specific gear notes (near-
    # unbounded distinct combinations - "Blinkers Again", "Winkers Off Again
    # + Tongue Tie Again", etc.) - too high-cardinality to treat as a plain
    # category, collapsed to a simple "gear changed today at all" flag
    # instead (a real, commonly-cited racing angle in its own right).
    full["gear_change_flag"] = (full["gear_changes"].astype(str) != "[]").astype(int)

    feature_cols = [c for c in full.columns if c not in EXCLUDE_COLS
                     and c not in ("price", "finish_position", "gear_changes")]
    print(f"Feature count: {len(feature_cols)}")

    X = full[feature_cols].copy()
    for c in CATEGORICAL_COLS:
        if c in X.columns:
            X[c] = X[c].astype("category")
    y = full["won"].to_numpy()

    n = len(full)
    fold_edges = np.array_split(np.arange(n), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[full.index[idx], "_fold"] = i

    pred_prob = pd.Series(index=full.index, dtype=float)
    t0 = time.time()
    for i in range(N_FOLDS):
        test_mask = full["_fold"] == i
        train_mask = ~test_mask
        model = lgb.LGBMClassifier(
            objective="binary", n_estimators=400, learning_rate=0.03,
            num_leaves=31, min_child_samples=50, subsample=0.8, colsample_bytree=0.8,
            reg_lambda=1.0, random_state=42, verbosity=-1,
        )
        model.fit(X[train_mask], y[train_mask], categorical_feature=[c for c in CATEGORICAL_COLS if c in X.columns])
        pred_prob.loc[test_mask] = model.predict_proba(X[test_mask])[:, 1]
        print(f"  fold {i}: trained on {train_mask.sum():,}, predicted {test_mask.sum():,} "
              f"({time.time()-t0:.0f}s elapsed)")

    full["raw_pred"] = pred_prob

    def _renorm(g):
        s = g["raw_pred"].sum()
        return g["raw_pred"] / s if s > 0 else g["raw_pred"]
    full["model_prob"] = full.groupby("race_id", group_keys=False).apply(_renorm)

    def _market_prob(g):
        inv = 1.0 / g["price"].to_numpy(dtype=float)
        return pd.Series(inv / inv.sum(), index=g.index)
    full["market_prob"] = full.groupby("race_id", group_keys=False).apply(_market_prob)
    full["edge"] = full["model_prob"] - full["market_prob"]

    def brier(p, w):
        return float(np.mean((p - w) ** 2))

    print(f"\n{'='*90}\nCALIBRATION: fresh ML model vs market\n{'='*90}")
    print(f"  Brier (market):        {brier(full['market_prob'], full['won']):.4f}")
    print(f"  Brier (fresh ML model): {brier(full['model_prob'], full['won']):.4f}")

    def calib_table(prob_col, label):
        d = full[["won", prob_col]].copy()
        d["bucket"] = pd.qcut(d[prob_col], 10, duplicates="drop")
        g = d.groupby("bucket", observed=True).agg(n=("won", "size"), mean_pred=(prob_col, "mean"),
                                                     actual_rate=("won", "mean"))
        print(f"\n  --- {label} ---")
        print(g.to_string(formatters={"mean_pred": "{:.1%}".format, "actual_rate": "{:.1%}".format}))

    calib_table("market_prob", "market")
    calib_table("model_prob", "fresh ML model")

    # top-pick comparison, same structure as wpr_rank_margin_detail_stats.py
    field_size = full.groupby("race_id")["model_prob"].transform("size")
    scoped = full[field_size >= 4].copy()
    scoped["model_rank"] = scoped.groupby("race_id")["model_prob"].rank(ascending=False, method="first").astype(int)
    scoped["market_rank"] = scoped.groupby("race_id")["price"].rank(ascending=True, method="first").astype(int)
    scoped["finish_position"] = pd.to_numeric(scoped["finish_position"], errors="coerce")

    print(f"\n{'='*90}\nTOP PICK: fresh ML model vs market favourite (field>=4, n={scoped['race_id'].nunique():,} races)\n{'='*90}")
    for rank_col, label in [("model_rank", "fresh ML model"), ("market_rank", "market favourite")]:
        top1 = scoped[scoped[rank_col] == 1]
        win_rate = top1["won"].mean() * 100
        p3 = (top1["finish_position"] <= 3).mean() * 100
        print(f"  {label:<18} win rate={win_rate:5.1f}%  place-top3={p3:5.1f}%  n={len(top1):,}")

    # ROI at PRICE_CAP, EDGE_THRESHOLD
    bets = scoped[(scoped["edge"] >= EDGE_THRESHOLD) & (scoped["price"] <= PRICE_CAP)]
    if len(bets) >= 20:
        stake = RETURN_UNITS / bets["price"].to_numpy()
        profit = np.where(bets["won"] == 1, RETURN_UNITS - stake, -stake)
        staked = stake.sum()
        roi = profit.sum() / staked * 100
        se = profit.std(ddof=1) / np.sqrt(len(profit))
        t = profit.mean() / se if se > 0 else float("nan")
        print(f"\n{'='*90}\nROI: fresh ML model, edge>={EDGE_THRESHOLD}, price<=${PRICE_CAP:.0f}\n{'='*90}")
        print(f"  n={len(bets):,}  strike={bets['won'].mean()*100:.1f}%  ROI={roi:+.1f}%  t={t:+.2f}")
    else:
        print(f"\nToo few edge>={EDGE_THRESHOLD} bets to score ROI (n={len(bets)})")

    print("\nFeature importance (top 20, from the last fold's model):")
    imp = pd.Series(model.feature_importances_, index=X.columns).sort_values(ascending=False)
    print(imp.head(20).to_string())

    print("\nSame caveats as always: leak-free K-fold, but one dataset, one attempt - a hypothesis,")
    print("not a guarantee, and gradient boosting on ~45k rows / 5 months is a small-data regime")
    print("for this kind of model (real quant shops use vastly more races before trusting a GBM).")


if __name__ == "__main__":
    run()
