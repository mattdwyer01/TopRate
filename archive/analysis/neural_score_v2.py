"""
neural_score_v2.py - follow-up to neural_score_v1.py, per explicit user
direction after seeing v1's results (agreement lifts strike rate 32.5%
vs 19.7%/24-26% for either model alone, but ROI is still negative even
on agreement - the market already shortens a horse two independent
systems both like): (1) fix a bug in v1's walk-forward, (2) layer a
market-value/edge filter on top of agreement, (3) layer a jockey/trainer
cutoff on top of agreement (the one signal that held up robustly across
every OTHER rule tested this session).

BUG FIX: v1's SimpleImputer silently DROPPED pfm_score for the first
walk-forward fold (its training window predates pfm_score's 2026-07-24
start entirely, so the column was 100% NaN at fit time, and sklearn's
default behaviour is to drop an all-missing column rather than keep a
constant-fill placeholder) - that fold's model silently trained on one
fewer feature than the other two folds, undetected until the run log's
own imputer warning was read closely. Fixed with
keep_empty_features=True, which fills instead of dropping.

Everything else (feature list, leak-safety reasoning, walk-forward
design, target) is identical to v1 - see that file's docstring for the
full rationale. This file only adds the post-hoc filters on the
AGREEMENT subset and re-validates the base numbers with the fix applied.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.neural_network import MLPClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import roc_auc_score
from sklearn.impute import SimpleImputer

import wpr_void

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"
UNIT_DOLLARS = 50
RETURN_UNITS = 4
MIN_STAKE_UNITS = 0.25
MAX_STAKE_UNITS = 4.0

FEATURE_COLS = [
    "speed_rating", "toprate_rating",
    "early_speed_score", "mid_speed_score", "late_speed_score", "total_speed_score",
    "avg_settled_pos", "avg_800m_pos", "avg_400m_pos",
    "wpr_consistency", "pfm_score",
    "speed_rank_in_race_pct",
    "contested_pace_num",
    "recent_trouble_n",
]


def stake_units(price):
    return np.clip(np.round(RETURN_UNITS / price, 2), MIN_STAKE_UNITS, MAX_STAKE_UNITS)


def load_deduped_form(form_csv):
    print("Loading + deduplicating wpr_form_history.csv.gz...")
    cols = ["horse", "date", "comments_video", "comments_steward", "track", "scrape_date"]
    fh = pd.read_csv(form_csv, usecols=lambda c: c in cols, dtype={"horse": str}, low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    if "scrape_date" in fh.columns:
        fh = fh.sort_values("scrape_date", kind="stable")
    dedup_keys = ["horse_lc", "date"] + (["track"] if "track" in fh.columns else [])
    before = len(fh)
    fh = fh.drop_duplicates(subset=dedup_keys, keep="last")
    print(f"  {before:,} rows -> {len(fh):,} after dedup")
    return fh.sort_values(["horse_lc", "date"]).reset_index(drop=True)


def compute_recent_trouble(runners_df, form_deduped, lookback=3):
    print(f"Computing recent_trouble_n (last {lookback} runs, STRONG markers only)...")
    fh = form_deduped
    trouble_by_horse = {}
    for horse_lc, g in fh.groupby("horse_lc", sort=False):
        dates = g["date"].tolist()
        cvs = g["comments_video"].tolist() if "comments_video" in g.columns else [None] * len(g)
        css = g["comments_steward"].tolist() if "comments_steward" in g.columns else [None] * len(g)
        is_trouble = [wpr_void.void_from_comment_only(cv, cs)[0] for cv, cs in zip(cvs, css)]
        trouble_by_horse[horse_lc] = (dates, is_trouble)

    out = np.zeros(len(runners_df), dtype=float)
    horse_lc_col = runners_df["horse"].astype(str).str.strip().str.lower().to_numpy()
    date_col = runners_df["date"].to_numpy()
    for i in range(len(runners_df)):
        entry = trouble_by_horse.get(horse_lc_col[i])
        if entry is None:
            out[i] = np.nan
            continue
        dates, is_trouble = entry
        prior = [t for dt, t in zip(dates, is_trouble) if dt < date_col[i]]
        out[i] = sum(prior[-lookback:]) if prior else np.nan
    return out


def run():
    print("Loading toprate_runners.csv...")
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    resulted = pd.to_numeric(df.get("resulted"), errors="coerce") == 1
    scratched = pd.to_numeric(df.get("scratched"), errors="coerce").fillna(0) == 1
    df = df[resulted & ~scratched].copy()
    df = df.sort_values("date").reset_index(drop=True)
    df["horse_lc"] = df["horse"].astype(str).str.strip().str.lower()
    print(f"  {len(df):,} resulted, non-scratched runner rows")

    for c in ["speed_rating", "toprate_rating", "early_speed_score", "mid_speed_score",
              "late_speed_score", "total_speed_score", "avg_settled_pos", "avg_800m_pos",
              "avg_400m_pos", "wpr_consistency", "pfm_score",
              "jockey_win_pct_90d", "trainer_win_pct_365d"]:
        df[c] = pd.to_numeric(df.get(c), errors="coerce")

    df["field_size_active"] = df.groupby("race_id")["run_id"].transform("count")
    df["speed_rank_in_race_pct"] = df.groupby("race_id")["speed_rating"] \
        .rank(ascending=False, method="average") / df["field_size_active"]
    df["contested_pace_num"] = df.get("contested_pace").map(
        {True: 1, False: 0, "True": 1, "False": 0}).astype(float) if "contested_pace" in df.columns else np.nan

    form_deduped = load_deduped_form(FORM_CSV)
    df["recent_trouble_n"] = compute_recent_trouble(df, form_deduped)

    df["won"] = pd.to_numeric(df["won"], errors="coerce").fillna(0).astype(int)
    df["market_price"] = pd.to_numeric(df.get("fixed_win_price"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("starting_price_sp"), errors="coerce")) \
        .combine_first(pd.to_numeric(df.get("price_top"), errors="coerce"))
    df["market_prob"] = 1.0 / df["market_price"]

    df["wpr_proj_for_rank"] = pd.to_numeric(df.get("wprp_proj"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("wpr_nett"), errors="coerce"))
    df["wpr_rank_own"] = df.groupby("race_id")["wpr_proj_for_rank"].rank(ascending=False, method="first")

    pace_dummies = pd.get_dummies(df["pace_scenario"].fillna("unknown"), prefix="pace")
    feature_frame = pd.concat([df[FEATURE_COLS], pace_dummies], axis=1).reset_index(drop=True)
    all_feature_cols = FEATURE_COLS + list(pace_dummies.columns)

    dates = df["date"]
    min_date, max_date = dates.min(), dates.max()
    print(f"\nData spans {min_date.date()} to {max_date.date()} ({len(df):,} rows)")

    fold_starts = pd.date_range(min_date.normalize(), max_date.normalize(), freq="MS")
    if len(fold_starts) < 3:
        print("Not enough date range for monthly walk-forward folds.")
        return

    all_preds = []
    for i in range(2, len(fold_starts)):
        train_end = fold_starts[i]
        test_end = fold_starts[i + 1] if i + 1 < len(fold_starts) else max_date + pd.Timedelta(days=1)
        train_mask = dates < train_end
        test_mask = (dates >= train_end) & (dates < test_end)
        n_train, n_test = train_mask.sum(), test_mask.sum()
        if n_train < 500 or n_test < 20:
            continue

        # keep_empty_features=True: v1's bug - an all-NaN-at-fit-time
        # column (pfm_score, in the earliest fold, predates its 2026-07-24
        # start) was silently DROPPED by the default imputer instead of
        # filled, so that fold's model trained on one fewer feature than
        # the others without erroring. This keeps every fold's feature
        # count consistent.
        imputer = SimpleImputer(strategy="median", keep_empty_features=True)
        X_train = imputer.fit_transform(feature_frame.loc[train_mask, all_feature_cols])
        y_train = df.loc[train_mask, "won"].to_numpy()
        X_test = imputer.transform(feature_frame.loc[test_mask, all_feature_cols])

        scaler = StandardScaler()
        X_train = scaler.fit_transform(X_train)
        X_test = scaler.transform(X_test)

        clf = MLPClassifier(hidden_layer_sizes=(16, 8), max_iter=500, random_state=42,
                             early_stopping=True, alpha=1e-3)
        clf.fit(X_train, y_train)
        proba = clf.predict_proba(X_test)[:, 1]

        fold_df = df.loc[test_mask, ["race_id", "run_id", "date", "won", "market_price", "market_prob",
                                      "wpr_rank_own", "jockey_win_pct_90d", "trainer_win_pct_365d"]].copy()
        fold_df["neural_proba"] = proba
        all_preds.append(fold_df)
        print(f"  fold {train_end.date()} - {test_end.date()}: train n={n_train}, test n={n_test}")

    preds = pd.concat(all_preds, ignore_index=True)
    preds["neural_rank"] = preds.groupby("race_id")["neural_proba"].rank(ascending=False, method="first")
    # Race-normalised model probability (sums to 1 per race, comparable to
    # market_prob) - raw predict_proba outputs don't sum to 1 across a
    # field since each runner was scored independently.
    preds["neural_prob_norm"] = preds["neural_proba"] / preds.groupby("race_id")["neural_proba"].transform("sum")
    preds["neural_edge"] = preds["neural_prob_norm"] - preds["market_prob"]

    print(f"\nPooled walk-forward test rows: {len(preds):,}")
    auc = roc_auc_score(preds["won"], preds["neural_proba"])
    print(f"Neural score AUC (pooled, bug fixed): {auc:.4f}")

    def strike_and_roi(mask, label, min_n=15):
        sub = preds[mask & preds["market_price"].notna() & (preds["market_price"] > 1)]
        n = len(sub)
        if n < min_n:
            print(f"  {label}: n={n} (too few)")
            return
        strike = sub["won"].mean() * 100
        units = stake_units(sub["market_price"])
        stake_dollars = units * UNIT_DOLLARS
        payout = np.where(sub["won"] == 1, stake_dollars * sub["market_price"], 0.0)
        roi = (payout - stake_dollars).sum() / stake_dollars.sum() * 100
        print(f"  {label}: n={n:<6} strike={strike:5.1f}%  ROI={roi:+6.1f}%")

    print("\n=== Baseline (re-check with bug fixed) ===")
    strike_and_roi(preds["neural_rank"] == 1, "Neural top-1")
    strike_and_roi(preds["wpr_rank_own"] == 1, "WPR top-1 (same pooled rows)")

    agree_mask = (preds["neural_rank"] == 1) & (preds["wpr_rank_own"] == 1)
    disagree_mask = (preds["neural_rank"] == 1) & (preds["wpr_rank_own"] != 1)
    print("\n=== Agreement test (bug fixed) ===")
    strike_and_roi(agree_mask, "AGREE (both pick the same horse)")
    strike_and_roi(disagree_mask, "DISAGREE (neural top-1, not WPR's)")

    print("\n=== AGREE + market-value/edge filter ===")
    for cut in (0.0, 0.03, 0.05, 0.08):
        strike_and_roi(agree_mask & (preds["neural_edge"] >= cut), f"AGREE AND edge>={cut:.2f}")

    print("\n=== AGREE + jockey/trainer cutoff ===")
    for cut in (10, 15, 18, 20):
        jt_mask = (preds["jockey_win_pct_90d"] >= cut) & (preds["trainer_win_pct_365d"] >= cut)
        strike_and_roi(agree_mask & jt_mask, f"AGREE AND jockey/trainer>={cut}%")

    print("\n=== AGREE + edge + jockey/trainer (full combo) ===")
    for edge_cut in (0.0, 0.05):
        for jt_cut in (15, 18):
            jt_mask = (preds["jockey_win_pct_90d"] >= jt_cut) & (preds["trainer_win_pct_365d"] >= jt_cut)
            strike_and_roi(agree_mask & (preds["neural_edge"] >= edge_cut) & jt_mask,
                           f"AGREE AND edge>={edge_cut:.2f} AND jockey/trainer>={jt_cut}%")

    print("\nDone.")


if __name__ == "__main__":
    run()
