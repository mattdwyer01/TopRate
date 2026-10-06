"""
neural_score_v1.py - first attempt at a genuinely SECOND, independent
prediction alongside WPR (user request, Sep 2026): "add different data
points ... towards a neural score, and be another way to predict a race
alongside WPR prediction. Ideally when both neural & WPR prediction
align, it should mean a bet".

DELIBERATELY uses only fields WPR's own model (wpr_projection.py) does
NOT already consume - see ADJ_TERMS/_compute_base there. If the two
scores shared inputs, "agreement" would be close to tautological (of
course two functions of mostly the same data agree). Excluded on that
basis: wpr_nett, ewm5/trailing WPR form, jockey_win_pct_90d,
trainer_win_pct_365d, barrier/distance/going (all already ADJ_TERMS or
base inputs).

FEATURES (all verified pre-race / leak-safe by reading toprate_daily.py's
own capture code before including anything - see each block below):
  - speed_rating, toprate_rating: scraped once at initial pre-race fetch
    (same "d" API response wpr_nett itself comes from) - never
    overwritten post-race.
  - early/mid/late/total_speed_score, avg_settled_pos, avg_800m_pos,
    avg_400m_pos, wpr_consistency: computed from form[:5] (the horse's
    OWN prior runs) at fetch time - genuinely trailing, not today's race.
  - speed_rank_in_race, pace_scenario, contested_pace: same-day
    same-race comparisons, but built purely from the above pre-race
    speed_rating values across the field - no post-race data involved.
  - pfm_score: third-party (Punting Form) score, same capture timing as
    speed_rating/toprate_rating.
  - recent_trouble_n: NEW engineered feature, not in the raw CSV at all -
    count of the horse's last 3 PRIOR runs (strictly date < race_date)
    whose comments_video/comments_steward trip wpr_void.py's STRONG
    marker list (vet/lame/bled/checked/fell/etc). comments_video/
    comments_steward themselves are confirmed POST-race, settling DAYS
    after a run (see toprate_daily.py's "final weight-adjusted WPR ...
    and comments settle DAYS after a race" comment) - unsafe as a
    same-race feature, but safe as a trailing signal about a horse's
    recent history, exactly like ewm5. wpr_form_history.csv.gz's own
    per-run comments are used here, dated strictly before the race being
    predicted.

TARGET: won (binary) - this model predicts the same thing WPR ultimately
serves as a price for (who wins), not WPR's own wpr_actual rating - a
literal trained model per user request, evaluated the way a classifier
should be (AUC, top-1-in-race strike rate), not a regression MAE.

VALIDATION: walk-forward, same rigor bar as calibrate_edge_score.py's
own audit (refit on strictly-prior data, walk across the full history) -
never a single random train/test split, which would let future data leak
into training via shared jockeys/trainers/horses across the split.

wpr_form_history.csv.gz dedup: MANDATORY (see wpr_rank_conjunction_
screen_v9_deduped.py's 42%-duplicate-rows finding this same session) -
skipping it silently corrupts any trailing average computed from this
file, comments included.

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
    "speed_rank_in_race_pct",  # normalised 0-1 by field size, not raw rank
    "contested_pace_num",
    "recent_trouble_n",
]
CATEGORICAL_COLS = ["pace_scenario"]


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
    """For each runner row, count STRONG trouble markers (wpr_void's own
    list) in the horse's last `lookback` runs strictly before race_date.
    Pure trailing lookup via merge_asof-style manual grouping - never
    touches the current race's own (post-race, unsafe) comments."""
    print(f"Computing recent_trouble_n (last {lookback} runs, STRONG markers only)...")
    fh = form_deduped
    trouble_by_horse = {}
    for horse_lc, g in fh.groupby("horse_lc", sort=False):
        dates = g["date"].tolist()
        cvs = g["comments_video"].tolist() if "comments_video" in g.columns else [None] * len(g)
        css = g["comments_steward"].tolist() if "comments_steward" in g.columns else [None] * len(g)
        is_trouble = [
            wpr_void.void_from_comment_only(cv, cs)[0]
            for cv, cs in zip(cvs, css)
        ]
        trouble_by_horse[horse_lc] = (dates, is_trouble)

    out = np.zeros(len(runners_df), dtype=float)
    horse_lc_col = runners_df["horse"].astype(str).str.strip().str.lower().to_numpy()
    date_col = runners_df["date"].to_numpy()
    for i in range(len(runners_df)):
        h = horse_lc_col[i]
        d = date_col[i]
        entry = trouble_by_horse.get(h)
        if entry is None:
            out[i] = np.nan
            continue
        dates, is_trouble = entry
        prior = [t for dt, t in zip(dates, is_trouble) if dt < d]
        if not prior:
            out[i] = np.nan
            continue
        out[i] = sum(prior[-lookback:])
    return out


def run():
    print("Loading toprate_runners.csv...")
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    resulted = pd.to_numeric(df.get("resulted"), errors="coerce") == 1
    scratched = pd.to_numeric(df.get("scratched"), errors="coerce").fillna(0) == 1
    df = df[resulted & ~scratched].copy()
    # Sorted and index-reset BEFORE any feature engineering below, so every
    # later frame built from df (feature_frame, pace_dummies, ...) shares
    # the exact same row order/index throughout - building it after led to
    # a label mismatch (feature_frame's pre-sort index vs df's post-sort
    # reset index).
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df = df.sort_values("date").reset_index(drop=True)
    df["horse_lc"] = df["horse"].astype(str).str.strip().str.lower()
    print(f"  {len(df):,} resulted, non-scratched runner rows")

    for c in ["speed_rating", "toprate_rating", "early_speed_score", "mid_speed_score",
              "late_speed_score", "total_speed_score", "avg_settled_pos", "avg_800m_pos",
              "avg_400m_pos", "wpr_consistency", "pfm_score"]:
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

    # WPR's own top pick (for the agreement check) - rank by wpr_nett's
    # own projection if present, else the raw rating. Uses wprp_proj
    # (the actual served projection) when available, matching what a
    # bettor actually sees.
    df["wpr_proj_for_rank"] = pd.to_numeric(df.get("wprp_proj"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("wpr_nett"), errors="coerce"))
    df["wpr_rank_own"] = df.groupby("race_id")["wpr_proj_for_rank"].rank(ascending=False, method="first")

    # One-hot the lone categorical feature.
    pace_dummies = pd.get_dummies(df["pace_scenario"].fillna("unknown"), prefix="pace")
    feature_frame = pd.concat([df[FEATURE_COLS], pace_dummies], axis=1).reset_index(drop=True)
    all_feature_cols = FEATURE_COLS + list(pace_dummies.columns)

    dates = df["date"]
    min_date, max_date = dates.min(), dates.max()
    print(f"\nData spans {min_date.date()} to {max_date.date()} ({len(df):,} rows)")

    # Walk-forward: monthly folds. Each fold trains on everything strictly
    # before the fold's start date, predicts the fold itself. First two
    # months skipped as pure burn-in (need enough training data first).
    fold_starts = pd.date_range(min_date.normalize(), max_date.normalize(), freq="MS")
    if len(fold_starts) < 3:
        print("Not enough date range for monthly walk-forward folds.")
        return

    all_preds = []
    imputer = SimpleImputer(strategy="median")
    for i in range(2, len(fold_starts)):
        train_end = fold_starts[i]
        test_end = fold_starts[i + 1] if i + 1 < len(fold_starts) else max_date + pd.Timedelta(days=1)
        train_mask = dates < train_end
        test_mask = (dates >= train_end) & (dates < test_end)
        n_train, n_test = train_mask.sum(), test_mask.sum()
        if n_train < 500 or n_test < 20:
            continue

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

        fold_df = df.loc[test_mask, ["race_id", "run_id", "date", "won", "market_price", "wpr_rank_own"]].copy()
        fold_df["neural_proba"] = proba
        all_preds.append(fold_df)
        print(f"  fold {train_end.date()} - {test_end.date()}: train n={n_train}, test n={n_test}")

    if not all_preds:
        print("No folds produced predictions.")
        return

    preds = pd.concat(all_preds, ignore_index=True)
    preds["neural_rank"] = preds.groupby("race_id")["neural_proba"].rank(ascending=False, method="first")

    print(f"\nPooled walk-forward test rows: {len(preds):,}")
    auc = roc_auc_score(preds["won"], preds["neural_proba"])
    print(f"Neural score AUC (pooled): {auc:.4f}")

    def strike_and_roi(mask, label):
        sub = preds[mask & preds["market_price"].notna() & (preds["market_price"] > 1)]
        n = len(sub)
        if n == 0:
            print(f"  {label}: n=0")
            return
        strike = sub["won"].mean() * 100
        units = stake_units(sub["market_price"])
        stake_dollars = units * UNIT_DOLLARS
        payout = np.where(sub["won"] == 1, stake_dollars * sub["market_price"], 0.0)
        roi = (payout - stake_dollars).sum() / stake_dollars.sum() * 100
        print(f"  {label}: n={n:<6} strike={strike:5.1f}%  ROI={roi:+6.1f}%")

    print("\n=== Top-1 strike rate/ROI comparison ===")
    strike_and_roi(preds["neural_rank"] == 1, "Neural top-1")
    strike_and_roi(preds["wpr_rank_own"] == 1, "WPR top-1 (same pooled rows)")

    print("\n=== Agreement test: does WPR top-1 == Neural top-1 predict better? ===")
    agree_mask = (preds["neural_rank"] == 1) & (preds["wpr_rank_own"] == 1)
    disagree_mask = (preds["neural_rank"] == 1) & (preds["wpr_rank_own"] != 1)
    strike_and_roi(agree_mask, "AGREE (both pick the same horse)")
    strike_and_roi(disagree_mask, "DISAGREE (neural top-1, but not WPR's)")

    print("\nDone.")


if __name__ == "__main__":
    run()
