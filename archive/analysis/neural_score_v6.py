"""
neural_score_v6.py - follow-up to v5, per explicit user question: "What
about margins to 2nd pick on both models?"

Mirrors the "genuine dominance" framing the user applied earlier this
session to WPR-only picks (a standout is a big gap to 2nd, not just a
market-price edge) - here applied to the AGREEMENT case: does a CLEAR
top pick on both models (not just a same top-1, but one with real
separation from its own field's 2nd-best) predict better than a close
call that could easily have gone either way?

Two margins computed per race:
  - wpr_margin: wpr_proj_for_rank of the WPR top pick minus its own
    2nd-ranked runner, in WPR points (same units already shown as
    "Proj" on the Race tab).
  - neural_margin: neural_prob_norm (race-normalised, sums to 1 per
    race - see v2/v3's own definition) of the neural top pick minus its
    2nd-ranked runner, in probability points.

Same data pipeline/features/leak-safety/walk-forward design as v3-v5 -
see v1's docstring for the full feature rationale.

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
    "wpr_consistency",
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


def margin_to_2nd(df, group_col, value_col):
    """For the row ranked #1 in each group by value_col, its margin to the
    #2 ranked row (both descending) - NaN (and 0 margin, meaningless) for
    every non-#1 row and for a group with only one entry."""
    def _margin(s):
        sorted_vals = s.sort_values(ascending=False)
        if len(sorted_vals) < 2 or pd.isna(sorted_vals.iloc[0]):
            return pd.Series(np.nan, index=s.index)
        top_idx = sorted_vals.index[0]
        m = sorted_vals.iloc[0] - sorted_vals.iloc[1]
        out = pd.Series(np.nan, index=s.index)
        out[top_idx] = m
        return out
    return df.groupby(group_col)[value_col].transform(_margin)


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
              "avg_400m_pos", "wpr_consistency",
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
    df["finish_position"] = pd.to_numeric(df.get("finish_position"), errors="coerce")
    df["market_price"] = pd.to_numeric(df.get("fixed_win_price"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("starting_price_sp"), errors="coerce")) \
        .combine_first(pd.to_numeric(df.get("price_top"), errors="coerce"))

    df["wpr_proj_for_rank"] = pd.to_numeric(df.get("wprp_proj"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("wpr_nett"), errors="coerce"))
    df["wpr_rank_own"] = df.groupby("race_id")["wpr_proj_for_rank"].rank(ascending=False, method="first")
    # WPR margin doesn't depend on the neural model at all - compute once,
    # upfront, on the full population (not per walk-forward fold).
    df["wpr_margin"] = margin_to_2nd(df, "race_id", "wpr_proj_for_rank")

    pace_dummies = pd.get_dummies(df["pace_scenario"].fillna("unknown"), prefix="pace")
    feature_frame = pd.concat([df[FEATURE_COLS], pace_dummies], axis=1).reset_index(drop=True)
    all_feature_cols = FEATURE_COLS + list(pace_dummies.columns)

    dates = df["date"]
    min_date, max_date = dates.min(), dates.max()
    print(f"\nData spans {min_date.date()} to {max_date.date()} ({len(df):,} rows)")

    fold_starts = pd.date_range(min_date.normalize(), max_date.normalize(), freq="MS")
    if len(fold_starts) < 2:
        print("Not enough date range for monthly walk-forward folds.")
        return

    all_preds = []
    for i in range(1, len(fold_starts)):
        train_end = fold_starts[i]
        test_end = fold_starts[i + 1] if i + 1 < len(fold_starts) else max_date + pd.Timedelta(days=1)
        train_mask = dates < train_end
        test_mask = (dates >= train_end) & (dates < test_end)
        n_train, n_test = train_mask.sum(), test_mask.sum()
        if n_train < 500 or n_test < 20:
            continue

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

        fold_df = df.loc[test_mask, ["race_id", "run_id", "date", "won", "finish_position", "market_price",
                                      "wpr_rank_own", "wpr_margin",
                                      "jockey_win_pct_90d", "trainer_win_pct_365d"]].copy()
        fold_df["neural_proba"] = proba
        all_preds.append(fold_df)
        print(f"  fold {train_end.date()} - {test_end.date()}: train n={n_train}, test n={n_test}")

    preds = pd.concat(all_preds, ignore_index=True)
    preds["neural_rank"] = preds.groupby("race_id")["neural_proba"].rank(ascending=False, method="first")
    preds["neural_prob_norm"] = preds["neural_proba"] / preds.groupby("race_id")["neural_proba"].transform("sum")
    preds["neural_margin"] = margin_to_2nd(preds, "race_id", "neural_prob_norm")
    preds["placed"] = (preds["finish_position"] >= 1) & (preds["finish_position"] <= 3)

    mid = preds["date"].quantile(0.5)
    halves = {"H1": preds[preds["date"] < mid], "H2": preds[preds["date"] >= mid]}
    print(f"\nPooled walk-forward test rows: {len(preds):,} "
          f"({preds['date'].min().date()} to {preds['date'].max().date()})")
    print(f"H1 < {mid.date()}, H2 >= {mid.date()}")

    agree_mask_all = (preds["neural_rank"] == 1) & (preds["wpr_rank_own"] == 1)
    agree_wpr_margin = preds.loc[agree_mask_all, "wpr_margin"]
    agree_neural_margin = preds.loc[agree_mask_all, "neural_margin"]
    print(f"\nAGREE population (n={agree_mask_all.sum()}) wpr_margin distribution: "
          f"median={agree_wpr_margin.median():.2f}, 25th={agree_wpr_margin.quantile(.25):.2f}, "
          f"75th={agree_wpr_margin.quantile(.75):.2f}")
    print(f"AGREE population neural_margin distribution: "
          f"median={agree_neural_margin.median():.4f}, 25th={agree_neural_margin.quantile(.25):.4f}, "
          f"75th={agree_neural_margin.quantile(.75):.4f}\n")

    def strike_and_roi(sub_df, min_n=15):
        sub = sub_df[sub_df["market_price"].notna() & (sub_df["market_price"] > 1)]
        n = len(sub)
        if n < min_n:
            return n, None, None, None
        strike = sub["won"].mean() * 100
        place_strike = sub["placed"].mean() * 100
        units = stake_units(sub["market_price"])
        stake_dollars = units * UNIT_DOLLARS
        payout = np.where(sub["won"] == 1, stake_dollars * sub["market_price"], 0.0)
        roi = (payout - stake_dollars).sum() / stake_dollars.sum() * 100
        return n, strike, place_strike, roi

    def report_both_halves(mask_fn, label):
        results = {}
        for name, half in halves.items():
            mask = mask_fn(half)
            results[name] = strike_and_roi(half[mask])
        n1, s1, p1, r1 = results["H1"]
        n2, s2, p2, r2 = results["H2"]
        both_ok = s1 is not None and s2 is not None and r1 > 0 and r2 > 0
        flag = "  <-- BOTH HALVES POSITIVE ROI" if both_ok else ""
        s1s = f"{s1:.1f}%" if s1 is not None else "n/a"
        s2s = f"{s2:.1f}%" if s2 is not None else "n/a"
        r1s = f"{r1:+.1f}%" if r1 is not None else "n/a"
        r2s = f"{r2:+.1f}%" if r2 is not None else "n/a"
        print(f"{label:<58} H1: n={n1:<5} strike={s1s:<7} ROI={r1s:<8}  "
              f"H2: n={n2:<5} strike={s2s:<7} ROI={r2s:<8}{flag}")
        return both_ok

    print("=== AGREE + WPR margin to 2nd ===")
    for cut in (1, 2, 3, 5):
        report_both_halves(
            lambda h, c=cut: (h["neural_rank"] == 1) & (h["wpr_rank_own"] == 1) & (h["wpr_margin"] >= c),
            f"AGREE AND wpr_margin>={cut} pts")
    print()

    print("=== AGREE + neural margin to 2nd ===")
    for cut in (0.02, 0.05, 0.10, 0.15):
        report_both_halves(
            lambda h, c=cut: (h["neural_rank"] == 1) & (h["wpr_rank_own"] == 1) & (h["neural_margin"] >= c),
            f"AGREE AND neural_margin>={cut:.2f}")
    print()

    print("=== AGREE + BOTH margins (clear on both models) ===")
    for wpr_cut in (1, 2, 3):
        for neural_cut in (0.02, 0.05, 0.10):
            report_both_halves(
                lambda h, wc=wpr_cut, nc=neural_cut: (h["neural_rank"] == 1) & (h["wpr_rank_own"] == 1)
                & (h["wpr_margin"] >= wc) & (h["neural_margin"] >= nc),
                f"AGREE AND wpr_margin>={wpr_cut} AND neural_margin>={neural_cut:.2f}")
    print()

    print("=== AGREE + BOTH margins + jockey/trainer (full combo) ===")
    for wpr_cut, neural_cut in [(1, 0.05), (2, 0.05), (2, 0.10)]:
        for jt_cut in (10, 15):
            report_both_halves(
                lambda h, wc=wpr_cut, nc=neural_cut, jc=jt_cut: (h["neural_rank"] == 1) & (h["wpr_rank_own"] == 1)
                & (h["wpr_margin"] >= wc) & (h["neural_margin"] >= nc)
                & (h["jockey_win_pct_90d"] >= jc) & (h["trainer_win_pct_365d"] >= jc),
                f"AGREE AND wpr_m>={wpr_cut} AND neural_m>={neural_cut:.2f} AND JT>={jt_cut}%")

    print("\nDone.")


if __name__ == "__main__":
    run()
