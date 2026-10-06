"""
wpr_edge_two_feature_test.py - tests a trainer/jockey-free edge score:
wprp_proj + pfm_score only, dropping trainer_win_pct_365d and
jockey_win_pct_90d from calibrate_edge_score.py's 4-feature blend (user
request, Sep 2026: distrust of the trailing win-pct signals specifically,
independent of whether the walk-forward audit says they help).

CONTEXT
  calibrate_edge_score.py's own ablation (see its docstring) found
  trainer/jockey trailing form "does almost all the work" for the
  4-feature blend's ranking quality (AUC/strike) - but that finding
  doesn't settle whether a 2-feature version is unusable, only that it
  should rank worse. This script runs the actual walk-forward comparison
  (same methodology, same leak-safe weekly refit) rather than relying on
  the old ablation's numbers, then re-runs the price-capped overlay
  sweep on this new score so the user can compare like for like: does a
  wprp_proj+pfm_score-only "wpr price" still find a not-confirmed-losing
  segment once capped at $26 (the cap size settled on in chat), same bar
  as the 4-feature version.

  Same scoring convention as production (see calibrate_edge_score._score
  and wpr_projection.compute_edge_scores): per-feature z-score against a
  population mean/std, skip-and-average over present features, EXCEPT a
  missing wprp_proj forces score=0 (same deliberate rule, kept for
  comparability - not re-litigated here). pfm_score coverage is ~34% of
  runners (per calibrate_edge_score.py), so for the other ~66% this
  2-feature score reduces to wprp_proj alone.

  Price basis: fixed_win_price (see wpr_bet_selection_fixed_price.py's
  docstring for why - SP isn't known pre-race, so it can't be a live
  selection input).

USAGE
  python wpr_edge_two_feature_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import log_loss, roc_auc_score

from calibrate_edge_score import RUNNERS_CSV

BURN_IN_WEEKS = 5
MIN_TRAIN = 300
FEATURES_2F = ["wprp_proj", "pfm_score"]
FEATURES_4F = ["wprp_proj", "trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"]
EDGE_THRESHOLDS = [0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAP = 26.0


def _load_resulted(features):
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["resulted"] = pd.to_numeric(df.get("resulted"), errors="coerce")
    df = df[(df["resulted"] == 1) & (df.get("scratched") != 1)].copy()
    df["date"] = pd.to_datetime(df.get("date"), errors="coerce")
    df["won"] = pd.to_numeric(df.get("won"), errors="coerce").fillna(0)
    fx = pd.to_numeric(df.get("fixed_win_price"), errors="coerce")
    sp_fallback = pd.to_numeric(df.get("starting_price_sp"), errors="coerce")
    df["sp"] = fx.fillna(sp_fallback)
    for f in features:
        df[f] = pd.to_numeric(df.get(f), errors="coerce")
    df = df.dropna(subset=["date", "race_id", "sp"])
    df = df[df["sp"] > 1.0]
    return df.sort_values("date")


def _score(data, mean, std, features):
    z = (data[features] - mean) / std.replace(0, np.nan)
    score = z.mean(axis=1, skipna=True)
    return score.where(data["wprp_proj"].notna(), 0.0)


def walk_forward(d, features, burn_in_weeks=BURN_IN_WEEKS, min_train=MIN_TRAIN):
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    rows, auc_list, ll_list, bet_profits, bets = [], [], [], [], []
    for wk in test_weeks:
        train = d[d["date"].dt.to_period("W") < wk]
        test = d[d["date"].dt.to_period("W") == wk].copy()
        if len(train) < min_train or len(test) == 0:
            continue
        mean, std = train[features].mean(), train[features].std()
        test["score"] = _score(test, mean, std, features)
        test = test.dropna(subset=["score"])
        if len(test) == 0:
            continue
        idx = test.groupby("race_id")["score"].idxmax()
        top = test.loc[idx]
        profit = np.where(top["won"] == 1, top["sp"] - 1, -1.0)
        bet_profits.extend(profit.tolist())
        rows.append({"n": len(top), "wins": int(top["won"].sum()), "profit": profit.sum()})
        e = np.exp(test["score"] - test.groupby("race_id")["score"].transform("max"))
        p = e / test.groupby("race_id")["score"].transform(lambda s: np.exp(s - s.max()).sum())
        if test["won"].nunique() == 2:
            auc_list.append(roc_auc_score(test["won"], test["score"]))
            ll_list.append(log_loss(test["won"], p.clip(1e-6, 1 - 1e-6)))
        test["p_mkt_norm"] = (1.0 / test["sp"]) / test.groupby("race_id")["sp"].transform(
            lambda s: (1.0 / s).sum())
        test["edge"] = p - test["p_mkt_norm"]
        bets.append(test[["won", "sp", "edge"]])
    return rows, auc_list, ll_list, np.array(bet_profits), pd.concat(bets, ignore_index=True)


def report_overlay(bets, cap):
    capped = bets[bets["sp"] <= cap]
    for thr in EDGE_THRESHOLDS:
        sub = capped[capped["edge"] >= thr]
        if len(sub) < 20:
            print(f"    edge>={thr:.2f}, price<={cap:.0f}: n={len(sub)} (too small)")
            continue
        profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
        se = profit.std(ddof=1) / np.sqrt(len(profit))
        t = profit.mean() / se if se > 0 else float("nan")
        flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
        print(f"    edge>={thr:.2f}, price<={cap:.0f}: n={len(sub):5d}  "
              f"strike={sub['won'].mean()*100:5.2f}%  ROI={profit.sum()/len(sub)*100:+6.2f}%  "
              f"t={t:+.2f}{flag}")


def run_variant(label, features):
    d = _load_resulted(features)
    coverage = {f: f"{d[f].notna().mean()*100:.1f}%" for f in features}
    print(f"\n========== {label} ({', '.join(features)}) ==========")
    print(f"coverage: {coverage}")
    rows, auc_list, ll_list, bet_profits, bets = walk_forward(d, features)
    n = sum(x["n"] for x in rows)
    wins = sum(x["wins"] for x in rows)
    profit = sum(x["profit"] for x in rows)
    se = bet_profits.std(ddof=1) / np.sqrt(len(bet_profits))
    t = bet_profits.mean() / se
    print(f"walk-forward top-1: n={n:,}  strike={wins/n*100:.2f}%  ROI={profit/n*100:+.2f}%  "
          f"t={t:+.2f}  mean weekly AUC={np.mean(auc_list):.4f}  logloss={np.mean(ll_list):.4f}")
    print(f"overlay x price<=${PRICE_CAP:.0f}:")
    report_overlay(bets, PRICE_CAP)
    return bets


def run():
    run_variant("4-FEATURE baseline (production)", FEATURES_4F)
    run_variant("2-FEATURE (wprp_proj + pfm_score only)", FEATURES_2F)
    print("\nCompare the two blocks above directly: same walk-forward methodology, same price "
          "basis (fixed_win_price), same $26 cap - the only difference is which features feed "
          "the score. If 2-feature AUC/strike drops a lot but the price-capped overlay ROI at "
          "$26 doesn't get meaningfully worse, dropping trainer/jockey costs ranking quality "
          "without necessarily costing this specific betting use case (they're different "
          "questions - see calibrate_edge_score.py's own pfm_score writeup for the same kind "
          "of AUC-vs-ROI split).")


if __name__ == "__main__":
    run()
