"""
wpr_edge_pfm_weighted_test.py - tests re-weighting the edge score's
"other" bucket (trainer_win_pct_365d, jockey_win_pct_90d, pfm_score) to
favour pfm_score over trainer/jockey, keeping the horse's own weight
(wprp_proj) fixed at its current ~0.25 share (user request, Sep 2026,
following wpr_edge_horse_weighted_test.py's finding that reducing the
horse's weight hurts every metric - this is a narrower, different
change: redistribute WITHIN the other-3 bucket, not between horse and
the rest).

METHODOLOGY: same leak-safe weekly walk-forward, $26 price cap,
fixed_win_price basis as every other script in this family. Score for
each row = weighted average of whichever of {wprp_proj, trainer, jockey,
pfm} are present, weights renormalised over present features only (same
skip-and-average spirit as production's _score, just weighted instead
of equal) - missing wprp_proj still forces score=0 (same rule as
production).

Weight configs tested (w_horse held at 0.25 throughout; the "other 0.75"
split between trainer/jockey/pfm progressively shifts toward pfm):
  baseline  0.25 / 0.25 / 0.25 / 0.25  (current production equal average)
  pfm_up1   0.25 / 0.15 / 0.15 / 0.45
  pfm_up2   0.25 / 0.10 / 0.10 / 0.55
  pfm_up3   0.25 / 0.05 / 0.05 / 0.65

pfm_score coverage is only ~34% of runners - for the other ~66% these
configs are IDENTICAL to just re-splitting between horse/trainer/jockey
(pfm's weight gets renormalised away, same skip logic as everywhere
else in this project), so any effect below is concentrated in the
minority of runners pfm_score actually covers.

USAGE
  python wpr_edge_pfm_weighted_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import log_loss, roc_auc_score

from calibrate_edge_score import RUNNERS_CSV

BURN_IN_WEEKS = 5
MIN_TRAIN = 300
ALL_FEATURES = ["wprp_proj", "trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"]
EDGE_THRESHOLDS = [0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAP = 26.0

WEIGHT_CONFIGS = {
    "baseline (current equal average)": {"wprp_proj": 0.25, "trainer_win_pct_365d": 0.25,
                                          "jockey_win_pct_90d": 0.25, "pfm_score": 0.25},
    "pfm_up1": {"wprp_proj": 0.25, "trainer_win_pct_365d": 0.15,
                "jockey_win_pct_90d": 0.15, "pfm_score": 0.45},
    "pfm_up2": {"wprp_proj": 0.25, "trainer_win_pct_365d": 0.10,
                "jockey_win_pct_90d": 0.10, "pfm_score": 0.55},
    "pfm_up3": {"wprp_proj": 0.25, "trainer_win_pct_365d": 0.05,
                "jockey_win_pct_90d": 0.05, "pfm_score": 0.65},
}


def _load_resulted():
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["resulted"] = pd.to_numeric(df.get("resulted"), errors="coerce")
    df = df[(df["resulted"] == 1) & (df.get("scratched") != 1)].copy()
    df["date"] = pd.to_datetime(df.get("date"), errors="coerce")
    df["won"] = pd.to_numeric(df.get("won"), errors="coerce").fillna(0)
    fx = pd.to_numeric(df.get("fixed_win_price"), errors="coerce")
    sp_fallback = pd.to_numeric(df.get("starting_price_sp"), errors="coerce")
    df["sp"] = fx.fillna(sp_fallback)
    for f in ALL_FEATURES:
        df[f] = pd.to_numeric(df.get(f), errors="coerce")
    df = df.dropna(subset=["date", "race_id", "sp"])
    df = df[df["sp"] > 1.0]
    return df.sort_values("date")


def _weighted_score(data, mean, std, weights):
    z = pd.DataFrame({f: (data[f] - mean[f]) / std[f] for f in ALL_FEATURES})
    present = z.notna()
    w = pd.Series(weights)
    weighted_sum = (z.fillna(0) * w).sum(axis=1)
    weight_total = (present * w).sum(axis=1)
    score = weighted_sum / weight_total.replace(0, np.nan)
    return score.where(data["wprp_proj"].notna(), 0.0)


def walk_forward(d, weights, burn_in_weeks=BURN_IN_WEEKS, min_train=MIN_TRAIN):
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    rows, auc_list, ll_list, bet_profits, bets = [], [], [], [], []
    for wk in test_weeks:
        train = d[d["date"].dt.to_period("W") < wk]
        test = d[d["date"].dt.to_period("W") == wk].copy()
        if len(train) < min_train or len(test) == 0:
            continue
        mean, std = train[ALL_FEATURES].mean(), train[ALL_FEATURES].std()
        test["score"] = _weighted_score(test, mean, std, weights)
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


def run():
    d = _load_resulted()
    print(f"resulted races: {d['race_id'].nunique():,}  runners: {len(d):,}  "
          f"({d['date'].min().date()} to {d['date'].max().date()})")
    print(f"pfm_score coverage: {d['pfm_score'].notna().mean()*100:.1f}%\n")

    for label, weights in WEIGHT_CONFIGS.items():
        print(f"========== {label}: {weights} ==========")
        rows, auc_list, ll_list, bet_profits, bets = walk_forward(d, weights)
        n = sum(x["n"] for x in rows)
        wins = sum(x["wins"] for x in rows)
        profit = sum(x["profit"] for x in rows)
        se = bet_profits.std(ddof=1) / np.sqrt(len(bet_profits))
        t = bet_profits.mean() / se
        print(f"  walk-forward top-1: n={n:,}  strike={wins/n*100:.2f}%  ROI={profit/n*100:+.2f}%  "
              f"t={t:+.2f}  mean weekly AUC={np.mean(auc_list):.4f}  logloss={np.mean(ll_list):.4f}")
        print(f"  overlay x price<=${PRICE_CAP:.0f}:")
        report_overlay(bets, PRICE_CAP)
        print()

    print("4 configs x 5 thresholds = 20 comparisons on top of everything else tested this "
          "session - treat any standout as a hypothesis for a future walk-forward period to "
          "confirm, not a result to ship immediately.")


if __name__ == "__main__":
    run()
