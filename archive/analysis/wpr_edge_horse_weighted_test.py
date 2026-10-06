"""
wpr_edge_horse_weighted_test.py - tests a HORSE-DOMINANT weighted edge
score against the current unweighted 4-feature average (user request,
Sep 2026): in calibrate_edge_score.py's plain average, wprp_proj (the
horse's own rating) gets only ~25-33% of the blend's weight per runner
(one of 3-4 equally-weighted features present), while
trainer_win_pct_365d + jockey_win_pct_90d together make up 50-67%
combined - a real, quantifiable imbalance, not just a feeling. This is
a DIFFERENT critique from wpr_edge_two_feature_test.py's "drop
trainer/jockey entirely" (confirmed catastrophic there) - here
trainer/jockey/pfm stay in the score, just heavily down-weighted so the
horse's own signal dominates.

Note this is also different from the "fitted weighted" version
calibrate_edge_score.py's own docstring mentions losing to the plain
average (a logistic regression letting the OPTIMISER pick weights,
which could easily still land on trainer/jockey-heavy since that's
what best fit the historical data) - this sweeps a small set of
DELIBERATE, horse-dominant weights instead, testing the specific
hypothesis "the horse should dominate" rather than whatever an
optimiser finds.

METHODOLOGY: same leak-safe weekly walk-forward as every other script
in this family, same $26 price cap, same fixed_win_price basis. Score:
  score = w_horse * z(wprp_proj) + (1 - w_horse) * mean(z(other features
  present))
Missing features are skipped and the remaining weight renormalised
across whichever of trainer/jockey/pfm are present (not silently
dropped) - same "skip and average" spirit as the production _score,
just weighted. Missing wprp_proj still forces score=0 (same rule as
production, kept for comparability).

USAGE
  python wpr_edge_horse_weighted_test.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import log_loss, roc_auc_score

from calibrate_edge_score import RUNNERS_CSV

BURN_IN_WEEKS = 5
MIN_TRAIN = 300
OTHER_FEATURES = ["trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"]
ALL_FEATURES = ["wprp_proj"] + OTHER_FEATURES
HORSE_WEIGHTS = [0.25, 0.40, 0.50, 0.60, 0.70, 0.80]  # 0.25 ~= current unweighted average
EDGE_THRESHOLDS = [0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAP = 26.0


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


def _weighted_score(data, mean, std, w_horse):
    z_horse = (data["wprp_proj"] - mean["wprp_proj"]) / std["wprp_proj"]
    z_others = pd.DataFrame({
        f: (data[f] - mean[f]) / std[f] for f in OTHER_FEATURES
    })
    other_mean = z_others.mean(axis=1, skipna=True)  # skip-and-average over present others
    both_present = z_horse.notna() & other_mean.notna()
    horse_only = z_horse.notna() & other_mean.isna()
    score = pd.Series(np.nan, index=data.index)
    score[both_present] = w_horse * z_horse[both_present] + (1 - w_horse) * other_mean[both_present]
    score[horse_only] = z_horse[horse_only]  # no other signal available - horse alone
    return score.where(data["wprp_proj"].notna(), 0.0)


def walk_forward(d, w_horse, burn_in_weeks=BURN_IN_WEEKS, min_train=MIN_TRAIN):
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    rows, auc_list, ll_list, bet_profits, bets = [], [], [], [], []
    for wk in test_weeks:
        train = d[d["date"].dt.to_period("W") < wk]
        test = d[d["date"].dt.to_period("W") == wk].copy()
        if len(train) < min_train or len(test) == 0:
            continue
        mean, std = train[ALL_FEATURES].mean(), train[ALL_FEATURES].std()
        test["score"] = _weighted_score(test, mean, std, w_horse)
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
          f"({d['date'].min().date()} to {d['date'].max().date()})\n")
    for w in HORSE_WEIGHTS:
        label = f"w_horse={w:.2f}" + ("  (~= current unweighted average)" if w == 0.25 else "")
        print(f"========== {label} ==========")
        rows, auc_list, ll_list, bet_profits, bets = walk_forward(d, w)
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

    print("Reminder: 6 weights x 5 thresholds = 30 comparisons here on top of everything else "
          "tested this session - treat any standout as a hypothesis for a future walk-forward "
          "period to confirm, not a result to ship immediately.")


if __name__ == "__main__":
    run()
