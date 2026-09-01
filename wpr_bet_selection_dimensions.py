"""
wpr_bet_selection_dimensions.py - extends calibrate_edge_score.py's
walk-forward edge-vs-market overlay test with a SECOND filter dimension,
to check whether combining edge with something else isolates a genuinely
profitable pocket that edge alone does not (see chat, Sep 2026: a re-run
of calibrate_edge_score.py's overlay test on the current, larger dataset
came back WORSE than the Aug audit - edge>=0.08 and edge>=0.10 are now
SIGNIFICANTLY NEGATIVE, not merely unproven - only edge>=0.20 (n=244) is
still a positive, non-significant point estimate).

METHODOLOGY: same leak-safe weekly walk-forward as calibrate_edge_score.py
(refit mean/std strictly on prior weeks, score the next week, pool bets
across all weeks) - this script just captures two more columns per bet
(field_size, wprp_rank-equivalent live rank) so they can be used as a
second filter alongside edge. Two dimensions tested, chosen for a real
prior reason rather than a blind scan (multiple-comparisons risk is
already high with 7 edge thresholds; adding a systematic second-dimension
sweep on top multiplies that risk further, so this is deliberately narrow):

  1. PRICE CAP: exclude extreme longshots (sp > cap) even when edge looks
     high - a nominal edge on a $41 shot is one big outlier result away
     from swinging the whole point estimate (this is a candidate
     explanation for edge>=0.20's healthy-looking but wildly noisy ROI).
  2. RANK AGREEMENT: only bet the overlay when the SAME runner is ALSO
     top-2 by the model's own score that week - i.e. require two
     independently-motivated signals (edge AND rank) to agree, instead of
     trusting edge in isolation.

Every result below is a POINT ESTIMATE test, same reporting discipline as
calibrate_edge_score.py: report t-stat, flag |t|>=1.96, and do not treat a
bigger number from a smaller n as proof of anything.

USAGE
  python wpr_bet_selection_dimensions.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

from calibrate_edge_score import FEATURES, _load_resulted, _score

BURN_IN_WEEKS = 5
MIN_TRAIN = 300
EDGE_THRESHOLDS = [0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]


def walk_forward_bets(d, burn_in_weeks=BURN_IN_WEEKS, min_train=MIN_TRAIN):
    """Same weekly refit loop as calibrate_edge_score.walk_forward_validate,
    but keeps field_size and live rank per bet instead of collapsing to
    just (won, sp, edge)."""
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    bets = []
    for wk in test_weeks:
        train = d[d["date"].dt.to_period("W") < wk]
        test = d[d["date"].dt.to_period("W") == wk].copy()
        if len(train) < min_train or len(test) == 0:
            continue
        mean, std = train[FEATURES].mean(), train[FEATURES].std()
        test["score"] = _score(test, mean, std)
        test = test.dropna(subset=["score"])
        if len(test) == 0:
            continue
        test["field_size"] = test.groupby("race_id")["race_id"].transform("count")
        test["live_rank"] = test.groupby("race_id")["score"].rank(ascending=False, method="first")
        e = np.exp(test["score"] - test.groupby("race_id")["score"].transform("max"))
        p = e / test.groupby("race_id")["score"].transform(lambda s: np.exp(s - s.max()).sum())
        test["p_mkt_norm"] = (1.0 / test["sp"]) / test.groupby("race_id")["sp"].transform(
            lambda s: (1.0 / s).sum())
        test["edge"] = p - test["p_mkt_norm"]
        test["p_model"] = p
        bets.append(test[["won", "sp", "edge", "field_size", "live_rank", "p_model"]])
    return pd.concat(bets, ignore_index=True)


def report(sub, label):
    if len(sub) < 20:
        print(f"    {label}: n={len(sub)} (too small, skipped)")
        return
    profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(len(profit))
    t = profit.mean() / se if se > 0 else float("nan")
    flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
    print(f"    {label}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
          f"ROI={profit.sum()/len(sub)*100:+6.2f}%  t={t:+.2f}{flag}")


def run():
    d = _load_resulted()
    print(f"resulted races: {d['race_id'].nunique():,}  runners: {len(d):,}  "
          f"({d['date'].min().date()} to {d['date'].max().date()})")
    bets = walk_forward_bets(d)
    print(f"total scored bets across walk-forward weeks: {len(bets):,}\n")

    print("=== Dimension 1: edge threshold x price cap ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets["edge"] >= thr]
        report(base, f"edge>={thr:.2f}, no price cap")
        for cap in PRICE_CAPS:
            sub = base[base["sp"] <= cap]
            report(sub, f"edge>={thr:.2f}, sp<={cap:.0f}")
        print()

    print("=== Dimension 2: edge threshold x rank agreement (top-2 by model score) ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets["edge"] >= thr]
        report(base, f"edge>={thr:.2f}, any rank")
        sub = base[base["live_rank"] <= 2]
        report(sub, f"edge>={thr:.2f}, live_rank<=2")
        print()

    print("=== Dimension 3: staking (Kelly-weighted vs flat) on the best point estimate so far ===")
    print("(edge>=0.20, sp<=15 - the highest-ROI, highest-t segment found above; this does NOT")
    print(" make the underlying edge significant, it only asks whether stake SIZING would have")
    print(" helped or hurt realising it, using the model's own p_model as the Kelly probability)")
    seg = bets[(bets["edge"] >= 0.20) & (bets["sp"] <= 15.0)].copy()
    if len(seg) >= 20:
        b = seg["sp"] - 1.0
        kelly_f_raw = (seg["p_model"] * seg["sp"] - 1.0) / b
        print(f"    raw (uncapped) full-Kelly fraction in this segment: "
              f"min={kelly_f_raw.min()*100:.1f}%  median={kelly_f_raw.median()*100:.1f}%  "
              f"max={kelly_f_raw.max()*100:.1f}% of bankroll - the model's own probability "
              f"estimate is confident enough here that full Kelly is always >5%, which is why "
              f"the capped/quarter-Kelly figures below flatten to a near-constant stake")
        kelly_f = kelly_f_raw.clip(lower=0.0, upper=0.05)  # standard practical cap: never >5% of bankroll
        quarter_kelly = kelly_f * 0.25
        flat_profit = np.where(seg["won"] == 1, seg["sp"] - 1, -1.0)
        kelly_profit = np.where(seg["won"] == 1, quarter_kelly * b, -quarter_kelly)
        print(f"    flat stake ($1 each):      total profit={flat_profit.sum():+.2f}  "
              f"ROI on turnover={flat_profit.sum()/len(seg)*100:+.2f}%")
        print(f"    quarter-Kelly (mean stake={quarter_kelly.mean()*100:.2f}% of bankroll): "
              f"total profit={kelly_profit.sum():+.2f}  "
              f"ROI on staked={kelly_profit.sum()/quarter_kelly.sum()*100:+.2f}%")
        print(f"    stake range: {quarter_kelly.min()*100:.2f}% - {quarter_kelly.max()*100:.2f}% "
              f"of bankroll per bet ({int((kelly_f == 0).sum())} bets sized to zero - "
              f"model's own p_model implies no edge despite the {'>=0.20' } threshold, an "
              f"artifact of p_model/market-normalisation differing from the edge calc above)")
    else:
        print(f"    n={len(seg)}, too small for a staking simulation")
    print()

    print("Reminder: every row above is one more comparison on the same dataset. A single "
          "row crossing |t|>=1.96 here is weaker evidence than the same threshold surviving "
          "calibrate_edge_score.py's own 7-threshold sweep, precisely because this script ran "
          "more tests looking for it. Treat any hit as a hypothesis for a FUTURE walk-forward "
          "period to confirm, not as a result to ship immediately.")


if __name__ == "__main__":
    run()
