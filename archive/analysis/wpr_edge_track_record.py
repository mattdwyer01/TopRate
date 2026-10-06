"""
wpr_edge_track_record.py - day-by-day forward track record for the blend/
edge score (wpr_projection.compute_edge_scores), benchmarked against the
market favourite, wpr_rank, and wprp_rank (the old production model) on
the SAME races each day.

WHY THIS EXISTS
  A single bad day (Caulfield, 29 Aug 2026: blend top-1 went 0/10) raised
  the question of whether the model is broken. This script is how to
  answer that without guessing: pull every recent resulted race, compute
  the same top-1/top-4/overlay comparison across ALL of them, and check
  whether a short losing streak is ordinary variance or a real trend.

  First run (5 weeks, 36 race days, 1,749 races, Aug 2026): blend top-1
  hit 27.6% (binomial test vs the 26.64% walk-forward-validated rate:
  p=0.358, i.e. no meaningful deviation), top-4 hit rate 69.5% vs a
  field-size-adjusted random baseline of 45.6% (a real, large beat of
  chance). ROI was still negative for both top-1 (-12.3%) and the 13%+
  overlay (-21.8%) - consistent with every finding in this project's
  history: the RANKING is real, converting it into PROFIT against the
  market's overround is not proven. The Caulfield day was a real outlier
  (0/10) sitting inside an otherwise on-trend 5 weeks, not the start of
  a trend - the market favourite itself only won 2/10 that specific day
  (vs its ~34% norm), pointing at a broadly upset-heavy card, not a
  blend-specific failure.

CAVEAT: this is NOT a walk-forward out-of-sample test - it applies the
CURRENT deployed model (fit on the whole dataset, see
calibrate_edge_score.py) to historical races, some of which that fit
used. It answers "is the currently-deployed model still behaving the way
the audit found", not "would this have worked without hindsight". Re-run
this periodically (weekly/monthly) as new races result to build a
genuinely forward (not fit-inclusive) track record over time - the
window naturally rolls forward and eventually clears the training data.

USAGE
  python wpr_edge_track_record.py                  # last 5 weeks (default)
  python wpr_edge_track_record.py --days 14         # last 2 weeks
  python wpr_edge_track_record.py --edge-threshold 0.15

NO EM DASHES policy: hyphens only in this file.
"""
import argparse

import numpy as np
import pandas as pd
from scipy.stats import binomtest

RUNNERS_CSV = "toprate_runners.csv"
VALIDATED_TOP1_STRIKE = 0.2664  # from calibrate_edge_score.py's walk-forward audit


def _load(days):
    df = pd.read_csv(RUNNERS_CSV, low_memory=False)
    df["resulted"] = pd.to_numeric(df["resulted"], errors="coerce")
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df["sp"] = pd.to_numeric(df["starting_price_sp"], errors="coerce")
    df["sp"] = df["sp"].fillna(pd.to_numeric(df["price_top"], errors="coerce"))
    df["won"] = pd.to_numeric(df["won"], errors="coerce")
    max_date = df.loc[df["resulted"] == 1, "date"].max()
    sub = df[(df["resulted"] == 1) & (df["scratched"] != 1)
             & (df["date"] >= max_date - pd.Timedelta(days=days))].copy()
    return sub.dropna(subset=["sp"])


def track_record(days=35, edge_threshold=0.13, venue=None):
    sub = _load(days)
    if venue:
        sub = sub[sub["venue"].str.contains(venue, case=False, na=False)]
    rows = []
    for d, day in sub.groupby(sub["date"].dt.date):
        top1_wins = top4_hits = mkt_wins = wpr_wins = wprp_wins = 0
        overlay_bets = overlay_wins = 0
        exp_top4_random = 0.0
        for _, g in day.groupby("race_id"):
            gb = g.dropna(subset=["wprp_blend_rank"])
            if len(gb):
                top1_wins += int(gb[gb["wprp_blend_rank"] == 1]["won"].sum())
                t4 = gb[gb["wprp_blend_rank"] <= 4]
                top4_hits += int((t4["won"] == 1).any())
                exp_top4_random += min(4, len(gb)) / len(gb)
            fav = g.loc[g["sp"].idxmin()]
            mkt_wins += int(fav["won"] == 1)
            gw = g.dropna(subset=["wpr_rank"])
            if len(gw):
                wpr_wins += int(gw.loc[gw["wpr_rank"].idxmin(), "won"] == 1)
            gwp = g.dropna(subset=["wprp_rank"])
            if len(gwp):
                wprp_wins += int(gwp.loc[gwp["wprp_rank"].idxmin(), "won"] == 1)
            ob = g[g["wprp_edge"] >= edge_threshold] if "wprp_edge" in g else g.iloc[0:0]
            overlay_bets += len(ob)
            overlay_wins += int(ob["won"].sum())
        rows.append({"date": d, "races": day["race_id"].nunique(), "top1_wins": top1_wins,
                     "top4_hits": top4_hits, "exp_top4_random": exp_top4_random,
                     "mkt_wins": mkt_wins, "wpr_wins": wpr_wins, "wprp_wins": wprp_wins,
                     "overlay_bets": overlay_bets, "overlay_wins": overlay_wins})
    return pd.DataFrame(rows).sort_values("date"), sub


def report(days=35, edge_threshold=0.13, venue=None):
    out, sub = track_record(days, edge_threshold, venue)
    if len(out) == 0:
        print("No resulted races in this window.")
        return
    pd.set_option("display.width", 160)
    print(out.to_string(index=False))

    tot = out["races"].sum()
    print(f"\n=== TOTALS: {len(out)} race days, {tot} races ===")
    for label, col in [("Blend top-1", "top1_wins"), ("Market favourite", "mkt_wins"),
                        ("wpr_rank", "wpr_wins"), ("wprp_rank (old model)", "wprp_wins")]:
        k = out[col].sum()
        print(f"{label:22s} {k:4d}/{tot} = {k/tot*100:.1f}%")
    print(f"{'Blend top-4 hit':22s} {out['top4_hits'].sum():4d}/{tot} = "
          f"{out['top4_hits'].sum()/tot*100:.1f}%  (field-size-adjusted random baseline: "
          f"{out['exp_top4_random'].sum()/tot*100:.1f}%)")

    top1 = sub.dropna(subset=["wprp_blend_rank"])
    top1 = top1[top1["wprp_blend_rank"] == 1]
    profit1 = np.where(top1["won"] == 1, top1["sp"] - 1, -1.0)
    print(f"{'Blend top-1 ROI':22s} {profit1.sum()/len(top1)*100:+.2f}% (n={len(top1)})")

    ob = sub[sub["wprp_edge"] >= edge_threshold]
    if len(ob):
        profit_ob = np.where(ob["won"] == 1, ob["sp"] - 1, -1.0)
        print(f"{'Overlay ROI ({:.0%}+)'.format(edge_threshold):22s} "
              f"{profit_ob.sum()/len(ob)*100:+.2f}% (n={len(ob)}, {int(ob['won'].sum())} wins)")

    k = out["top1_wins"].sum()
    res = binomtest(k, tot, VALIDATED_TOP1_STRIKE)
    print(f"\nBinomial test vs validated {VALIDATED_TOP1_STRIKE*100:.1f}% top-1 strike: "
          f"p-value={res.pvalue:.3f} "
          f"({'consistent with validated rate' if res.pvalue > 0.05 else 'significant deviation - investigate'})")
    print("\nRemember: strike-rate/top-4 tracking here is not the same question as ROI - the "
          "ranking can be genuinely working while still losing money against the market's own "
          "overround. Don't read a good strike-rate run as proof of profit, or a bad run (like "
          "one venue on one day) as proof the model is broken - check both, and check the "
          "binomial test before reacting to either.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--days", type=int, default=35, help="lookback window in days (default 35)")
    ap.add_argument("--edge-threshold", type=float, default=0.13,
                    help="overlay threshold to report (default 0.13, matches the live Overlays tab floor)")
    ap.add_argument("--venue", type=str, default=None, help="filter to one venue (substring match)")
    args = ap.parse_args()
    report(args.days, args.edge_threshold, args.venue)
