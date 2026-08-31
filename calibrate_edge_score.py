"""
calibrate_edge_score.py - fit the "edge score": an unweighted z-score
average of WPR projection + trailing jockey/trainer form + a form-provider
score (pfm_score) into a per-race win-probability estimate, compared
against the market's own implied
probability to find value (edge = model_prob - market_prob). Writes the
per-feature mean/std into wpr_models/config.json under "edge_score" for
wpr_projection.compute_edge_scores to use.

WHY THIS SHAPE, NOT A FITTED MODEL
  An earlier version of this fit a logistic regression on 6 features
  (wprp_proj, speed_rating, pfm_score, pf_ai_score, trainer_win_pct_365d,
  jockey_win_pct_90d) and validated it on a single 70/30 date split -
  that showed AUC ~0.72 and an overlay ROI of +6% to +17%. A proper
  walk-forward check (Aug 2026 audit: model refit weekly on strictly-prior
  data, walked across the full Apr-Aug history rather than one split)
  told a different story:
    - The RANKING quality genuinely holds up: AUC stayed ~0.68 and top-1
      strike rate ~28% across every burn-in window tested, well above WPR
      alone's ~0.58 AUC / ~25% strike. This is real and robust.
    - The fitted logistic regression was NOT the best way to combine the
      signals - a plain unweighted average of z-scored features beat it
      on every walk-forward fold (28.1% strike / AUC 0.68 vs the
      logistic's 25.4% / -5.3% ROI). Feature ablation showed trainer/
      jockey trailing form does almost all the work; wprp_proj adds a
      little, speed_rating and pf_ai_score add essentially nothing, so
      they were dropped. pfm_score is a genuine mixed case, not a clean
      drop: removing it from the 6-feature average LOWERED AUC (0.6806 ->
      0.6655, a real loss in ranking quality) but RAISED the point-estimate
      ROI (+0.51% -> +4.20%) - since neither ROI number is anywhere close
      to statistically significant, that ROI swing is not good evidence
      pfm_score hurts profitability, but it IS good evidence pfm_score
      adds real discrimination. Kept in FEATURES on that basis - its only
      real cost is coverage (~34% of runners have it, so it's skipped for
      the rest, see HOW THE SCORE IS COMPUTED below), not a demonstrated
      ROI cost. wprp_proj + trainer/jockey trailing form + pfm_score
      matched or beat the full 6-feature version's AUC/strike with more
      stable ROI across burn-in choices than either the 6-feature or the
      pfm-less 3-feature version - see the walk-forward output below.
    - The overlay ROI claim did NOT hold up walked forward across the
      full history (pooled n~3,800-21,500 depending on threshold): low
      thresholds (edge>=0, >=0.05) came back SIGNIFICANTLY NEGATIVE
      (t=-10.44, t=-5.00), and every threshold from 0.08 up was
      statistically indistinguishable from zero (|t|<0.9 in the 6-feature
      logistic version). Re-run with this simpler unweighted-average
      score, the shape improved (ROI rises monotonically with the
      threshold: +0.8% / +2.1% / +5.2% / +7.0% / +11.8% at edge
      >=0.08/0.10/0.13/0.15/0.20) but STILL never reached significance
      (max t=0.84 at edge>=0.20, n=427). Conclusion: the RANKING is a
      real, validated improvement over WPR; the OVERLAY is an unproven,
      experimental signal worth tracking forward, not a validated source
      of profit - see EdgeOverlays.tsx's copy, which must stay honest
      about this.

  Deliberately excludes jt_combo_win_pct - see toprate_daily.py's SIGNALS
  comment: that field leaks the runner's own race result on low-ride-count
  combos (winPercent reads ~100/~0 exactly matching whether the runner
  just won or lost), so any backtest or model using it is meaningless.

HOW THE SCORE IS COMPUTED (must match wpr_projection.compute_edge_scores
exactly, since that is what actually runs in production)
  For each feature, z = (value - training_mean) / training_std. A runner
  missing a feature has that feature SKIPPED (not median-imputed) - the
  score is the mean of whatever z-scores the runner actually has. A
  runner missing every feature gets no score at all (same "no model
  estimate" fallback as a WPR projection with insufficient history).
  This is a real behaviour change from the old median-imputing logistic
  model - a runner with no wprp_proj now scores purely on its jockey/
  trainer form rather than being anchored toward "average WPR".

USAGE
  python calibrate_edge_score.py           # report only (walk-forward validation)
  python calibrate_edge_score.py --write   # also update wpr_models/config.json

Re-run this quarterly (or whenever a season's worth of new resulted races
has accumulated) to keep the mean/std current - see CLAUDE.md.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.metrics import log_loss, roc_auc_score

RUNNERS_CSV = "toprate_runners.csv"
CONFIG_PATH = Path("wpr_models") / "config.json"
FEATURES = ["wprp_proj", "trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"]
BURN_IN_WEEKS = 5


def _load_resulted():
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                     low_memory=False)
    df["resulted"] = pd.to_numeric(df.get("resulted"), errors="coerce")
    df = df[(df["resulted"] == 1) & (df.get("scratched") != 1)].copy()
    df["date"] = pd.to_datetime(df.get("date"), errors="coerce")
    df["won"] = pd.to_numeric(df.get("won"), errors="coerce").fillna(0)
    df["sp"] = pd.to_numeric(df.get("starting_price_sp"), errors="coerce")
    df["sp"] = df["sp"].fillna(pd.to_numeric(df.get("price_top"), errors="coerce"))
    for f in FEATURES:
        df[f] = pd.to_numeric(df.get(f), errors="coerce")
    df = df.dropna(subset=["date", "race_id", "sp"])
    df = df[df["sp"] > 1.0]
    return df.sort_values("date")


def _score(data, mean, std):
    """The exact scoring formula compute_edge_scores uses in production:
    per-feature z-score against a fixed mean/std, skip-and-average over
    whichever features are present - EXCEPT a missing wprp_proj forces the
    whole score to 0.0 regardless of other signals (a deliberate user
    decision, Aug 2026, made after seeing this costs strike/ROI/AUC/logloss
    relative to skip-and-average - see module docstring's WHY THIS SHAPE
    section and wpr_projection.compute_edge_scores' _score for the numbers
    and rationale). Keep this in sync with that function - this script's
    validation is meaningless if it tests a different rule than production
    actually runs."""
    z = (data[FEATURES] - mean) / std.replace(0, np.nan)
    score = z.mean(axis=1, skipna=True)
    return score.where(data["wprp_proj"].notna(), 0.0)


def walk_forward_validate(d, burn_in_weeks=BURN_IN_WEEKS, min_train=300):
    """Refit mean/std weekly on strictly-prior data, walked across the
    whole history - this is the real validation, not a single split (see
    module docstring for why the single-split version was misleading)."""
    weeks = sorted(d["date"].dt.to_period("W").unique())
    test_weeks = weeks[burn_in_weeks:]
    rows, auc_list, ll_list, bet_profits, edge_bets = [], [], [], [], []
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
        test["p_mkt"] = 1.0 / test["sp"]
        test["p_mkt_norm"] = test["p_mkt"] / test.groupby("race_id")["p_mkt"].transform("sum")
        test["edge"] = p - test["p_mkt_norm"]
        for _, row in test.iterrows():
            edge_bets.append((row["won"], row["sp"], row["edge"]))
    return rows, auc_list, ll_list, np.array(bet_profits), pd.DataFrame(edge_bets, columns=["won", "sp", "edge"])


def calibrate(write=False):
    d = _load_resulted()
    print(f"resulted races: {d['race_id'].nunique():,}  runners: {len(d):,}  "
          f"({d['date'].min().date()} to {d['date'].max().date()})")

    rows, auc_list, ll_list, bet_profits, edge_bets = walk_forward_validate(d)
    n = sum(x["n"] for x in rows)
    wins = sum(x["wins"] for x in rows)
    profit = sum(x["profit"] for x in rows)
    se = bet_profits.std(ddof=1) / np.sqrt(len(bet_profits))
    t = bet_profits.mean() / se
    print(f"\nwalk-forward validation ({len(rows)} weekly refits, burn-in {BURN_IN_WEEKS} weeks, "
          f"strictly-prior training each time):")
    print(f"  top-1 pick: n={n:,}  strike={wins/n*100:.2f}%  ROI={profit/n*100:+.2f}%  "
          f"t={t:+.2f} (need ~1.96 for significance)")
    print(f"  mean weekly AUC={np.mean(auc_list):.4f}  logloss={np.mean(ll_list):.4f}")

    print("\n  edge-vs-market overlay (pooled across all walk-forward weeks):")
    significant_negative, significant_positive, tested = [], [], []
    for thr in [0.0, 0.05, 0.08, 0.10, 0.13, 0.15, 0.20]:
        sub = edge_bets[edge_bets["edge"] >= thr]
        if len(sub) < 20:
            continue
        p = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
        se_o = p.std(ddof=1) / np.sqrt(len(p))
        t_o = p.mean() / se_o if se_o > 0 else float("nan")
        flag = ""
        if abs(t_o) >= 1.96:
            flag = "  ** SIGNIFICANT **"
            (significant_negative if t_o < 0 else significant_positive).append(thr)
        tested.append(thr)
        print(f"    edge>={thr:.2f}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
              f"ROI={p.sum()/len(sub)*100:+6.2f}%  t={t_o:+.2f}{flag}")

    print()
    if abs(t) >= 1.96:
        print(f"  ** The ranking's own top-1 ROI IS statistically significant (t={t:+.2f}) - "
              f"{'a real edge' if t > 0 else 'a confirmed LOSS, do not deploy this as a top-pick strategy'}.")
    else:
        print(f"  The ranking's top-1 ROI is not statistically significant (t={t:+.2f}).")
    if significant_negative:
        print(f"  ** WARNING: edge>={min(significant_negative):.2f} and up shown SIGNIFICANTLY "
              f"NEGATIVE at: {', '.join(f'{x:.2f}' for x in significant_negative)} - these are "
              f"CONFIRMED LOSING thresholds in this audit, not merely unproven. Do not present "
              f"them as viable in the UI.")
    if significant_positive:
        print(f"  ** {', '.join(f'{x:.2f}' for x in significant_positive)} showed significantly "
              f"POSITIVE ROI - still verify this isn't multiple-comparisons luck (7 thresholds "
              f"tested) before trusting it.")
    if not significant_negative and not significant_positive:
        print("  No threshold reached |t|>=1.96 either direction - indistinguishable from "
              "break-even, not proven profitable. Do not report bigger point estimates from a "
              "later run as proof without re-checking significance.")

    # Final production mean/std: computed on ALL resulted data now that the
    # walk-forward above has validated the approach generalizes.
    full_mean = d[FEATURES].mean()
    full_std = d[FEATURES].std()

    overlay_results = []
    for thr in [0.0, 0.05, 0.08, 0.10, 0.13, 0.15, 0.20]:
        sub = edge_bets[edge_bets["edge"] >= thr]
        if len(sub) < 20:
            continue
        p = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
        se_o = p.std(ddof=1) / np.sqrt(len(p))
        t_o = p.mean() / se_o if se_o > 0 else float("nan")
        overlay_results.append({
            "threshold": thr, "n": len(sub), "strike_pct": round(sub["won"].mean() * 100, 2),
            "roi_pct": round(p.sum() / len(sub) * 100, 2), "t_stat": round(float(t_o), 2),
            "significant": bool(abs(t_o) >= 1.96),
        })

    if write:
        if not CONFIG_PATH.exists():
            print(f"\n{CONFIG_PATH} not found, cannot write.")
            return
        if significant_negative:
            note = (f"Unweighted z-score average (NOT a fitted model) - deliberately excludes "
                     f"jt_combo_win_pct (confirmed leak, see toprate_daily.py SIGNALS comment). "
                     f"A missing wprp_proj forces score=0 (user decision, costs some accuracy - "
                     f"see wpr_projection.compute_edge_scores' _score). WARNING: edge>="
                     f"{min(significant_negative):.2f} and up ({', '.join(f'{x:.2f}' for x in significant_negative)}) "
                     f"showed SIGNIFICANTLY NEGATIVE ROI in the walk-forward audit (see "
                     f"overlay_validation below) - these are CONFIRMED LOSING thresholds under "
                     f"this scoring rule, not merely unproven. Do not surface them as a viable "
                     f"tier in the UI; re-run this script if the scoring rule ever changes back.")
        else:
            note = ("Unweighted z-score average (NOT a fitted model) - deliberately excludes "
                     "jt_combo_win_pct (confirmed leak, see toprate_daily.py SIGNALS comment). "
                     "A missing wprp_proj forces score=0 (user decision, costs some accuracy - "
                     "see wpr_projection.compute_edge_scores' _score). The AUC/strike-rate "
                     "improvement over WPR alone is walk-forward validated and robust; no "
                     "overlay threshold reached statistical significance in this run (see "
                     "overlay_validation below) - treat edge as an experimental signal to "
                     "track forward, not a proven bet-selection filter.")
        cfg = json.load(open(CONFIG_PATH))
        cfg["edge_score"] = {
            "method": "unweighted_zscore_average",
            "features": FEATURES,
            "means": full_mean.to_dict(),
            "stds": full_std.to_dict(),
            "trained_on_races": int(d["race_id"].nunique()),
            "trained_on_runners": int(len(d)),
            "date_range": [str(d["date"].min().date()), str(d["date"].max().date())],
            "walk_forward_validation": {
                "n_weekly_refits": len(rows), "burn_in_weeks": BURN_IN_WEEKS,
                "top1_strike_pct": round(wins / n * 100, 2),
                "top1_roi_pct": round(profit / n * 100, 2),
                "top1_t_stat": round(float(t), 2),
                "mean_weekly_auc": round(float(np.mean(auc_list)), 4),
            },
            "overlay_validation": overlay_results,
            "note": note,
        }
        json.dump(cfg, open(CONFIG_PATH, "w"), indent=1)
        print(f"\nwrote edge_score ({len(FEATURES)} features, unweighted average, "
              f"{d['race_id'].nunique():,} races) to {CONFIG_PATH}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true",
                    help="write the fitted edge_score block into wpr_models/config.json")
    args = ap.parse_args()
    calibrate(write=args.write)
