"""
calibrate_edge_score.py - HISTORICAL / NOT USED IN PRODUCTION (Sep 2026).
compute_edge_scores() no longer reads the "edge_score" config block this
script writes - once trainer_merit/jockey_merit became ADJ_TERMS inside
wprp_proj itself, this blend was double-counting that signal (once raw,
once via WPR), and a leak-free walk-forward test found WPR's own price
ALONE beats every blend variant on ROI - see wpr_projection.
compute_edge_scores' own docstring for the full reasoning and
wpr_bet_selection_leakfree_eval.py for the test. Kept only for its
documented history of what was tried and why (same status as
toprate_html_v3.py - reference, not live). Do not re-run --write; it
would populate a config block nothing reads.

ORIGINAL DOCSTRING (for history):
fit the "edge score": an unweighted z-score
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
    # wprp_price - the field-relative softmax price already shown on the
    # dashboard (see wpr_projection.project_race) - loaded here too so
    # wpr_price_edge_report() below can compare "edge vs the number the user
    # actually sees" against the blend-score edge above, without a second
    # CSV read.
    df["wprp_price"] = pd.to_numeric(df.get("wprp_price"), errors="coerce")
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
        test["model_prob"] = p
        for _, row in test.iterrows():
            edge_bets.append((row["won"], row["sp"], row["edge"], row["model_prob"]))
    return (rows, auc_list, ll_list, np.array(bet_profits),
            pd.DataFrame(edge_bets, columns=["won", "sp", "edge", "model_prob"]))


# Price brackets for segmenting the overlay test - favourite-longshot bias
# means a pooled overlay result (as the base walk_forward_validate/calibrate
# report above does) can hide a real signal in one bracket, or make a bracket
# with a genuine leak look tolerable once averaged with the rest. Bucketed by
# the runner's own SP, since that's the standard framing for favourite-
# longshot bias in the literature (final market position, not entry price -
# see the CLV note below for why entry price isn't usable here).
PRICE_BRACKETS = [
    ("favourite <=$3", 1.0, 3.0),
    ("mid $3-8", 3.0, 8.0),
    ("longshot $8-20", 8.0, 20.0),
    ("roughie $20+", 20.0, float("inf")),
]


def calibration_report(edge_bets):
    """Reliability diagram as a table: bucket every walk-forward runner by
    model_prob (not just the ones flagged as overlays), compare predicted
    probability to actual empirical win rate per bucket. This is checked
    BEFORE any overlay/edge analysis because it answers a more basic
    question the pooled overlay test doesn't: are the model's probabilities
    trustworthy at all, independent of how they compare to the market. A
    model that ranks well (see the AUC numbers above) can still be poorly
    calibrated - e.g. systematically overconfident on short-priced runners -
    which would make any edge computed from it unreliable regardless of
    threshold."""
    bins = [0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 1.01]
    labels = ["0-5%", "5-10%", "10-15%", "15-20%", "20-30%", "30-50%", "50%+"]
    d = edge_bets.copy()
    d["bucket"] = pd.cut(d["model_prob"], bins=bins, labels=labels, right=False)
    print("\n  calibration (predicted probability vs actual win rate, all walk-forward runners):")
    print(f"    {'bucket':<10} {'n':>7} {'mean predicted':>15} {'actual win rate':>16} {'diff':>8}")
    for label in labels:
        sub = d[d["bucket"] == label]
        if len(sub) < 20:
            continue
        pred = sub["model_prob"].mean()
        actual = sub["won"].mean()
        print(f"    {label:<10} {len(sub):>7,} {pred*100:>14.1f}% {actual*100:>15.1f}% "
              f"{(actual-pred)*100:>+7.1f}pp")
    print("    (a well-calibrated bucket has actual close to predicted; a bucket that's "
          "consistently over-predicted means the model is overconfident there, which would "
          "make edge computed against that bucket's runners look better than it really is)")


def overlay_by_bracket(edge_bets):
    """Repeats calibrate()'s pooled edge>=threshold overlay test, but
    separately within each PRICE_BRACKET, since a pooled result can hide a
    bracket-specific signal (or bracket-specific leak) that averages out to
    "not significant" overall. Same t-test methodology as the pooled
    version - see calibrate() for the significance-flagging convention."""
    print("\n  edge-vs-market overlay, segmented by price bracket:")
    for label, lo, hi in PRICE_BRACKETS:
        bracket = edge_bets[(edge_bets["sp"] > lo) & (edge_bets["sp"] <= hi)]
        print(f"\n    -- {label} (n={len(bracket):,} runners in bracket) --")
        any_tested = False
        for thr in [0.0, 0.05, 0.08, 0.10, 0.13, 0.15, 0.20]:
            sub = bracket[bracket["edge"] >= thr]
            if len(sub) < 20:
                continue
            any_tested = True
            profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
            se = profit.std(ddof=1) / np.sqrt(len(profit))
            t = profit.mean() / se if se > 0 else float("nan")
            flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
            print(f"      edge>={thr:.2f}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
                  f"ROI={profit.sum()/len(sub)*100:+6.2f}%  t={t:+.2f}{flag}")
        if not any_tested:
            print("      (fewer than 20 bets at every threshold in this bracket - too few to test)")


def _overlay_sweep(bets, label_indent="    "):
    """Shared edge>=threshold t-test sweep, used by wpr_price_edge_report()
    below. calibrate()'s own pooled loop and overlay_by_bracket() predate
    this helper and are left as their own inline loops (each has slightly
    different bookkeeping - significant_negative/positive tracking for the
    production --write note - not worth the risk of refactoring already-
    validated code to remove the duplication)."""
    for thr in [0.0, 0.05, 0.08, 0.10, 0.13, 0.15, 0.20]:
        sub = bets[bets["edge"] >= thr]
        if len(sub) < 20:
            continue
        profit = np.where(sub["won"] == 1, sub["sp"] - 1, -1.0)
        se = profit.std(ddof=1) / np.sqrt(len(profit))
        t = profit.mean() / se if se > 0 else float("nan")
        flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
        print(f"{label_indent}edge>={thr:.2f}: n={len(sub):5d}  strike={sub['won'].mean()*100:5.2f}%  "
              f"ROI={profit.sum()/len(sub)*100:+6.2f}%  t={t:+.2f}{flag}")


def wpr_price_edge_report(d):
    """Same edge = model_prob - market_prob idea as compute_edge_scores, but
    with model_prob taken straight from wprp_price (the field-relative
    softmax price the dashboard already shows, from wpr_projection.
    project_race) instead of the separate blend-score z-average.

    No walk-forward refitting needed here, unlike the blend score - wprp_
    price is already a genuine pre-race number the production pipeline
    computed with no knowledge of the result, so there's no leakage risk in
    using it directly across the whole history in one pass (more data than
    the blend's walk-forward test gets after burn-in).

    Answers a different question than the blend-score edge: is "edge
    relative to the number the user actually sees on the Race tab" a
    usable signal, as opposed to edge relative to a blend the dashboard
    doesn't surface directly. Trade-off: wprp_proj alone was the weakest of
    the ablated features in the Aug 2026 edge-score audit (trainer/jockey
    trailing form did most of the work) - so expect this to rank worse than
    the blend on AUC/strike rate. Whether it does better, worse, or the same
    on the OVERLAY specifically is a separate, open question - that's what
    this checks."""
    sub = d.dropna(subset=["wprp_price"]).copy()
    sub["model_prob_raw"] = 1.0 / sub["wprp_price"]
    sub["model_prob"] = (sub["model_prob_raw"]
                          / sub.groupby("race_id")["model_prob_raw"].transform("sum"))
    sub["mkt_prob_raw"] = 1.0 / sub["sp"]
    sub["mkt_prob"] = (sub["mkt_prob_raw"]
                        / sub.groupby("race_id")["mkt_prob_raw"].transform("sum"))
    sub["edge"] = sub["model_prob"] - sub["mkt_prob"]

    print(f"\n{'='*60}\nwprp_price edge report ({sub['race_id'].nunique():,} races, "
          f"{len(sub):,} runners, {sub['date'].min().date()} to {sub['date'].max().date()})")

    top1 = sub.loc[sub.groupby("race_id")["model_prob"].idxmax()]
    profit = np.where(top1["won"] == 1, top1["sp"] - 1, -1.0)
    se = profit.std(ddof=1) / np.sqrt(len(profit))
    t = profit.mean() / se
    auc = roc_auc_score(sub["won"], sub["model_prob"]) if sub["won"].nunique() == 2 else float("nan")
    print(f"  top-1 pick (by wprp_price alone): n={len(top1):,}  strike={top1['won'].mean()*100:.2f}%  "
          f"ROI={profit.sum()/len(top1)*100:+.2f}%  t={t:+.2f}")
    print(f"  AUC (whole field, all runners) = {auc:.4f}")

    print("\n  edge-vs-market overlay (pooled, wprp_price as model_prob):")
    _overlay_sweep(sub)

    print("\n  edge-vs-market overlay, segmented by price bracket (wprp_price as model_prob):")
    for label, lo, hi in PRICE_BRACKETS:
        bracket = sub[(sub["sp"] > lo) & (sub["sp"] <= hi)]
        print(f"\n    -- {label} (n={len(bracket):,} runners in bracket) --")
        _overlay_sweep(bracket, label_indent="      ")


def calibrate(write=False, extended=False):
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

    if extended:
        calibration_report(edge_bets)
        overlay_by_bracket(edge_bets)
        print(
            "\n  CLV / entry-price note: wanted to also test edge computed against an early "
            "(bettable) price rather than starting_price_sp, and to check CLV (does the price "
            "move toward our pick after we'd have bet it) - not possible with current data. "
            "fixed_win_price in toprate_runners.csv correlates 0.97 with starting_price_sp "
            "(exactly equal 45% of the time, median abs diff $0.10) because it's overwritten on "
            "every price_refresh.yml run, so by resulted time it just IS the closing price, not "
            "an earlier one. toprate_runners.csv's own open_price column has only 7% coverage. "
            "toprate_price_history.csv has genuine open-vs-current snapshots but only keeps a "
            "rolling 7 days (by design, see snapshot_prices() in toprate_daily.py) - nowhere near "
            "enough history for a walk-forward validation. Revisit once price_history has "
            "accumulated months of data, or if a separate un-rotated price log is ever kept."
        )

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
    ap.add_argument("--extended", action="store_true",
                    help="also report a calibration/reliability table and the overlay "
                         "threshold test segmented by price bracket (favourite/mid/"
                         "longshot/roughie), on top of the standard pooled report")
    ap.add_argument("--wpr-price-edge", action="store_true",
                    help="also report the edge-vs-market overlay (pooled and by price "
                         "bracket) using wprp_price directly as model_prob, instead of "
                         "the blend score - i.e. edge relative to the number already "
                         "shown on the dashboard, not the separate trainer/jockey blend")
    args = ap.parse_args()
    calibrate(write=args.write, extended=args.extended)
    if args.wpr_price_edge:
        wpr_price_edge_report(_load_resulted())
