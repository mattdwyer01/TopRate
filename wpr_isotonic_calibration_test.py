"""
wpr_isotonic_calibration_test.py - tests whether a post-hoc isotonic
recalibration on top of the shipped softmax(beta=0.15) win probability
further improves calibration/ROI, following up on a diagnostic finding
(see chat, Sep 2026): the STORED wprp_blend_prob column in
toprate_runners.csv showed severe top-decile overconfidence (46.7%
predicted vs 27.8% actual) - but that column is only recomputed for each
day's OWN races (compute_edge_score() scopes to target_date_str, never
retroactively rewrites history, same staleness discipline as wprp_proj
itself), so it was measuring a mix mostly dominated by the OLD beta=0.3
era, not the current beta=0.15 (recalibrated 2026-09-12 via
calibrate_price_beta.py, already held-out validated).

Recomputing FRESH with current beta=0.15 (same fair-comparison technique
calibrate_price_beta.py itself uses) showed the bulk of the problem is
already fixed: top-decile 30.9% predicted vs 28.1% actual, Brier 0.0934
(stale) -> 0.0878 (fresh). BUT a finer look at just the very top of the
distribution still shows a real, smaller residual: top 1% by predicted
prob (n=553) is 53.7% predicted vs 45.4% actual (an 8.3pt gap, ~4
standard errors - not noise). A single global softmax beta is a
one-parameter calibration curve; it may not be flexible enough to
capture the TRUE shape of the probability-vs-outcome relationship at the
extreme tail even when it's well-fit everywhere else.

WHAT THIS TESTS: fit an isotonic regression (monotonic, non-parametric -
strictly more flexible than a single beta, and rank-preserving so it
can't change WPR's actual selections) mapping raw softmax(beta=0.15)
probability -> P(win), on one half of resulted races; apply to the OTHER
half (renormalized per race back to sum=1, the standard convention for
recalibrating a multiclass/softmax output); pool both directions. Same
leak-free bidirectional half-split as every other test tonight.

Reports: Brier score, log-loss, and a reliability table, raw vs
isotonic-calibrated, on held-out data. ALSO checks the downstream ROI
impact: edge (calibrated model_prob - market_prob) at the existing
EDGE_THRESHOLDS, since a probability recalibration changes what "edge"
means even though it can't change which horse WPR likes best.

WHY wprp_proj IS RECOMPUTED FRESH, NOT READ FROM toprate_runners.csv:
same reasoning as calibrate_price_beta.py - reuses its _load_resulted()
directly so this test is immune to the exact staleness bug that made
the original diagnostic look worse than reality.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
from sklearn.isotonic import IsotonicRegression

from calibrate_price_beta import _load_resulted, DEFAULT_DAYS_BACK
from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import EDGE_THRESHOLDS

BETA = 0.15
DAYS_BACK = 150  # wider window than calibrate_price_beta.py's default 45 -
                  # _load_resulted() recomputes wprp_proj fresh regardless
                  # of window size, so a bigger sample costs time, not
                  # correctness, and this test wants real n at the extreme
                  # tail (top 1%) where the residual showed up.


def softmax_by_race(data, beta=BETA):
    """Raw softmax win probability per runner, race-scoped, >=4 finishers
    only (small fields are structurally different - a 3-horse race can
    have a "favourite" north of 50% fair price with no overconfidence
    involved at all)."""
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.append(pd.DataFrame({"p_raw": p, "won": g["won"].to_numpy(),
                                   "race_id": rid}, index=g.index))
    return pd.concat(rows) if rows else pd.DataFrame(columns=["p_raw", "won", "race_id"])


def apply_isotonic(iso, scored):
    """Apply a fitted isotonic map to p_raw, then renormalise per race
    back to sum=1 - the standard convention for recalibrating a
    multiclass/softmax output (isotonic operates per-runner and has no
    knowledge of the race-level simplex constraint on its own)."""
    s = scored.copy()
    s["p_iso_raw"] = iso.predict(s["p_raw"].to_numpy())
    race_sum = s.groupby("race_id")["p_iso_raw"].transform("sum")
    s["p_iso"] = s["p_iso_raw"] / race_sum.replace(0, np.nan)
    return s.dropna(subset=["p_iso"])


def brier(p, won):
    return float(((p - won) ** 2).mean())


def logloss(p, won):
    pc = np.clip(p, 1e-6, 1 - 1e-6)
    return float(-np.mean(won * np.log(pc) + (1 - won) * np.log(1 - pc)))


def reliability(scored, col, n_bins=10):
    s = scored.copy()
    s["bin"] = pd.qcut(s[col], n_bins, labels=False, duplicates="drop")
    return s.groupby("bin").agg(pred=(col, "mean"), actual=("won", "mean"), n=("won", "size"))


def run():
    print(f"Loading resulted races (fresh wprp_proj via compute_wpr_projection, "
          f"{DAYS_BACK} days back)...")
    d = _load_resulted(days_back=DAYS_BACK)
    d = d.dropna(subset=["wprp_proj", "won", "race_id", "date"])
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races, "
          f"{d['date'].min()} .. {d['date'].max()}")

    mid = d["date"].quantile(0.5)
    h1, h2 = d[d["date"] < mid].copy(), d[d["date"] >= mid].copy()
    print(f"H1: {h1['race_id'].nunique():,} races (< {mid.date() if hasattr(mid, 'date') else mid}), "
          f"H2: {h2['race_id'].nunique():,} races")

    pooled_raw, pooled_iso = [], []
    for fit_h, held_h, label in [(h1, h2, "H1->H2"), (h2, h1, "H2->H1")]:
        fit_scored = softmax_by_race(fit_h)
        held_scored = softmax_by_race(held_h)
        print(f"\n{label}: fit n={len(fit_scored):,}, held-out n={len(held_scored):,}")

        iso = IsotonicRegression(out_of_bounds="clip", y_min=0.0, y_max=1.0)
        iso.fit(fit_scored["p_raw"].to_numpy(), fit_scored["won"].to_numpy())

        held_iso = apply_isotonic(iso, held_scored)
        # keep both frames aligned to the same row set (isotonic renorm can
        # drop a race if its whole race_sum collapsed, extremely rare)
        held_raw = held_scored.loc[held_iso.index]

        print(f"  raw:  Brier={brier(held_raw['p_raw'], held_raw['won']):.4f}  "
              f"logloss={logloss(held_raw['p_raw'], held_raw['won']):.4f}")
        print(f"  iso:  Brier={brier(held_iso['p_iso'], held_iso['won']):.4f}  "
              f"logloss={logloss(held_iso['p_iso'], held_iso['won']):.4f}")

        pooled_raw.append(held_raw)
        pooled_iso.append(held_iso)

    raw_all = pd.concat(pooled_raw, ignore_index=True)
    iso_all = pd.concat(pooled_iso, ignore_index=True)

    print("\n" + "=" * 78)
    print("POOLED HELD-OUT CALIBRATION: raw softmax(beta=0.15) vs isotonic-recalibrated")
    print("=" * 78)
    print(f"n={len(raw_all):,}")
    print(f"Brier   raw={brier(raw_all['p_raw'], raw_all['won']):.4f}   "
          f"iso={brier(iso_all['p_iso'], iso_all['won']):.4f}")
    print(f"logloss raw={logloss(raw_all['p_raw'], raw_all['won']):.4f}   "
          f"iso={logloss(iso_all['p_iso'], iso_all['won']):.4f}")

    print("\n--- reliability (10 deciles), raw ---")
    print(reliability(raw_all, "p_raw").to_string())
    print("\n--- reliability (10 deciles), isotonic ---")
    print(reliability(iso_all, "p_iso").to_string())

    print("\n--- top of the distribution (raw vs iso) ---")
    for top_pct in (0.05, 0.02, 0.01):
        thr_raw = raw_all["p_raw"].quantile(1 - top_pct)
        top_raw = raw_all[raw_all["p_raw"] >= thr_raw]
        thr_iso = iso_all["p_iso"].quantile(1 - top_pct)
        top_iso = iso_all[iso_all["p_iso"] >= thr_iso]
        print(f"top {top_pct*100:.0f}%: raw pred={top_raw['p_raw'].mean():.3f} "
              f"actual={top_raw['won'].mean():.3f} (n={len(top_raw)})  |  "
              f"iso pred={top_iso['p_iso'].mean():.3f} "
              f"actual={top_iso['won'].mean():.3f} (n={len(top_iso)})")

    # ROI impact: recompute edge using calibrated probability against
    # market price, same convention/thresholds as every ROI test tonight.
    print("\n" + "=" * 78)
    print("ROI IMPACT (edge = model_prob - market_prob, raw vs isotonic-calibrated)")
    print("=" * 78)
    for name, scored in [("raw (beta=0.15 softmax)", raw_all), ("isotonic-recalibrated", iso_all)]:
        s = scored.copy()
        price_col = None
        for c in ("fixed_win_price", "starting_price_sp", "price_top"):
            if c in s.columns:
                sp = pd.to_numeric(s[c], errors="coerce")
                s["sp"] = sp if price_col is None else s["sp"].fillna(sp)
                price_col = c
        if "sp" not in s.columns:
            print(f"\n--- {name} ---  (no price column found, skipping ROI)")
            continue
        s = s.dropna(subset=["sp"])
        s = s[s["sp"] > 1.0]
        prob_col = "p_iso" if "p_iso" in s.columns else "p_raw"
        s["mkt_prob"] = s.groupby("race_id")["sp"].transform(lambda x: (1 / x) / (1 / x).sum())
        s["edge_wpr"] = s[prob_col] - s["mkt_prob"]
        print(f"\n--- {name} ---")
        print(f"total held-out bets: {len(s):,}  [population avg price ${s['sp'].mean():.2f}]")
        for thr in EDGE_THRESHOLDS:
            report(s[s["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
