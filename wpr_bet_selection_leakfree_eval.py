"""
wpr_bet_selection_leakfree_eval.py - a GENUINELY leak-free version of
wpr_bet_selection_post_retrain.py's edge/ROI test.

WHY THIS EXISTS (see chat, Sep 2026)
  wpr_bet_selection_post_retrain.py applied the SHIPPED, final config.json
  population lookups (track_barrier, closing_merit, trainer_merit,
  jockey_merit) to every historical row, including the rows those very
  lookups were fitted from. For trainer_merit/jockey_merit specifically
  this is a real problem, not a theoretical one: trainer_win_pct_365d/
  jockey_win_pct_90d only exist in toprate_runners.csv's last ~4 months of
  daily snapshots, which is ALMOST THE ENTIRE evaluation window (Apr-Aug
  2026) - so "held out" there mostly wasn't. Re-deriving the price beta
  (Variant D) made the already-implausible ROI numbers WORSE, not better,
  which is the signature of leakage inflating a signal that a beta fix
  cannot touch.

  This script fixes it the same way wpr_trainer_jockey_adj_strike_eval.py
  already validated trainer_merit/jockey_merit itself: split the data
  50/50 by date, fit EVERY population-level artifact (track_barrier,
  closing_merit, trainer_merit, jockey_merit, the price-softmax beta, and
  the edge z-score means/stds) on one half ONLY, and score/evaluate ROI
  purely on the OTHER half. Doing this in both directions and pooling the
  two held-out halves back together gives one full-coverage dataset where
  every single row's wprp_proj and edge came from a fit that never saw
  that row (or any row from the same half) - genuinely leak-free, unlike
  the shipped-config approach.

  beta and the z-score means/stds are picked via IN-SAMPLE fit-half
  selection (same convention calibrate_price_beta.py/calibrate_edge_score.py
  already use for these low-risk scalar/normalization constants, as
  opposed to the ADJ_TERM population lookups themselves, which directly
  encode target - career_avg and so get the strict train/apply split).

USAGE
  python wpr_bet_selection_leakfree_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm, report

EDGE_FEATURES_A = ["wprp_proj", "trainer_win_pct_365d", "jockey_win_pct_90d", "pfm_score"]
EDGE_FEATURES_B = ["wprp_proj", "pfm_score"]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
EDGE_THRESHOLDS = [0.0, 0.08, 0.10, 0.13, 0.15, 0.20]
PRICE_CAPS = [15.0, 26.0]


def _score(data, mean, std, features):
    z = (data[features] - mean) / std.replace(0, np.nan)
    score = z.mean(axis=1, skipna=True)
    return score.where(data["wprp_proj"].notna(), 0.0)


def _brier(data, beta):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_half):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_half, b)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def _edge_from_score(frame, score_col):
    e = np.exp(frame[score_col] - frame.groupby("race_id")[score_col].transform("max"))
    p = e / frame.groupby("race_id")[score_col].transform(lambda s: np.exp(s - s.max()).sum())
    p_mkt = (1.0 / frame["sp"]) / frame.groupby("race_id")["sp"].transform(lambda s: (1.0 / s).sum())
    return p - p_mkt


def fit_and_score(fit_half, held_out, fit_cutoff):
    """Fits every population artifact on fit_half ONLY; returns held_out
    with wprp_proj + three edge columns computed purely from fit_half's
    fitted lookups/beta/means - held_out itself never contributes to any
    fit used to score it."""
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE

    beta = _fit_beta(fit_half)
    mean_a, std_a = fit_half[EDGE_FEATURES_A].mean(), fit_half[EDGE_FEATURES_A].std()
    mean_b, std_b = fit_half[EDGE_FEATURES_B].mean(), fit_half[EDGE_FEATURES_B].std()

    held_out = held_out.copy()
    held_out["score_a"] = _score(held_out, mean_a, std_a, EDGE_FEATURES_A)
    held_out["score_b"] = _score(held_out, mean_b, std_b, EDGE_FEATURES_B)
    held_out["edge_a"] = _edge_from_score(held_out, "score_a")
    held_out["edge_b"] = _edge_from_score(held_out, "score_b")
    held_out["score_wpr"] = beta * held_out["wprp_proj"]
    held_out["edge_wpr"] = _edge_from_score(held_out, "score_wpr")
    held_out["fit_beta"] = beta
    return held_out


def report_edge(bets, edge_col, label):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    fallback_pct = bets["used_sp_fallback"].mean() * 100
    print(f"total held-out bets: {len(bets):,}  (fixed_win_price fallback to SP for {fallback_pct:.1f}%)  "
          f"[population avg price ${bets['sp'].mean():.2f}]\n")
    print("=== Edge threshold alone ===")
    for thr in EDGE_THRESHOLDS:
        report(bets[bets[edge_col] >= thr], f"edge>={thr:.2f}")
    print("\n=== Edge threshold x price cap ===")
    for thr in EDGE_THRESHOLDS:
        base = bets[bets[edge_col] >= thr]
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"edge>={thr:.2f}, price<={cap:.0f}")


PRICE_BUCKETS = [1.0, 3.0, 5.0, 8.0, 15.0, 26.0, 1e9]
PRICE_BUCKET_LABELS = ["<3", "3-5", "5-8", "8-15", "15-26", ">26"]


def favourite_bias_diagnostic(pooled):
    """Are the edge-based strategies finding real signal, or just harvesting
    the market's own favourite-longshot bias (favourites structurally
    underbet, so ANY strategy that ends up mostly backing short-priced
    runners looks profitable regardless of the model)? Checks this
    directly: compares each edge variant's ROI WITHIN a price bucket
    against that SAME bucket's own unconditional baseline (backing every
    runner in that price range, no model at all). If the edge-filtered
    ROI is close to its bucket's baseline, the filter isn't adding
    anything beyond "pick a shorter price" - if it's clearly higher, that's
    real incremental selection skill on top of whatever price-bucket bias
    exists."""
    print(f"\n{'='*70}\nFAVOURITE-LONGSHOT BIAS DIAGNOSTIC\n{'='*70}")

    fav_idx = pooled.groupby("race_id")["sp"].idxmin()
    favs = pooled.loc[fav_idx]
    print("\n--- Baseline: back EVERY favourite (shortest price in the race), no model at all ---")
    report(favs, "every favourite")

    pooled = pooled.copy()
    pooled["bucket"] = pd.cut(pooled["sp"], bins=PRICE_BUCKETS, labels=PRICE_BUCKET_LABELS, right=False)

    print("\n--- Baseline: back EVERY runner in each price bucket, no model/edge filter at all ---")
    for b in PRICE_BUCKET_LABELS:
        report(pooled[pooled["bucket"] == b], f"bucket ${b} (unconditional, n=all)")

    for edge_col, name in [("edge_a", "A"), ("edge_b", "B"), ("edge_wpr", "WPR-alone")]:
        print(f"\n--- {name}: edge>=0.10-selected bets, BY price bucket "
              f"(compare each row to that bucket's unconditional baseline above) ---")
        sub = pooled[pooled[edge_col] >= 0.10]
        for b in PRICE_BUCKET_LABELS:
            report(sub[sub["bucket"] == b], f"{name} edge>=0.10, bucket ${b}")


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging result, trainer/jockey win-rate, price and pfm_score "
          "from toprate_runners.csv by (horse, date)...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_price_pfm(full)
    full = add_base(full)

    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["used_sp_fallback"] = sp.isna() & sp_fallback.notna()
    full["sp"] = sp.fillna(sp_fallback)
    full["pfm_score"] = pd.to_numeric(full["pfm_score"], errors="coerce")
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    print("\nFitting on H1, scoring held-out H2...")
    h2_scored = fit_and_score(h1.copy(), h2.copy(), h1["date"].max())
    print(f"  H1-fit beta: {h2_scored['fit_beta'].iloc[0]}")

    print("Fitting on H2, scoring held-out H1...")
    h1_scored = fit_and_score(h2.copy(), h1.copy(), h2["date"].max())
    print(f"  H2-fit beta: {h1_scored['fit_beta'].iloc[0]}")

    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} rows "
          f"(every row scored using ONLY the other half's fit)")

    report_edge(pooled, "edge_a", "Variant A (unchanged features, double-counts trainer/jockey) - LEAK-FREE")
    report_edge(pooled, "edge_b", "Variant B (trainer/jockey dropped from blend) - LEAK-FREE")
    report_edge(pooled, "edge_wpr", "Variant WPR (WPR price alone, beta refit per direction) - LEAK-FREE")

    favourite_bias_diagnostic(pooled)

    print("\nSame multiple-comparisons caveat as the earlier bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship.")


if __name__ == "__main__":
    run()
