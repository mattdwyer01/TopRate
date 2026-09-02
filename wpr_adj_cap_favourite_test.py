"""
wpr_adj_cap_favourite_test.py - leak-free test of whether loosening the
ADJ_TERMS total cap (and refitting its calibration slope) closes the
favourite-calibration gap found in chat (Sep 2026): market favourites
(shortest fixed price in the race) actually win ~33% of the time, but
WPR's own beta=0.15 softmax price only credits them ~23%. Traced to
_OWN_DELTA_TOTAL_CAP=6.0 + _CALIB_ADJ_SLOPE=0.1791 capping the maximum
possible combined contribution of all 10 ADJ_TERMS at about +-1.1 points -
so almost the entire favourite/field rating gap has to come from _base
(a horse's own general level, not race-relative), which only manages
about a 4.7-point average edge for favourites - not enough for beta to
turn into a well-calibrated probability.

METHOD (leak-free, same convention as wpr_bet_selection_leakfree_eval.py):
  50/50 chronological split. On EACH half (used as the fit half):
    - fit track_barrier/closing_merit/trainer_merit/jockey_merit lookups
      on the fit half only (reused helpers)
    - for each candidate total-adjustment cap, refit a fresh OLS slope
      (target ~ a + b_base*_base + b_adj*adj_sum_at_this_cap) on the FIT
      HALF ONLY - same 2-variable decomposed regression the shipped
      0.1791 slope itself came from, just leak-free per half and swept
      over cap values instead of fixed at 6.0
    - apply the fitted (a, b_base, b_adj) to the HELD-OUT half to get a
      candidate wprp_proj, then fit price beta (grid search, same as
      wpr_bet_selection_leakfree_eval.py) purely on the fit half's own
      candidate projections
    - score held-out MAE (target vs candidate projection) and the
      favourite-calibration gap (actual win rate vs beta-implied
      probability for the held-out half's market favourites) - both
      pooled across both directions (H1-fit/H2-score, H2-fit/H1-score)
      before reporting, so every row is scored by a fit that never saw it.

The shipped cap=6.0/slope=0.1791 combination is included as one of the
candidates (refit at cap=6.0, to sanity-check the refit recovers close to
0.1791) plus looser caps, so the shipped config and the candidates are
compared on the exact same held-out rows under the exact same protocol.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm

CAP_CANDIDATES = [6.0, 9.0, 12.0, 18.0, 1e9]  # 1e9 = effectively uncapped (per-term caps at +-3 still apply)
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40, 0.50, 0.60, 0.80, 1.00]


def _raw_adj_sum(frame, cap):
    """Same per-term capping/shrinkage as production (_shrink already baked
    into each ADJ_TERMS column), just with the TOTAL cap swapped out for
    `cap` instead of the shipped _OWN_DELTA_TOTAL_CAP=6.0."""
    vals = frame[wpr.ADJ_TERMS].to_numpy(dtype=float)
    row_sum = vals.sum(axis=1)
    scale = np.ones(len(row_sum))
    over = np.abs(row_sum) > cap
    nonzero_over = over & (row_sum != 0)
    scale[nonzero_over] = cap / np.abs(row_sum[nonzero_over])
    return (vals * scale[:, None]).sum(axis=1)


def _fit_ols(y, x1, x2):
    """target ~ a + b1*x1 + b2*x2, plain OLS via lstsq. Returns (a, b1, b2)."""
    X = np.column_stack([np.ones(len(y)), x1, x2])
    coef, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
    return coef[0], coef[1], coef[2]


def _brier(data, beta, proj_col):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g[proj_col].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def _fit_beta(fit_half, proj_col):
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        br = _brier(fit_half, b, proj_col)
        if br < best_brier:
            best_brier, best_beta = br, b
    return best_beta


def fit_and_score_candidate(fit_half, held_out, cap):
    """Fits the (a, b_base, b_adj) OLS on fit_half at this cap, applies to
    held_out, fits beta on fit_half's own resulting projections, returns
    held_out with a candidate projection + fitted beta attached."""
    fit_half = fit_half.copy()
    held_out = held_out.copy()
    fit_half["_adj_sum"] = _raw_adj_sum(fit_half, cap)
    held_out["_adj_sum"] = _raw_adj_sum(held_out, cap)

    a, b_base, b_adj = _fit_ols(fit_half["target"].to_numpy(),
                                 fit_half["_base"].to_numpy(),
                                 fit_half["_adj_sum"].to_numpy())
    fit_half["_cand_proj"] = a + b_base * fit_half["_base"] + b_adj * fit_half["_adj_sum"]
    held_out["_cand_proj"] = a + b_base * held_out["_base"] + b_adj * held_out["_adj_sum"]

    beta = _fit_beta(fit_half, "_cand_proj")
    held_out["_cand_beta"] = beta
    held_out["_fit_a"] = a
    held_out["_fit_b_base"] = b_base
    held_out["_fit_b_adj"] = b_adj
    return held_out


def favourite_calibration(pooled, proj_col, beta_col):
    """Market favourites (shortest fixed price per race) only: actual win
    rate vs the model-implied probability under this candidate's own
    fitted beta (each row already carries the beta fitted on ITS side's
    fit-half, per fit_and_score_candidate)."""
    fav_idx = pooled.groupby("race_id")["sp"].idxmin()
    favs = pooled.loc[fav_idx].copy()

    def _implied_prob(g):
        beta = g[beta_col].iloc[0]
        pv = g[proj_col].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        return pd.Series(p, index=g.index)

    implied = pooled.groupby("race_id", group_keys=False).apply(_implied_prob)
    fav_prob = implied.loc[favs.index]
    return len(favs), float(favs["won"].mean()), float(fav_prob.mean())


def held_out_mae(pooled, proj_col):
    return float((pooled["target"] - pooled[proj_col]).abs().mean())


def run():
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging result, trainer/jockey win-rate, price from toprate_runners.csv...")
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
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    print("\nFitting population lookups (track_barrier/closing_merit/trainer_merit/jockey_merit)...")
    add_track_barrier(h1, [h1, h2])
    add_closing_merit([h1, h2], h1["date"].max())
    edges_t1, lookup_t1 = fit_bucket_lookup(h1, "trainer_win_pct_365d")
    edges_j1, lookup_j1 = fit_bucket_lookup(h1, "jockey_win_pct_90d")
    apply_bucket(h1, "trainer_win_pct_365d", edges_t1, lookup_t1, "trainer_merit")
    apply_bucket(h1, "jockey_win_pct_90d", edges_j1, lookup_j1, "jockey_merit")
    apply_bucket(h2, "trainer_win_pct_365d", edges_t1, lookup_t1, "trainer_merit")
    apply_bucket(h2, "jockey_win_pct_90d", edges_j1, lookup_j1, "jockey_merit")

    add_track_barrier(h2, [h1, h2])
    add_closing_merit([h1, h2], h2["date"].max())
    edges_t2, lookup_t2 = fit_bucket_lookup(h2, "trainer_win_pct_365d")
    edges_j2, lookup_j2 = fit_bucket_lookup(h2, "jockey_win_pct_90d")
    # Note: h1/h2 track_barrier/closing_merit above get overwritten by
    # whichever fit ran last - each direction below re-fits its OWN
    # population lookups on ITS fit half right before scoring, so this is
    # just prep; the real leak-free application happens per-direction in
    # the loop.

    print(f"\n{'='*78}\nCandidate sweep (cap -> refit slope), both directions pooled\n{'='*78}")
    for cap in CAP_CANDIDATES:
        # Direction 1: fit on H1 (re-fit pop lookups on H1 only), score H2
        h1f, h2f = h1.copy(), h2.copy()
        add_track_barrier(h1f, [h1f, h2f])
        add_closing_merit([h1f, h2f], h1f["date"].max())
        et, lt = fit_bucket_lookup(h1f, "trainer_win_pct_365d")
        ej, lj = fit_bucket_lookup(h1f, "jockey_win_pct_90d")
        apply_bucket(h1f, "trainer_win_pct_365d", et, lt, "trainer_merit")
        apply_bucket(h1f, "jockey_win_pct_90d", ej, lj, "jockey_merit")
        apply_bucket(h2f, "trainer_win_pct_365d", et, lt, "trainer_merit")
        apply_bucket(h2f, "jockey_win_pct_90d", ej, lj, "jockey_merit")
        h2_scored = fit_and_score_candidate(h1f, h2f, cap)

        # Direction 2: fit on H2, score H1
        h1g, h2g = h1.copy(), h2.copy()
        add_track_barrier(h2g, [h1g, h2g])
        add_closing_merit([h1g, h2g], h2g["date"].max())
        et2, lt2 = fit_bucket_lookup(h2g, "trainer_win_pct_365d")
        ej2, lj2 = fit_bucket_lookup(h2g, "jockey_win_pct_90d")
        apply_bucket(h2g, "trainer_win_pct_365d", et2, lt2, "trainer_merit")
        apply_bucket(h2g, "jockey_win_pct_90d", ej2, lj2, "jockey_merit")
        apply_bucket(h1g, "trainer_win_pct_365d", et2, lt2, "trainer_merit")
        apply_bucket(h1g, "jockey_win_pct_90d", ej2, lj2, "jockey_merit")
        h1_scored = fit_and_score_candidate(h2g, h1g, cap)

        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
        mae = held_out_mae(pooled, "_cand_proj")
        n_fav, actual_wr, implied_wr = favourite_calibration(pooled, "_cand_proj", "_cand_beta")

        b1 = h2_scored[["_fit_a", "_fit_b_base", "_fit_b_adj"]].iloc[0]
        b2 = h1_scored[["_fit_a", "_fit_b_base", "_fit_b_adj"]].iloc[0]
        beta1 = h2_scored["_cand_beta"].iloc[0]
        beta2 = h1_scored["_cand_beta"].iloc[0]

        cap_label = "uncapped (per-term +-3 still applies)" if cap > 1e6 else f"{cap:.1f}"
        print(f"\n--- cap={cap_label} ---")
        print(f"  H1-fit: a={b1['_fit_a']:.3f} b_base={b1['_fit_b_base']:.3f} "
              f"b_adj={b1['_fit_b_adj']:.4f} beta={beta1}")
        print(f"  H2-fit: a={b2['_fit_a']:.3f} b_base={b2['_fit_b_base']:.3f} "
              f"b_adj={b2['_fit_b_adj']:.4f} beta={beta2}")
        print(f"  held-out MAE (pooled): {mae:.4f}")
        print(f"  market favourites (n={n_fav:,}): actual win rate={actual_wr*100:.1f}%  "
              f"model-implied prob={implied_wr*100:.1f}%  gap={((actual_wr-implied_wr)*100):+.1f}pp")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship.")


if __name__ == "__main__":
    run()
