"""
wpr_adj_cap_favourite_test.py - leak-free test of whether loosening the
ADJ_TERMS PER-TERM cap (_OWN_DELTA_CAP) closes the favourite-calibration
gap found in chat (Sep 2026): market favourites (shortest fixed price in
the race) actually win ~33% of the time, but WPR's own beta=0.15 softmax
price only credits them ~23%.

HISTORY (Sep 2026, both caught mid-run before any result was trusted):
  v1 swept _OWN_DELTA_TOTAL_CAP (the cap on the SUM of all 10 ADJ_TERMS,
  shipped at 6.0) - a direct check of toprate_runners.csv's wprp_contrib
  breakdown across 47,888 resulted runs showed the raw combined sum NEVER
  exceeds 1.1 in the entire dataset, so that cap never binds and the sweep
  was a no-op by construction.

  v2 swept the real bottleneck, _OWN_DELTA_CAP=3.0 (applied via _shrink()
  to 7 of the 10 terms: own_distance, own_going, own_first_up,
  own_second_up, own_trend, own_long_spell, closing_merit - hit exactly
  11-12% of the time each for the first three) - but crashed (closing_merit
  isn't a build_training_frame() column at all; it's only added later, per
  half, by add_closing_merit(), so the pre-loop sanity check KeyError'd),
  and building it uncovered a SEPARATE, real production bug while
  debugging: _shrink()'s cap clip, max(-cap, min(cap, shrunk)), does not
  propagate NaN (Python's min/max return the non-NaN operand), so a NaN
  delta silently became exactly +cap instead of the intended "unseen -> 0"
  fallback. Fixed directly in wpr_projection.py's _shrink() (returns 0.0
  on a NaN delta now); this script counts how often the old behaviour
  would have fired historically (see NAN_HIT_COUNT below) and uses the
  fixed function throughout.

METHOD (leak-free, same convention as wpr_bet_selection_leakfree_eval.py):
  wpr._OWN_DELTA_CAP is monkeypatched to an effectively-infinite value for
  the ENTIRE run (not just the shared build) - this makes every _shrink()
  call anywhere (both build_training_frame's own_distance/own_going/etc,
  AND add_closing_merit's per-half closing_merit) come back fully
  unclipped, so any smaller candidate cap can be re-applied afterward with
  a cheap clip in pandas rather than needing a separate rebuild per
  candidate. Uses the real, now NaN-safe _shrink() throughout (the fix in
  wpr_projection.py); the separate "how often did the old bug fire"
  question is answered by wpr_shrink_nan_bug_quantify.py instead, since
  counting it correctly here would need a cross-process shared counter
  (build_training_frame's n_jobs=-1 forks workers, and a plain Python
  counter's increments in a forked child never propagate back).

  50/50 chronological split. On EACH half (used as the fit half):
    - fit track_barrier/closing_merit's population baseline/trainer_merit/
      jockey_merit lookups on the fit half only
    - for each candidate per-term cap, clip the 7 affected terms to
      +/-cap, sum all 10 ADJ_TERMS, then refit a fresh OLS slope
      (target ~ a + b_base*_base + b_adj*adj_sum_at_this_cap) on the FIT
      HALF ONLY - same 2-variable decomposed regression the shipped
      0.1791 slope itself came from, just leak-free per half and swept
      over per-term cap values instead of fixed at 3.0
    - apply the fitted (a, b_base, b_adj) to the HELD-OUT half, fit price
      beta (grid search) purely on the fit half's own candidate
      projections, then score held-out MAE and the favourite-calibration
      gap (actual win rate vs beta-implied probability for the held-out
      half's market favourites) - both pooled across both directions
      (H1-fit/H2-score, H2-fit/H1-score) before reporting.

The shipped cap=3.0 is included as one of the candidates (refit at 3.0,
under the NOW-FIXED _shrink, to sanity-check the refit recovers close to
the shipped 0.1791 slope) alongside looser caps, so the shipped config
and the candidates are compared on the exact same held-out rows under the
exact same protocol.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm

# The 7 terms whose raw magnitude is bounded by _OWN_DELTA_CAP (via
# _shrink()) - these are what get re-clipped per candidate below.
SHRINK_TERMS = ["own_distance", "own_going", "own_first_up", "own_second_up",
                "own_trend", "own_long_spell", "closing_merit"]
# track_barrier/trainer_merit/jockey_merit are population lookups with
# their own K=300 shrinkage and no separate hard cap - carried through
# unchanged in every candidate.
UNCAPPED_TERMS = ["track_barrier", "trainer_merit", "jockey_merit"]

CAP_CANDIDATES = [3.0, 5.0, 8.0, 15.0, 1e9]  # 1e9 = effectively uncapped
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40, 0.50, 0.60, 0.80, 1.00]

def _adj_sum_at_cap(frame, cap):
    """frame's SHRINK_TERMS columns are already fully UNCAPPED (built with
    wpr._OWN_DELTA_CAP patched to ~infinity, for the whole run) - re-clip
    each to +/-cap here, then add the always-uncapped population-lookup
    terms. No total-sum cap (already shown inert at the shipped cap=3.0 in
    v1, so it's dropped from this sweep entirely - see module docstring)."""
    clipped = frame[SHRINK_TERMS].clip(lower=-cap, upper=cap)
    return clipped.sum(axis=1) + frame[UNCAPPED_TERMS].sum(axis=1)


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
    fit_half = fit_half.copy()
    held_out = held_out.copy()
    fit_half["_adj_sum"] = _adj_sum_at_cap(fit_half, cap)
    held_out["_adj_sum"] = _adj_sum_at_cap(held_out, cap)

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
    original_cap = wpr._OWN_DELTA_CAP
    wpr._OWN_DELTA_CAP = 1e9   # uncapped for the WHOLE run, not just the shared build
    try:
        print("Rebuilding training frame (full history, uncapped own-deltas, this takes a while)...")
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

        for t in ["own_distance", "own_going"]:
            pct_past_3 = (full[t].abs() > 3.0).mean() * 100
            print(f"  sanity: {t} |raw uncapped| > 3.0 for {pct_past_3:.1f}% of rows "
                  f"(max {full[t].abs().max():.2f}) - confirms uncapped build took effect, "
                  f"and no more 1e9 outliers now the NaN-cap bug is fixed")

        mid = full["date"].quantile(0.5)
        h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
        print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

        print(f"\n{'='*78}\nCandidate sweep (per-term cap -> refit slope), both directions pooled\n{'='*78}")
        for cap in CAP_CANDIDATES:
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

            if cap == CAP_CANDIDATES[0]:
                pct_cm = (h2_scored["closing_merit"].abs() > 3.0).mean() * 100
                print(f"  sanity: closing_merit |raw uncapped| > 3.0 for {pct_cm:.1f}% of held-out rows "
                      f"(max {h2_scored['closing_merit'].abs().max():.2f}) - confirms this term is "
                      f"ALSO correctly uncapped now (v2's crash meant this was never actually tested)")

            pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
            mae = held_out_mae(pooled, "_cand_proj")
            n_fav, actual_wr, implied_wr = favourite_calibration(pooled, "_cand_proj", "_cand_beta")

            b1 = h2_scored[["_fit_a", "_fit_b_base", "_fit_b_adj"]].iloc[0]
            b2 = h1_scored[["_fit_a", "_fit_b_base", "_fit_b_adj"]].iloc[0]
            beta1 = h2_scored["_cand_beta"].iloc[0]
            beta2 = h1_scored["_cand_beta"].iloc[0]

            cap_label = "uncapped" if cap > 1e6 else f"{cap:.1f}"
            print(f"\n--- per-term cap={cap_label} ---")
            print(f"  H1-fit: a={b1['_fit_a']:.3f} b_base={b1['_fit_b_base']:.3f} "
                  f"b_adj={b1['_fit_b_adj']:.4f} beta={beta1}")
            print(f"  H2-fit: a={b2['_fit_a']:.3f} b_base={b2['_fit_b_base']:.3f} "
                  f"b_adj={b2['_fit_b_adj']:.4f} beta={beta2}")
            print(f"  held-out MAE (pooled): {mae:.4f}")
            print(f"  market favourites (n={n_fav:,}): actual win rate={actual_wr*100:.1f}%  "
                  f"model-implied prob={implied_wr*100:.1f}%  gap={((actual_wr-implied_wr)*100):+.1f}pp")

        print("\n(How often the old pre-fix _shrink NaN-cap bug actually fired historically is")
        print(" quantified separately in wpr_shrink_nan_bug_quantify.py - counting it correctly here")
        print(" would need a cross-process shared counter, since build_training_frame's n_jobs=-1")
        print(" forks workers and a plain Python counter's increments in a forked child never")
        print(" propagate back to this process.)")

        print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
        print("row here as a hypothesis for a future walk-forward period, not a result to ship.")
    finally:
        wpr._OWN_DELTA_CAP = original_cap


if __name__ == "__main__":
    run()
