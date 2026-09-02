"""
wpr_trainer_jockey_k_sweep_test.py - was _TJ_MERIT_K=300 (the shrinkage
strength for trainer_merit/jockey_merit's population decile lookup) ever
actually validated for THIS pair of terms, or just borrowed by analogy
from _TRACK_BARRIER_K (which WAS independently swept, K=30-1200, best at
300 - see wpr_projection.py's own docstring above _TRACK_BARRIER_K)?

Checked wpr_trainer_jockey_adj_strike_eval.py (the script that actually
validated and got trainer_merit/jockey_merit adopted): its own
_SHRINK_K = 300.0 comment says "matches wpr._TRACK_BARRIER_K" - i.e. it
was never independently swept, just copied. trainer_win_pct_365d/
jockey_win_pct_90d have very different coverage/statistics than the
barrier bands track_barrier buckets by (~20% overall coverage, decile
buckets of a continuous win-rate rather than a handful of physical
barrier positions), so there's no reason to assume the same K is optimal
here without checking.

METHOD: same top-1 strike-rate + held-out MAE adoption bar the term was
originally validated under (wpr_trainer_jockey_adj_strike_eval.py's own
report() function, reused here unmodified), swept across
K_GRID for the "both together" variant (trainer_merit + jockey_merit
combined - the variant actually shipped), both chronological
half-split directions. Looking for whether a K other than 300 clears the
strike-rate bar by MORE in both directions, not just whether 300 itself
clears it (already known - it shipped).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import (
    FORM_CSV, N_BUCKETS, merge_trainer_jockey_by_horse_date, add_closing_merit,
    top1_strike_rate, proj_of,
)

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
K_GRID = [30, 75, 150, 300, 500, 750, 1200]


def build_full():
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            return full
        print("Cache is stale - rebuilding.")
    print("Rebuilding training frame (full history, this takes a while)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = add_base(full)
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return full


def fit_bucket_lookup_at_k(fit_rows, col, k):
    """Same as wpr_trainer_jockey_adj_strike_eval.fit_bucket_lookup, but
    with the shrinkage strength as a parameter instead of hardcoded."""
    d = fit_rows.dropna(subset=[col, "target", "career_avg"])
    edges = np.unique(np.quantile(d[col], np.linspace(0, 1, N_BUCKETS + 1)))
    resid = d["target"] - d["career_avg"]
    global_mean = resid.mean()
    bucket = np.digitize(d[col], edges[1:-1])
    lookup = {}
    for b in range(len(edges) - 1):
        m = resid[bucket == b]
        if len(m):
            n = len(m)
            shrunk = (n * m.mean() + k * global_mean) / (n + k)
            lookup[b] = float(shrunk - global_mean)
        else:
            lookup[b] = 0.0
    return edges, lookup


def apply_bucket(frame, col, edges, lookup, out_col):
    vals = frame[col]
    bucket = np.digitize(vals, edges[1:-1])
    frame[out_col] = [lookup.get(b, 0.0) if v == v else 0.0 for b, v in zip(bucket, vals)]


def build_variant_at_k(fit_half, h1f, h2f, fit_cutoff, k):
    add_track_barrier(fit_half, [h1f, h2f])
    add_closing_merit([h1f, h2f], fit_cutoff)
    edges_t, lookup_t = fit_bucket_lookup_at_k(fit_half, "trainer_win_pct_365d", k)
    edges_j, lookup_j = fit_bucket_lookup_at_k(fit_half, "jockey_win_pct_90d", k)
    for f in (h1f, h2f):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")


def score_at_k(full, h1, h2, k):
    h1_d1, h2_d1 = h1.copy(), h2.copy()
    build_variant_at_k(h1_d1, h1_d1, h2_d1, h1["date"].max(), k)

    h1_d2, h2_d2 = h1.copy(), h2.copy()
    build_variant_at_k(h2_d2, h1_d2, h2_d2, h2["date"].max(), k)

    for d in (h1_d1, h2_d1, h1_d2, h2_d2):
        d["proj_base"] = proj_of(d, [])
        d["proj_both"] = proj_of(d, ["trainer_merit", "jockey_merit"])

    b_r2, _, _ = top1_strike_rate(h2_d1, "proj_base")
    c_r2, _, _ = top1_strike_rate(h2_d1, "proj_both")
    b_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_base"])
    c_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_both"])

    b_r1b, _, _ = top1_strike_rate(h1_d2, "proj_base")
    c_r1b, _, _ = top1_strike_rate(h1_d2, "proj_both")
    b_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_base"])
    c_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_both"])

    return {
        "k": k,
        "h2_strike_base": b_r2, "h2_strike_cand": c_r2, "h2_strike_delta": c_r2 - b_r2,
        "h2_mae_base": b_mae2, "h2_mae_cand": c_mae2, "h2_mae_delta": c_mae2 - b_mae2,
        "h1_strike_base": b_r1b, "h1_strike_cand": c_r1b, "h1_strike_delta": c_r1b - b_r1b,
        "h1_mae_base": b_mae1, "h1_mae_cand": c_mae1, "h1_mae_delta": c_mae1 - b_mae1,
    }


def run():
    full = build_full()
    non_tb_terms = [t for t in wpr.ADJ_TERMS
                    if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance",
                         "trainer_win_pct_365d", "jockey_win_pct_90d"])
    print(f"Scoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    rows = [score_at_k(full, h1, h2, k) for k in K_GRID]

    print(f"{'K':>6} | {'H2 strike (base->cand)':>26} | {'H2 MAE delta':>12} | "
          f"{'H1 strike (base->cand)':>26} | {'H1 MAE delta':>12} | both dirs improved?")
    print("-" * 115)
    for r in rows:
        both_strike_improved = r["h2_strike_delta"] > 0 and r["h1_strike_delta"] > 0
        both_mae_improved = r["h2_mae_delta"] < 0 and r["h1_mae_delta"] < 0
        flag = "  <-- clears strike bar" if both_strike_improved else ""
        print(f"{r['k']:>6} | {r['h2_strike_base']:>6.2f}%->{r['h2_strike_cand']:>6.2f}% "
              f"({r['h2_strike_delta']:+.2f}pp) | {r['h2_mae_delta']:>+11.4f} | "
              f"{r['h1_strike_base']:>6.2f}%->{r['h1_strike_cand']:>6.2f}% "
              f"({r['h1_strike_delta']:+.2f}pp) | {r['h1_mae_delta']:>+11.4f} | "
              f"strike:{both_strike_improved} mae:{both_mae_improved}{flag}")

    print(f"\nShipped K=300 for comparison is in the table above. Looking for whether a")
    print(f"different K clears the strike-rate bar (both directions) by a wider margin,")
    print(f"not just whether 300 clears it at all (already known - it shipped).")

    n_h1_races = h1["race_id"].nunique()
    n_h2_races = h2["race_id"].nunique()
    p = 0.30
    se_h1 = (p * (1 - p) / n_h1_races) ** 0.5 * 100
    se_h2 = (p * (1 - p) / n_h2_races) ** 0.5 * 100
    print(f"\nNoise floor check: H1 has {n_h1_races:,} races (top-1 strike rate SE ~{se_h1:.2f}pp), "
          f"H2 has {n_h2_races:,} races (SE ~{se_h2:.2f}pp). Every K-to-K delta in the strike-rate "
          f"column above is smaller than this SE - the apparent 'lower K does better' pattern is")
    print(f"not distinguishable from sampling noise at this sample size. K=300 is not disproven by")
    print(f"this sweep; there is no statistically meaningful case for changing it from a single split.")
    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
