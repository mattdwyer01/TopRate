"""
wpr_sectional_merit_strike_eval.py - tests two candidate ADJ_TERMS built
from TopRate's own detailed sectional RATINGS (13 signed index figures
per run, higher = better - see build_features' _SECT_COLS), which are
already computed (avg_sect_i_time, avg_sect_i_early, recent-6-run means)
but currently only feed the confidence models via FEATURES, never the
actual projection (a dedicated test this session found adding all 13 to
FEATURES barely moved confidence calibration, +0.243 -> +0.244, and by
architecture cannot move MAE/strike at all - see chat).

CANDIDATES
  sect_time_merit: from avg_sect_i_time (an overall time-based ability
    index) - plausibly redundant with wpr_nett/ewm3 already in BASE,
    since it is another measure of overall ability.
  sect_early_merit: from avg_sect_i_early (an early-sectional-strength
    index) - more likely distinct signal, since neither BASE nor any
    current ADJ_TERM directly captures "how strong is this horse's early
    sectional profile" (closing_merit is about LATE/closing sectionals
    specifically, pace-context-adjusted; this is a different phase).

METHODOLOGY: population-level fitted lookup (same structure as
track_barrier/gear_change), NOT a per-horse own-history match, since
avg_sect_i_X is already itself a per-horse recent-form summary (from
build_features) - bucket it into deciles (population-wide, fit on one
chronological half only), compute shrunk mean residual (target - _base)
per decile, apply to both halves. Held-out top-1 strike rate and MAE,
both directions, same adoption bar as every other candidate this
session (closing_merit/gear_change: strike-rate-both-directions is the
bar, MAE trading off is an accepted, known cost).

USAGE
  python wpr_sectional_merit_strike_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date

FORM_CSV = "wpr_form_history.csv.gz"
_SHRINK_K = 300.0  # matches wpr._TRACK_BARRIER_K (population-level lookup)
N_BUCKETS = 10


def add_closing_merit(apply_frames, cutoff_date):
    """Mirrors add_track_barrier's pattern for the OTHER population+own-
    history hybrid ADJ_TERM already in production (see wpr_projection.
    _fit_pace_baseline/_closing_merit_term) - needed here since the
    current 8-term baseline includes closing_merit and this frame must
    match production's proj_of() exactly."""
    lookup = wpr._fit_pace_baseline(FORM_CSV, cutoff_date)
    for frame in apply_frames:
        frame["closing_merit"] = [
            wpr._closing_merit_term(pairs, lookup) for pairs in frame["closing_pairs"]
        ]


def fit_sect_bucket_lookup(fit_rows, col):
    """Population mean residual (target - _base) per decile bucket of
    col, shrunk toward the global mean with strength _SHRINK_K, fit on
    fit_rows only. Returns (bucket_edges, lookup dict)."""
    d = fit_rows.dropna(subset=[col, "target", "_base"])
    edges = np.unique(np.quantile(d[col], np.linspace(0, 1, N_BUCKETS + 1)))
    resid = d["target"] - d["_base"]
    global_mean = resid.mean()
    bucket = np.digitize(d[col], edges[1:-1])
    lookup = {}
    for b in range(len(edges) - 1):
        m = resid[bucket == b]
        if len(m):
            n = len(m)
            shrunk = (n * m.mean() + _SHRINK_K * global_mean) / (n + _SHRINK_K)
            lookup[b] = float(shrunk - global_mean)
        else:
            lookup[b] = 0.0
    return edges, lookup


def apply_sect_bucket(frame, col, edges, lookup, out_col):
    vals = frame[col]
    bucket = np.digitize(vals, edges[1:-1])
    frame[out_col] = [lookup.get(b, 0.0) if v == v else 0.0 for b, v in zip(bucket, vals)]


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def proj_of(frame, extra_terms):
    # trainer_merit/jockey_merit need their own population-fit lookup
    # (like track_barrier/closing_merit) that this script never builds -
    # they are not plain columns here, so excluded from the base ADJ_TERMS
    # set (same exclusion as non_tb_terms below).
    terms = [t for t in wpr.ADJ_TERMS if t not in ("trainer_merit", "jockey_merit")] + extra_terms
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging race result (won) from toprate_runners.csv by (horse_id, date)...")
    full = merge_won_by_horse_date(full)

    full = add_base(full)
    non_tb_terms = [t for t in wpr.ADJ_TERMS
                    if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    print(f"\nScoped rows: {len(full):,}")
    for col in ["avg_sect_i_time", "avg_sect_i_early"]:
        print(f"  {col} coverage: {full[col].notna().mean()*100:.1f}%")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    def build_variant(fit_half, h1f, h2f, fit_cutoff):
        add_track_barrier(fit_half, [h1f, h2f])
        add_closing_merit([h1f, h2f], fit_cutoff)
        edges_t, lookup_t = fit_sect_bucket_lookup(fit_half, "avg_sect_i_time")
        edges_e, lookup_e = fit_sect_bucket_lookup(fit_half, "avg_sect_i_early")
        for f in (h1f, h2f):
            apply_sect_bucket(f, "avg_sect_i_time", edges_t, lookup_t, "sect_time_merit")
            apply_sect_bucket(f, "avg_sect_i_early", edges_e, lookup_e, "sect_early_merit")

    h1_d1, h2_d1 = h1.copy(), h2.copy()
    build_variant(h1_d1, h1_d1, h2_d1, h1["date"].max())

    h1_d2, h2_d2 = h1.copy(), h2.copy()
    build_variant(h2_d2, h1_d2, h2_d2, h2["date"].max())

    for d in (h1_d1, h2_d1, h1_d2, h2_d2):
        d["proj_base"] = proj_of(d, [])
        d["proj_time"] = proj_of(d, ["sect_time_merit"])
        d["proj_early"] = proj_of(d, ["sect_early_merit"])
        d["proj_both"] = proj_of(d, ["sect_time_merit", "sect_early_merit"])

    def report(candidate_col, label):
        print(f"\n========== {label} ==========")
        print("=== H1-fit/H2-validate direction ===")
        b_r1, b_k1, b_n1 = top1_strike_rate(h1_d1, "proj_base")
        b_r2, b_k2, b_n2 = top1_strike_rate(h2_d1, "proj_base")
        c_r1, c_k1, c_n1 = top1_strike_rate(h1_d1, candidate_col)
        c_r2, c_k2, c_n2 = top1_strike_rate(h2_d1, candidate_col)
        b_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_base"])
        c_mae2 = mean_absolute_error(h2_d1["target"], h2_d1[candidate_col])
        print(f"  top-1 strike:  baseline H1={b_k1}/{b_n1}={b_r1:.2f}%  H2(held-out)={b_k2}/{b_n2}={b_r2:.2f}%")
        print(f"  top-1 strike:  +{label} H1={c_k1}/{c_n1}={c_r1:.2f}%  H2(held-out)={c_k2}/{c_n2}={c_r2:.2f}%")
        print(f"  held-out MAE:  baseline={b_mae2:.4f}  +{label}={c_mae2:.4f}")

        print("=== H2-fit/H1-validate direction ===")
        b_r2b, b_k2b, b_n2b = top1_strike_rate(h2_d2, "proj_base")
        b_r1b, b_k1b, b_n1b = top1_strike_rate(h1_d2, "proj_base")
        c_r2b, c_k2b, c_n2b = top1_strike_rate(h2_d2, candidate_col)
        c_r1b, c_k1b, c_n1b = top1_strike_rate(h1_d2, candidate_col)
        b_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_base"])
        c_mae1 = mean_absolute_error(h1_d2["target"], h1_d2[candidate_col])
        print(f"  top-1 strike:  baseline H2={b_k2b}/{b_n2b}={b_r2b:.2f}%  H1(held-out)={b_k1b}/{b_n1b}={b_r1b:.2f}%")
        print(f"  top-1 strike:  +{label} H2={c_k2b}/{c_n2b}={c_r2b:.2f}%  H1(held-out)={c_k1b}/{c_n1b}={c_r1b:.2f}%")
        print(f"  held-out MAE:  baseline={b_mae1:.4f}  +{label}={c_mae1:.4f}")

        strike_improved = (c_r2 > b_r2) and (c_r1b > b_r1b)
        mae_improved = (c_mae2 < b_mae2) and (c_mae1 < b_mae1)
        print(f"  Top-1 strike improved BOTH directions: {strike_improved} "
              f"(H2: {b_r2:.2f}%->{c_r2:.2f}%, H1: {b_r1b:.2f}%->{c_r1b:.2f}%)")
        print(f"  Held-out MAE improved BOTH directions: {mae_improved} "
              f"(H2: {b_mae2:.4f}->{c_mae2:.4f}, H1: {b_mae1:.4f}->{c_mae1:.4f})")
        print(f"  ADOPTABLE (strike-rate bar): {strike_improved}")

    report("proj_time", "sect_time_merit")
    report("proj_early", "sect_early_merit")
    report("proj_both", "sect_time_merit+sect_early_merit combined")


if __name__ == "__main__":
    run()
