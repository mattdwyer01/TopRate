"""
wpr_conditional_beta_test.py - does applying a LOWER (flatter) beta
specifically to races whose top-WPR-rated runner is hot-streak-driven
(ewm3 > wpr_nett) fix the extreme-overconfidence bucket, where the
rating-side fix (wpr_asymmetric_base_shrink_test.py) failed?

WHY (Sep 2026): discounting a hot-streak horse's ewm3 input barely moved
its own calibration gap (-54.0pp -> -53.7pp even at full strength) -
correlation across horses (hot-streak dominance is less reliable) didn't
mean the ewm3 NUMBER was the mechanism; capping it didn't make the horse
"become" more reliable. This tests a different lever entirely: instead
of changing WHAT the rating is, change HOW SHARPLY that rating gap
converts to probability, conditional on the race's own top pick being
hot-streak-sourced - i.e. accept the rating as computed, but flatten its
translation into an implied probability specifically when the reliability
marker (ewm3 > nett) is present for that race's own top pick.

CANDIDATE: beta_race = BETA_HOT if the race's own top-WPR-rated runner
has ewm3 > wpr_nett, else the standard FIXED_BETA (0.15) - swept over
BETA_HOT in [0.05, 0.075, 0.10, 0.125, 0.15] (0.15 reproduces the
shipped behaviour exactly, for direct comparison under this script's own
protocol). wprp_proj itself (base + adjustment) is UNCHANGED throughout -
only which beta scales it into a probability changes, and only for
flagged races.

BETA_HOT is picked leak-free: on the FIT half, restricted to races whose
own top pick is hot-streak-flagged, find the BETA_HOT minimising Brier
score on THAT subset only - then apply to the held-out half's flagged
races. Non-flagged races use the standard FIXED_BETA throughout, both
halves.

METHOD: leak-free 50/50 split, same per-half population-lookup fits as
the other scripts in this series, loaded from the shared disk cache.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm

FIXED_BETA = 0.15
CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
BETA_HOT_CANDIDATES = [0.05, 0.075, 0.10, 0.125, 0.15]


def fit_and_score(fit_half, held_out):
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["wprp_proj"] = f["_base"].to_numpy() + f["adj_total"].to_numpy()
    return held_out.copy()


def flag_hot_streak_races(frame):
    """race_id -> True if that race's own top-WPR-rated runner has
    ewm3 > wpr_nett (both present; unknown/missing treated as not-hot,
    conservative default - only flag when the marker is actually present)."""
    top_idx = frame.groupby("race_id")["wprp_proj"].idxmax()
    tops = frame.loc[top_idx]
    hot = (tops["ewm3"] > tops["wpr_nett"]) & tops["ewm3"].notna() & tops["wpr_nett"].notna()
    return dict(zip(tops["race_id"], hot))


def model_prob_conditional(frame, beta_hot, hot_flags):
    frame = frame.copy()
    frame["_is_hot_race"] = frame["race_id"].map(hot_flags).fillna(False)

    def _prob(g):
        beta = beta_hot if g["_is_hot_race"].iloc[0] else FIXED_BETA
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    frame["model_prob"] = frame.groupby("race_id", group_keys=False).apply(_prob)
    return frame


def _brier_on_subset(frame, beta, race_ids):
    sub = frame[frame["race_id"].isin(race_ids)]
    rows = []
    for rid, g in sub.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")


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
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return full


def report_candidate(beta_hot, pooled):
    top_idx = pooled.groupby("race_id")["wprp_proj"].idxmax()
    tops = pooled.loc[top_idx]

    overall_brier = ((pooled["model_prob"] - pooled["won"]) ** 2).mean()
    high = tops[tops["model_prob"] >= 0.5]
    actual, implied = high["won"].mean(), high["model_prob"].mean()

    both = tops.dropna(subset=["wpr_nett", "ewm3"])
    hot = both[both["ewm3"] > both["wpr_nett"]]
    hot_high = hot[hot["model_prob"] >= 0.5]
    hot_actual = hot_high["won"].mean() if len(hot_high) else float("nan")
    hot_implied = hot_high["model_prob"].mean() if len(hot_high) else float("nan")

    not_hot = both[both["ewm3"] <= both["wpr_nett"]]
    not_hot_high = not_hot[not_hot["model_prob"] >= 0.5]
    nh_actual = not_hot_high["won"].mean() if len(not_hot_high) else float("nan")
    nh_implied = not_hot_high["model_prob"].mean() if len(not_hot_high) else float("nan")

    label = beta_hot if isinstance(beta_hot, str) else f"{beta_hot:.3f}"
    print(f"\n--- beta_hot={label} ---")
    print(f"  overall Brier (every runner, pooled): {overall_brier:.4f}")
    print(f"  >=50% implied group (n={len(high):,}): implied={implied*100:.1f}%  "
          f"actual={actual*100:.1f}%  gap={(actual-implied)*100:+.1f}pp")
    if len(hot_high):
        print(f"  ...hot-streak subset (n={len(hot_high):,}): implied={hot_implied*100:.1f}%  "
              f"actual={hot_actual*100:.1f}%  gap={(hot_actual-hot_implied)*100:+.1f}pp")
    else:
        print("  ...no hot-streak rows in this bucket")
    if len(not_hot_high):
        print(f"  ...non-hot-streak subset (n={len(not_hot_high):,}): implied={nh_implied*100:.1f}%  "
              f"actual={nh_actual*100:.1f}%  gap={(nh_actual-nh_implied)*100:+.1f}pp")


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    print("\nFitting on H1, scoring held-out H2...")
    h2_scored = fit_and_score(h1.copy(), h2.copy())
    print("Fitting on H2, scoring held-out H1...")
    h1_scored = fit_and_score(h2.copy(), h1.copy())

    # Leak-free BETA_HOT selection needs each FIT half's own hot-streak
    # races flagged too (fit_and_score already mutated h1/h2 copies above
    # via the held_out argument, but not the fit_half itself with the
    # OTHER direction's population lookups - refit each fit half against
    # itself as its own "held out" just to get its own wprp_proj for flagging).
    h1_for_fit = fit_and_score(h1.copy(), h1.copy())
    h2_for_fit = fit_and_score(h2.copy(), h2.copy())

    fit1_hot_flags = flag_hot_streak_races(h1_for_fit)
    fit1_hot_ids = [rid for rid, is_hot in fit1_hot_flags.items() if is_hot]
    fit2_hot_flags = flag_hot_streak_races(h2_for_fit)
    fit2_hot_ids = [rid for rid, is_hot in fit2_hot_flags.items() if is_hot]
    print(f"\nH1 (fit-half) hot-streak races: {len(fit1_hot_ids):,} / {h1_for_fit['race_id'].nunique():,}")
    print(f"H2 (fit-half) hot-streak races: {len(fit2_hot_ids):,} / {h2_for_fit['race_id'].nunique():,}")

    best_beta_hot_1 = min(BETA_HOT_CANDIDATES, key=lambda b: _brier_on_subset(h1_for_fit, b, fit1_hot_ids))
    best_beta_hot_2 = min(BETA_HOT_CANDIDATES, key=lambda b: _brier_on_subset(h2_for_fit, b, fit2_hot_ids))
    print(f"Leak-free fitted beta_hot: H1-fit={best_beta_hot_1}, H2-fit={best_beta_hot_2}")

    h2_hot_flags = flag_hot_streak_races(h2_scored)
    h1_hot_flags = flag_hot_streak_races(h1_scored)

    print(f"\n{'='*90}\nCandidate sweep: conditional beta for hot-streak-flagged races, pooled\n{'='*90}")
    for beta_hot in BETA_HOT_CANDIDATES:
        h2_prob = model_prob_conditional(h2_scored, beta_hot, h2_hot_flags)
        h1_prob = model_prob_conditional(h1_scored, beta_hot, h1_hot_flags)
        pooled = pd.concat([h1_prob, h2_prob], ignore_index=True)
        report_candidate(beta_hot, pooled)

    h2_prob = model_prob_conditional(h2_scored, best_beta_hot_1, h2_hot_flags)
    h1_prob = model_prob_conditional(h1_scored, best_beta_hot_2, h1_hot_flags)
    pooled = pd.concat([h1_prob, h2_prob], ignore_index=True)
    report_candidate(f"{best_beta_hot_1}/{best_beta_hot_2}", pooled)

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
