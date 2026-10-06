"""
wpr_base_redesign_tests.py - three follow-up tests to the nett-vs-ewm3
finding, all leak-free, all loaded from the shared disk cache:

  A. Remove ewm3 from base entirely (alpha=1.0, base=wpr_nett only) -
     does dropping it fix the extreme-tail overconfidence, and at what
     overall accuracy cost? (precedent: removing wpr_nett entirely, the
     OTHER half of the blend, cost a real, measured 0.56 held-out MAE in
     Aug 2026 before being reverted - this checks the symmetric question
     for ewm3 rather than assuming the same trade-off applies.)

  B. Class-move-gated ewm3 discount - the earlier flat ewm3-hot-streak
     discount (wpr_asymmetric_base_shrink_test.py) barely moved the
     needle. This tests a sharper version of the same idea: only discount
     the hot-streak excess when there's ALSO a genuine "hollow form"
     signal - class_move (already an existing, leak-safe feature: today's
     class rung minus the mean rung of the horse's last 5 runs) strongly
     positive, meaning the recent hot form was earned against a WEAKER
     grade than today's race. First reports the diagnostic (does
     class_move actually differ between the hot-streak subset and
     everyone else, and does it predict the calibration gap within the
     hot-streak subset) before testing the gated discount itself.

  C. Population improvement-by-experience - the current model only rates
     horses with >=3 prior runs at all (_MIN_RUNS filters below that), so
     true 0-2-start debutants are already out of scope for this exact
     check (a separate, structural gap - queued elsewhere). This tests
     the adjacent, answerable question: for horses in their early starts
     (n_runs in the training frame currently bottoms out at 3), is there
     a REMAINING systematic improvement trend by experience even AFTER
     their own individual base rating - i.e. does a population-level
     "horses at this many starts typically still improve" residual exist,
     leak-free fit on one half and checked on the other, the same
     population-shrinkage convention track_barrier/trainer_merit already
     use.

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
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]


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


def raw_base(frame, base_fn):
    nett, ewm3 = frame["wpr_nett"], frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    blended = pd.Series(np.where(both, base_fn(nett, ewm3), nett.fillna(ewm3)), index=frame.index)
    blended = blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])
    return blended.apply(wpr._calibrate_base)


def fit_and_score(fit_half, held_out, base_fn):
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_cand"] = raw_base(f, base_fn)
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["wprp_proj_cand"] = f["_base_cand"] + f["adj_total"]
    return held_out.copy()


def _brier(data, beta):
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj_cand"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")


def add_model_prob(frame, beta):
    frame = frame.copy()

    def _prob(g):
        pv = g["wprp_proj_cand"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    frame["model_prob"] = frame.groupby("race_id", group_keys=False).apply(_prob)
    return frame


def run_candidate(label, h1, h2, base_fn):
    h1f, h2f = h1.copy(), h2.copy()
    h2_scored = fit_and_score(h1f, h2f, base_fn)
    beta1 = min(BETA_GRID, key=lambda b: _brier(h1f, b))
    h1g, h2g = h1.copy(), h2.copy()
    h1_scored = fit_and_score(h2g, h1g, base_fn)
    beta2 = min(BETA_GRID, key=lambda b: _brier(h2g, b))

    h2_scored = add_model_prob(h2_scored, beta1)
    h1_scored = add_model_prob(h1_scored, beta2)
    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)

    mae = (pooled["target"] - pooled["wprp_proj_cand"]).abs().mean()
    top_idx = pooled.groupby("race_id")["wprp_proj_cand"].idxmax()
    tops = pooled.loc[top_idx]
    high = tops[tops["model_prob"] >= 0.5]
    actual, implied = (high["won"].mean(), high["model_prob"].mean()) if len(high) else (float("nan"), float("nan"))

    both = tops.dropna(subset=["wpr_nett", "ewm3"])
    hot = both[both["ewm3"] > both["wpr_nett"]]
    hot_high = hot[hot["model_prob"] >= 0.5]
    hot_actual = hot_high["won"].mean() if len(hot_high) else float("nan")
    hot_implied = hot_high["model_prob"].mean() if len(hot_high) else float("nan")

    print(f"\n--- {label} (beta1={beta1}, beta2={beta2}) ---")
    print(f"  held-out MAE (pooled): {mae:.4f}")
    print(f"  >=50% implied group (n={len(high):,}): implied={implied*100:.1f}%  actual={actual*100:.1f}%  "
          f"gap={(actual-implied)*100:+.1f}pp")
    if len(hot_high):
        print(f"  ...hot-streak subset (n={len(hot_high):,}): implied={hot_implied*100:.1f}%  "
              f"actual={hot_actual*100:.1f}%  gap={(hot_actual-hot_implied)*100:+.1f}pp")
    return pooled


def test_a(h1, h2):
    print(f"\n{'='*90}\nTEST A: remove ewm3 entirely (base = wpr_nett only)\n{'='*90}")
    run_candidate("shipped (50/50 nett/ewm3)", h1, h2, lambda n, e: 0.5 * n + 0.5 * e)
    run_candidate("ewm3 removed (100% nett)", h1, h2, lambda n, e: n)


def test_b_diagnostic(full):
    print(f"\n{'='*90}\nTEST B (diagnostic): does class_move differ for the hot-streak subset?\n{'='*90}")
    # Pure descriptive diagnostic (not a leak-free evaluation) - in-sample
    # population-lookup fit on the whole frame is fine here, just to get a
    # wprp_proj to identify each race's own top pick by.
    full = full.copy()
    add_track_barrier(full, [full])
    add_closing_merit([full], full["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(full, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(full, "jockey_win_pct_90d")
    apply_bucket(full, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(full, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
    full["wprp_proj"] = full["_base"] + wpr._cap_adj_sum(
        full[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE

    top_idx = full.groupby("race_id")["wprp_proj"].idxmax()
    tops = full.loc[top_idx].dropna(subset=["wpr_nett", "ewm3"]).copy()
    hot = tops[tops["ewm3"] > tops["wpr_nett"]]
    not_hot = tops[tops["ewm3"] <= tops["wpr_nett"]]
    print(f"  hot-streak tops (n={len(hot):,}): avg class_move={hot['class_move'].mean():+.2f}")
    print(f"  non-hot-streak tops (n={len(not_hot):,}): avg class_move={not_hot['class_move'].mean():+.2f}")

    print("\n  Within hot-streak tops: does class_move predict reliability?")
    hot = hot.copy()
    buckets = pd.qcut(hot["class_move"], 4, duplicates="drop")
    for b, g in hot.groupby(buckets, observed=True):
        print(f"    class_move {b}: n={len(g):4,d}  avg class_move={g['class_move'].mean():+6.2f}  "
              f"actual win rate={g['won'].mean()*100:5.1f}%")


def test_b_fix(h1, h2):
    print(f"\n{'='*90}\nTEST B (fix): class-move-gated ewm3 discount\n{'='*90}")

    # class_move isn't visible inside raw_base(nett, ewm3) directly - build
    # the candidate base inline here instead of via the simple base_fn hook.
    def raw_base_class_gated(frame, slope, cap):
        nett, ewm3, cmove = frame["wpr_nett"], frame["ewm3"], frame["class_move"]
        excess = (ewm3 - nett).clip(lower=0)
        discount = (cmove * slope).clip(lower=0, upper=cap)
        effective_ewm3 = ewm3 - excess * discount
        both = nett.notna() & ewm3.notna()
        blended = pd.Series(np.where(both, 0.5 * nett + 0.5 * effective_ewm3, nett.fillna(ewm3)), index=frame.index)
        blended = blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])
        return blended.apply(wpr._calibrate_base)

    def fit_and_score_gated(fit_half, held_out, slope, cap):
        add_track_barrier(fit_half, [fit_half, held_out])
        add_closing_merit([fit_half, held_out], fit_half["date"].max())
        edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
        edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
        for f in (fit_half, held_out):
            apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
            apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
            f["_base_cand"] = raw_base_class_gated(f, slope, cap)
            f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
            f["wprp_proj_cand"] = f["_base_cand"] + f["adj_total"]
        return held_out.copy()

    for slope, cap in [(0.0, 1.0), (0.02, 1.0), (0.05, 1.0), (0.1, 1.0)]:
        h1f, h2f = h1.copy(), h2.copy()
        h2_scored = fit_and_score_gated(h1f, h2f, slope, cap)
        beta1 = min(BETA_GRID, key=lambda b: _brier(h1f, b))
        h1g, h2g = h1.copy(), h2.copy()
        h1_scored = fit_and_score_gated(h2g, h1g, slope, cap)
        beta2 = min(BETA_GRID, key=lambda b: _brier(h2g, b))
        h2_scored = add_model_prob(h2_scored, beta1)
        h1_scored = add_model_prob(h1_scored, beta2)
        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)

        mae = (pooled["target"] - pooled["wprp_proj_cand"]).abs().mean()
        top_idx = pooled.groupby("race_id")["wprp_proj_cand"].idxmax()
        tops = pooled.loc[top_idx]
        high = tops[tops["model_prob"] >= 0.5]
        actual, implied = (high["won"].mean(), high["model_prob"].mean()) if len(high) else (float("nan"),) * 2
        both = tops.dropna(subset=["wpr_nett", "ewm3"])
        hot = both[both["ewm3"] > both["wpr_nett"]]
        hot_high = hot[hot["model_prob"] >= 0.5]
        hot_actual = hot_high["won"].mean() if len(hot_high) else float("nan")
        hot_implied = hot_high["model_prob"].mean() if len(hot_high) else float("nan")
        print(f"\n--- slope={slope:.2f} (per class-rung discount, capped at {cap:.0%}) ---")
        print(f"  held-out MAE: {mae:.4f}")
        print(f"  >=50% group (n={len(high):,}): gap={(actual-implied)*100:+.1f}pp")
        if len(hot_high):
            print(f"  ...hot-streak subset (n={len(hot_high):,}): gap={(hot_actual-hot_implied)*100:+.1f}pp")


def test_c(full):
    print(f"\n{'='*90}\nTEST C: population improvement-by-experience for early-start horses\n{'='*90}")
    print(f"  n_runs range in this frame: {full['n_runs'].min():.0f} to {full['n_runs'].max():.0f} "
          f"(the model only rates horses with >=3 prior runs at all - true 0-2-start debutants are")
    print(f"  structurally out of scope for this exact frame, a separate gap)")

    # Must compare against the CALIBRATED base, not the raw pre-calibration
    # blend - _base itself is raw (see add_base), and calibration exists
    # specifically to correct raw-base-vs-actual bias, so comparing target
    # against raw _base would just rediscover "calibration is needed" (already
    # known) rather than a REMAINING trend after the existing correction.
    full = full.copy()
    full["_base_calibrated"] = full["_base"].apply(wpr._calibrate_base)
    full["_resid"] = full["target"] - full["_base_calibrated"]
    buckets = [3, 4, 5, 6, 8, 10, 15, 25, 1000]
    labels = ["3", "4", "5", "6", "7-8", "9-10", "11-15", "16-25", "26+"]
    full["n_runs_bucket"] = pd.cut(full["n_runs"], bins=[2] + buckets, labels=labels)
    print("\n  Residual (actual target minus current base) by career start count:")
    print("  (a positive residual here means the CURRENT base under-rates horses at that experience")
    print("   level on average - i.e. a real, unexploited population improvement trend)")
    for b, g in full.groupby("n_runs_bucket", observed=True):
        if len(g) < 30:
            continue
        print(f"    n_runs={b:>6}: n={len(g):6,d}  avg residual={g['_resid'].mean():+.3f}  "
              f"std={g['_resid'].std():.2f}")


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    test_a(h1, h2)
    test_b_diagnostic(full)
    test_b_fix(h1, h2)
    test_c(full)

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
