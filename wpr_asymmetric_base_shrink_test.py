"""
wpr_asymmetric_base_shrink_test.py - does asymmetrically discounting
ewm3 specifically when it's running hot relative to wpr_nett fix the
extreme-overconfidence bucket, without touching the (already fine, even
underconfident) case where nett exceeds ewm3?

WHY (Sep 2026): wpr_base_source_calibration_test.py + wpr_base_source_
direction_check.py found a ~40pp calibration swing depending purely on
sign/size of (wpr_nett - ewm3) - confirmed in both leak-free directions
independently. Dominance from a hot recent-form run (ewm3 >> nett) is
badly overconfident; dominance from a high TopRate rating (nett >> ewm3)
is far more reliable. A flat re-weight of the 50/50 alpha would move
BOTH cases the same direction - this tests a targeted fix instead: only
discount the excess when ewm3 > nett, leaving the nett > ewm3 case (and
the already-reasonable middle) untouched.

CANDIDATE: effective_ewm3 = ewm3 - max(0, ewm3 - wpr_nett) * DISCOUNT
DISCOUNT=0 reproduces the shipped blend exactly (baseline, for direct
comparison under this script's own protocol). DISCOUNT=1 fully caps
ewm3 at wpr_nett whenever it's running hot (the most aggressive
candidate). alpha stays fixed at the shipped 0.5 and the existing
piecewise base calibration is applied unchanged, to isolate the effect
of this one lever cleanly before conflating it with an alpha or
calibration-slope change (same one-lever-at-a-time discipline as the
earlier adjustment-cap sweep).

METHOD: leak-free 50/50 split, same per-half population-lookup fits and
fixed beta=0.15 as the other scripts in this series, loaded from the
shared disk cache.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import FORM_CSV, merge_trainer_jockey_by_horse_date, \
    add_closing_merit, fit_bucket_lookup, apply_bucket
from wpr_bet_selection_post_retrain import merge_price_pfm

FIXED_BETA = 0.15
CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
DISCOUNT_CANDIDATES = [0.0, 0.25, 0.5, 0.75, 1.0]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]


def _base_with_discount(frame, discount):
    """Replicates _compute_base's own branching exactly (both present ->
    blend, else fall back through ewm3/avg_last3/career_avg), just with
    ewm3 discounted toward wpr_nett whenever it's running hot, before the
    existing 50/50 blend and the existing piecewise calibration."""
    nett = frame["wpr_nett"]
    ewm3 = frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    excess = (ewm3 - nett).clip(lower=0)
    effective_ewm3 = ewm3 - excess * discount
    raw = pd.Series(np.where(both, 0.5 * nett + 0.5 * effective_ewm3, nett.fillna(ewm3)), index=frame.index)
    raw = raw.fillna(frame["avg_last3"]).fillna(frame["career_avg"])
    return raw.apply(wpr._calibrate_base)


def fit_and_score(fit_half, held_out, discount):
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["_base_cand"] = _base_with_discount(f, discount)
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
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def add_model_prob(frame, beta):
    frame = frame.copy()

    def _prob(g):
        pv = g["wprp_proj_cand"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    frame["model_prob"] = frame.groupby("race_id", group_keys=False).apply(_prob)
    return frame


def build_full():
    form_mtime = Path(FORM_CSV).stat().st_mtime
    if CACHE_PATH.exists():
        with open(CACHE_PATH, "rb") as fh:
            cached_mtime, full = pickle.load(fh)
        if cached_mtime == form_mtime:
            print(f"Loaded cached training frame ({len(full):,} rows) - skipping the ~15-20 min rebuild.")
            return full
        print("Cache is stale - rebuilding.")
    from wpr_own_pace_backtest import add_base
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


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    print(f"\n{'='*90}\nCandidate sweep: ewm3-hot-streak discount, both directions pooled\n{'='*90}")
    for discount in DISCOUNT_CANDIDATES:
        # fit_and_score mutates fit_half (h1f/h2g) in place with its own
        # wprp_proj_cand too, alongside returning held_out - reused directly
        # for the beta grid search instead of recomputing it a second time.
        h1f, h2f = h1.copy(), h2.copy()
        h2_scored = fit_and_score(h1f, h2f, discount)
        best_beta1 = min(BETA_GRID, key=lambda b: _brier(h1f, b))

        h1g, h2g = h1.copy(), h2.copy()
        h1_scored = fit_and_score(h2g, h1g, discount)
        best_beta2 = min(BETA_GRID, key=lambda b: _brier(h2g, b))

        h2_scored = add_model_prob(h2_scored, best_beta1)
        h1_scored = add_model_prob(h1_scored, best_beta2)
        pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)

        mae = (pooled["target"] - pooled["wprp_proj_cand"]).abs().mean()
        top_idx = pooled.groupby("race_id")["wprp_proj_cand"].idxmax()
        tops = pooled.loc[top_idx]
        high = tops[tops["model_prob"] >= 0.5]
        actual, implied = high["won"].mean(), high["model_prob"].mean()

        both = tops.dropna(subset=["wpr_nett", "ewm3"])
        hot = both[both["ewm3"] > both["wpr_nett"]]
        hot_high = hot[hot["model_prob"] >= 0.5]
        hot_actual = hot_high["won"].mean() if len(hot_high) else float("nan")
        hot_implied = hot_high["model_prob"].mean() if len(hot_high) else float("nan")

        print(f"\n--- discount={discount:.2f} (beta1={best_beta1}, beta2={best_beta2}) ---")
        print(f"  held-out MAE (pooled): {mae:.4f}")
        print(f"  >=50% implied group (n={len(high):,}): implied={implied*100:.1f}%  "
              f"actual={actual*100:.1f}%  gap={(actual-implied)*100:+.1f}pp")
        print(f"  ...of which ewm3>nett ('hot streak') subset (n={len(hot_high):,}): "
              f"implied={hot_implied*100:.1f}%  actual={hot_actual*100:.1f}%  "
              f"gap={(hot_actual-hot_implied)*100:+.1f}pp" if len(hot_high) else "  ...no hot-streak rows in this bucket")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
