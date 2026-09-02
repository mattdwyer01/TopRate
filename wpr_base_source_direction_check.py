"""
wpr_base_source_direction_check.py - does the nett-vs-ewm3 calibration
finding (wpr_base_source_calibration_test.py) hold up in BOTH leak-free
directions separately, or is the pooled result being driven by one half?

Same setup, same cache, but reports H1-fit/H2-score and H2-fit/H1-score
as two independent breakdowns instead of pooling them - if the same
"ewm3-driven dominance is unreliable, nett-driven dominance is reliable"
shape shows up in both halves independently, that's real signal, not a
one-half fluke.

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


def add_model_prob(frame, beta):
    frame = frame.copy()

    def _prob(g):
        pv = g["wprp_proj"].to_numpy(dtype=float)
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


def top_picks_with_source(scored):
    """Each race's top-rated runner, with nett_minus_ewm3 attached."""
    top_idx = scored.groupby("race_id")["wprp_proj"].idxmax()
    tops = scored.loc[top_idx].copy()
    return tops.dropna(subset=["wpr_nett", "ewm3"]).copy()


def report_direction(label, tops):
    tops = tops.copy()
    tops["nett_minus_ewm3"] = tops["wpr_nett"] - tops["ewm3"]
    print(f"\n--- {label}: whole top-rated population (n={len(tops):,}) ---")
    buckets = pd.qcut(tops["nett_minus_ewm3"], 4, duplicates="drop")
    for b, g in tops.groupby(buckets, observed=True):
        actual, implied = g["won"].mean(), g["model_prob"].mean()
        print(f"    nett-ewm3 {b}: n={len(g):4,d}  avg(nett-ewm3)={g['nett_minus_ewm3'].mean():+5.1f}  "
              f"avg model_prob={implied*100:5.1f}%  actual win rate={actual*100:5.1f}%  "
              f"gap={((actual-implied)*100):+5.1f}pp")

    high = tops[tops["model_prob"] >= 0.5]
    print(f"  --- {label}: >=50% implied group only (n={len(high):,}) ---")
    if len(high) < 40:
        print("    too small to bucket further")
        return
    hbuckets = pd.qcut(high["nett_minus_ewm3"], 4, duplicates="drop")
    for b, g in high.groupby(hbuckets, observed=True):
        actual, implied = g["won"].mean(), g["model_prob"].mean()
        print(f"    nett-ewm3 {b}: n={len(g):4,d}  avg(nett-ewm3)={g['nett_minus_ewm3'].mean():+5.1f}  "
              f"avg model_prob={implied*100:5.1f}%  actual win rate={actual*100:5.1f}%  "
              f"gap={((actual-implied)*100):+5.1f}pp")


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")
    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    print(f"\nFitting on H1, scoring held-out H2 (beta fixed at {FIXED_BETA})...")
    h2_scored = add_model_prob(fit_and_score(h1.copy(), h2.copy()), FIXED_BETA)
    print(f"Fitting on H2, scoring held-out H1 (beta fixed at {FIXED_BETA})...")
    h1_scored = add_model_prob(fit_and_score(h2.copy(), h1.copy()), FIXED_BETA)

    print(f"\n{'='*90}\nDirection 1: fit on H1, scored on held-out H2 (H2 dates only)\n{'='*90}")
    report_direction("H1-fit / H2-score", top_picks_with_source(h2_scored))

    print(f"\n{'='*90}\nDirection 2: fit on H2, scored on held-out H1 (H1 dates only)\n{'='*90}")
    report_direction("H2-fit / H1-score", top_picks_with_source(h1_scored))

    print("\nIf both directions show the same shape (ewm3-driven dominance worse, nett-driven")
    print("dominance better) independently, that's real signal, not a one-half fluke.")


if __name__ == "__main__":
    run()
