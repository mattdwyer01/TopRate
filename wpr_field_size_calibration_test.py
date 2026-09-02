"""
wpr_field_size_calibration_test.py - does field size explain why beta=0.15
is wildly overconfident on runners it rates above 50% to win (708-runner
n at 70.4% implied vs 33.4% actual, found in wpr_favourite_calibration_
curve.py)?

HYPOTHESIS: a softmax's implied probability for the top-rated horse is
mechanically pushed higher just by having FEWER rivals to split
probability mass among, for the same underlying rating gap - so an
extreme implied probability might often reflect "small field" more than
"genuinely dominant horse", and a fixed beta has no way to tell the two
apart.

METHOD: reuses the exact same leak-free fixed-beta=0.15 setup (see
wpr_favourite_calibration_curve.py for the full writeup), then checks
the >=50% implied-probability group specifically: does its average field
size differ from the rest of the population, and does the calibration
gap (actual - implied) vary by field-size bucket WITHIN that group and
across the whole population.

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
FIELD_SIZE_BUCKETS = [0, 6, 8, 10, 12, 100]
FIELD_SIZE_LABELS = ["<=6", "7-8", "9-10", "11-12", "13+"]


def fit_and_score(fit_half, held_out):
    add_track_barrier(fit_half, [fit_half, held_out])
    add_closing_merit([fit_half, held_out], fit_half["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
    for f in (fit_half, held_out):
        apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
        apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
        f["wprp_proj"] = f["_base"].to_numpy() + wpr._cap_adj_sum(
            f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
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
        print("Cache is stale (form history changed since it was built) - rebuilding.")

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

    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    print(f"Cached to {CACHE_PATH} for reuse by future runs (until wpr_form_history.csv.gz changes).")
    return full


def run():
    full = build_full()
    print(f"\nScoped rows: {len(full):,}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    print(f"\nFitting on H1, scoring held-out H2 (beta fixed at {FIXED_BETA})...")
    h2_scored = add_model_prob(fit_and_score(h1.copy(), h2.copy()), FIXED_BETA)
    print(f"Fitting on H2, scoring held-out H1 (beta fixed at {FIXED_BETA})...")
    h1_scored = add_model_prob(fit_and_score(h2.copy(), h1.copy()), FIXED_BETA)
    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    pooled["field_size"] = pd.to_numeric(pooled["field_size"], errors="coerce")
    print(f"\nPooled leak-free held-out set: {len(pooled):,} runners")

    top_idx = pooled.groupby("race_id")["wprp_proj"].idxmax()
    tops = pooled.loc[top_idx].copy()

    print(f"\n{'='*78}\nField size: >=50% implied-prob group vs everyone else "
          f"(each race's own top-rated runner only)\n{'='*78}")
    high = tops[tops["model_prob"] >= 0.5]
    rest = tops[tops["model_prob"] < 0.5]
    print(f"  >=50% implied group (n={len(high):,}): avg field_size={high['field_size'].mean():.2f}, "
          f"median={high['field_size'].median():.1f}")
    print(f"  <50% implied group  (n={len(rest):,}): avg field_size={rest['field_size'].mean():.2f}, "
          f"median={rest['field_size'].median():.1f}")

    print(f"\n{'='*78}\nWithin the >=50% implied group: calibration BY field-size bucket\n{'='*78}")
    high = high.copy()
    high["fs_bucket"] = pd.cut(high["field_size"], bins=FIELD_SIZE_BUCKETS, labels=FIELD_SIZE_LABELS)
    for b, g in high.groupby("fs_bucket", observed=True):
        if len(g) < 15:
            print(f"  field size {b}: n={len(g)} (too small, skipped)")
            continue
        actual, implied = g["won"].mean(), g["model_prob"].mean()
        print(f"  field size {b:>5}: n={len(g):4,d}  avg model_prob={implied*100:5.1f}%  "
              f"actual win rate={actual*100:5.1f}%  gap={((actual-implied)*100):+5.1f}pp")

    print(f"\n{'='*78}\nAcross the WHOLE top-rated population: calibration BY field-size bucket\n"
          f"(does the gap concentrate in small fields regardless of implied prob level?)\n{'='*78}")
    tops = tops.copy()
    tops["fs_bucket"] = pd.cut(tops["field_size"], bins=FIELD_SIZE_BUCKETS, labels=FIELD_SIZE_LABELS)
    for b, g in tops.groupby("fs_bucket", observed=True):
        if len(g) < 15:
            print(f"  field size {b}: n={len(g)} (too small, skipped)")
            continue
        actual, implied = g["won"].mean(), g["model_prob"].mean()
        print(f"  field size {b:>5}: n={len(g):4,d}  avg model_prob={implied*100:5.1f}%  "
              f"actual win rate={actual*100:5.1f}%  gap={((actual-implied)*100):+5.1f}pp")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
