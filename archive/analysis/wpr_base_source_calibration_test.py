"""
wpr_base_source_calibration_test.py - is the extreme-overconfidence
bucket (wpr_favourite_calibration_curve.py: runners rated >=50% to win
actually won 33.4% of the time, n=908) a BASE problem or an ADJUSTMENT
problem - and if base, is it specifically wpr_nett-driven dominance that's
unreliable, or ewm3-driven dominance?

WHY: field size didn't explain it (wpr_field_size_calibration_test.py
found the opposite of the hypothesised direction - miscalibration got
WORSE in bigger fields, not better). The user's own suspicion from
earlier in this session ("if anything the base calculation should be
adjusted by changing the 50/50 ratio of wpr_nett & ewm3") points at a
more specific, testable mechanism: since ADJ_TERMS can never contribute
more than ~+/-1.1 points combined (see wpr_adj_cap_favourite_test.py),
any edge large enough to push a runner's implied probability above 50%
is ALMOST ENTIRELY a base-driven gap by construction - this script
confirms that directly, then asks the sharper question: within that
base-driven edge, does it matter whether the dominance comes from a high
wpr_nett (TopRate's own rating) vs a high ewm3 (this horse's own recent-
run average)? If one source is systematically less reliable at the
extreme tail than the other, that's a concrete, actionable lever on
_BASE_BLEND_ALPHA - a much more surgical answer than "try different
alpha values and see".

METHOD: same leak-free fixed-beta=0.15 setup as the other calibration
scripts in this series, loaded from the shared disk cache (see
wpr_day_by_day_fixed_beta.py's build_full() - populated by the last run
that didn't find one).

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
    print(f"wpr_nett coverage: {full['wpr_nett'].notna().mean()*100:.1f}%, "
          f"ewm3 coverage: {full['ewm3'].notna().mean()*100:.1f}%")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()

    print(f"\nFitting on H1, scoring held-out H2 (beta fixed at {FIXED_BETA})...")
    h2_scored = add_model_prob(fit_and_score(h1.copy(), h2.copy()), FIXED_BETA)
    print(f"Fitting on H2, scoring held-out H1 (beta fixed at {FIXED_BETA})...")
    h1_scored = add_model_prob(fit_and_score(h2.copy(), h1.copy()), FIXED_BETA)
    pooled = pd.concat([h1_scored, h2_scored], ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} runners")

    top_idx = pooled.groupby("race_id")["wprp_proj"].idxmax()
    tops = pooled.loc[top_idx].copy()

    # Field-average _base and adj_total EXCLUDING the top pick itself, per race.
    race_base_sum = pooled.groupby("race_id")["_base"].transform("sum")
    race_adj_sum = pooled.groupby("race_id")["adj_total"].transform("sum")
    race_n = pooled.groupby("race_id")["_base"].transform("size")
    pooled["field_avg_base_excl"] = (race_base_sum - pooled["_base"]) / (race_n - 1)
    pooled["field_avg_adj_excl"] = (race_adj_sum - pooled["adj_total"]) / (race_n - 1)
    tops = pooled.loc[top_idx].copy()
    tops["base_edge"] = tops["_base"] - tops["field_avg_base_excl"]
    tops["adj_edge"] = tops["adj_total"] - tops["field_avg_adj_excl"]

    print(f"\n{'='*78}\nHow much of the top pick's edge over the field is base vs adjustment?\n{'='*78}")
    for label, sub in [("Whole top-rated population", tops), ("Just the >=50% implied group", tops[tops["model_prob"] >= 0.5])]:
        base_share = (sub["base_edge"] / (sub["base_edge"] + sub["adj_edge"])).clip(-5, 5)
        print(f"  {label} (n={len(sub):,}): avg base_edge={sub['base_edge'].mean():.2f} pts, "
              f"avg adj_edge={sub['adj_edge'].mean():.2f} pts, "
              f"median base share of total edge={base_share.median()*100:.1f}%")

    print(f"\n{'='*78}\nWithin base-driven dominance: does wpr_nett vs ewm3 source matter?\n"
          f"(nett_minus_ewm3 = TopRate's own rating minus this horse's own recent-form avg -\n"
          f" positive means TopRate rates it higher than its own form does, and vice versa)\n{'='*78}")
    both = tops.dropna(subset=["wpr_nett", "ewm3"]).copy()
    both["nett_minus_ewm3"] = both["wpr_nett"] - both["ewm3"]
    for label, sub in [("Whole top-rated population", both), ("Just the >=50% implied group", both[both["model_prob"] >= 0.5])]:
        print(f"\n  --- {label} (n={len(sub):,}) ---")
        buckets = pd.qcut(sub["nett_minus_ewm3"], 4, duplicates="drop")
        for b, g in sub.groupby(buckets, observed=True):
            actual, implied = g["won"].mean(), g["model_prob"].mean()
            print(f"    nett-ewm3 {b}: n={len(g):4,d}  avg(nett-ewm3)={g['nett_minus_ewm3'].mean():+5.1f}  "
                  f"avg model_prob={implied*100:5.1f}%  actual win rate={actual*100:5.1f}%  "
                  f"gap={((actual-implied)*100):+5.1f}pp")

    print("\nSame multiple-comparisons caveat as the other bet-selection scripts: treat any")
    print("row here as a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
