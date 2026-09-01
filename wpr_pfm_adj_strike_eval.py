"""
wpr_pfm_adj_strike_eval.py - tests pfm_score as a THIRD population-level
ADJ_TERM candidate (pfm_merit), on top of the now-shipped trainer_merit/
jockey_merit (see wpr_trainer_jockey_adj_strike_eval.py, PR #147). Same
question, same bar: does adding it as an adjustment to WPR ITSELF improve
held-out top-1 strike rate in BOTH directions of a chronological split,
over a baseline that already includes trainer_merit/jockey_merit.

WHY THIS IS A GENUINE QUESTION, NOT AN ASSUMED YES
  pfm_score is a real mixed case per calibrate_edge_score.py's own
  ablation history: it measurably helps the SEPARATE edge-score blend's
  ranking (AUC), but it is also the most market-correlated of the edge
  features (~71% correlated with market price - mostly a "market echo"
  rather than independent signal, unlike trainer/jockey which had LOWER
  market correlation - see chat, Sep 2026 standalone-AUC/market-corr
  review). Whether that translates into an adoptable WPR-itself
  adjustment (vs. only being useful in a separate market-comparison
  blend) is exactly what this script checks, same as the trainer/jockey
  case before it.

METHODOLOGY: same population-fitted decile-bucket lookup as
trainer_merit/jockey_merit (shrunk residual = target - career_avg per
decile, K=300 shrinkage, fit on one chronological half, applied to both).
Baseline is the CURRENT shipped model (base + all 10 production
ADJ_TERMS, trainer_merit/jockey_merit refit per split same as the
original eval - not read from config.json, to avoid any overlap-with-
test-window leakage). Candidate adds pfm_merit on top. Scoped to rows
where pfm_score is present (~34% coverage per calibrate_edge_score.py) -
trainer/jockey merit degrade gracefully to 0.0 where THEIR coverage is
missing, matching real production behaviour for this subset.

USAGE
  python wpr_pfm_adj_strike_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date
from wpr_trainer_jockey_adj_strike_eval import (
    FORM_CSV, merge_trainer_jockey_by_horse_date, add_closing_merit,
    fit_bucket_lookup, apply_bucket, proj_of, report,
)


def merge_pfm_by_horse_date(D, runners_csv="toprate_runners.csv"):
    tr = pd.read_csv(runners_csv, low_memory=False, usecols=["horse", "date", "pfm_score"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr = tr.dropna(subset=["date"])
    tr = tr.drop_duplicates(subset=["horse", "date"], keep=False)
    return D.merge(tr, on=["horse", "date"], how="inner")


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])

    print("\nMerging race result, trainer/jockey win-rate, and pfm_score "
          "from toprate_runners.csv by (horse, date)...")
    full = merge_won_by_horse_date(full)
    full = merge_trainer_jockey_by_horse_date(full)
    full = merge_pfm_by_horse_date(full)

    full = add_base(full)
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance", "pfm_score"])
    print(f"\nScoped rows (pfm_score covered): {len(full):,}")
    print(f"  trainer_win_pct_365d coverage within this subset: {full['trainer_win_pct_365d'].notna().mean()*100:.1f}%")
    print(f"  jockey_win_pct_90d coverage within this subset: {full['jockey_win_pct_90d'].notna().mean()*100:.1f}%")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    def build_variant(fit_half, h1f, h2f, fit_cutoff):
        add_track_barrier(fit_half, [h1f, h2f])
        add_closing_merit([h1f, h2f], fit_cutoff)
        edges_t, lookup_t = fit_bucket_lookup(fit_half, "trainer_win_pct_365d")
        edges_j, lookup_j = fit_bucket_lookup(fit_half, "jockey_win_pct_90d")
        edges_p, lookup_p = fit_bucket_lookup(fit_half, "pfm_score")
        print(f"  pfm_merit lookup (by decile): {lookup_p}")
        for f in (h1f, h2f):
            apply_bucket(f, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
            apply_bucket(f, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
            apply_bucket(f, "pfm_score", edges_p, lookup_p, "pfm_merit")

    print("\nFitting H1-fit/H2-validate direction...")
    h1_d1, h2_d1 = h1.copy(), h2.copy()
    build_variant(h1_d1, h1_d1, h2_d1, h1["date"].max())

    print("\nFitting H2-fit/H1-validate direction...")
    h1_d2, h2_d2 = h1.copy(), h2.copy()
    build_variant(h2_d2, h1_d2, h2_d2, h2["date"].max())

    for d in (h1_d1, h2_d1, h1_d2, h2_d2):
        d["proj_base"] = proj_of(d, [])
        d["proj_pfm"] = proj_of(d, ["pfm_merit"])

    report(h1_d1, h2_d1, h1_d2, h2_d2, "proj_pfm", "pfm_merit (on top of current trainer/jockey model)")


if __name__ == "__main__":
    run()
