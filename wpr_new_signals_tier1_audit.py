"""
wpr_new_signals_tier1_audit.py - the FIRST pass at the user's original
signal wishlist (see chat, Sep 2026 - the very start of this session,
before every later redirect: age/sex, jockey/trainer change, jockey's
record at this track, jockey-horse combo, trainer's FU/2U pattern,
stable-wide form, sire/dam stats, track shape, travel effect, etc).
None of these were ever implemented or tested - this checks the
cheapest, highest-confidence subset (Tier 1) against the SAME 10-year
race_results depth used for the base-anchor and ADJ_TERM work, at both
a POPULATION level (does this category show a real, era-stable
systematic bias in the current model's residual) and a HORSE level
(concrete before/after examples, not just an aggregate number).

TIER 1 (this script): jockey change, trainer change (both own-history,
leak-free by construction - only ever compares to the PRIOR run's
jockey/trainer, never today's), horse age, horse sex, race weight basis
(SW/WFA/HCP/CW/QLTY - already backfilled via weight_restriction).

METHOD: rather than building a full candidate ADJ_TERM (shrunk lookup,
leave-one-era-out MAE ablation) for every one of these up front, this
is a cheaper first-pass RESIDUAL AUDIT - does the CURRENT model
(base_ewm5 + track_barrier + closing_merit + own-history terms, the
same scope already validated as testable this deep in wpr_base_anchor_
fullmodel_roi_backtest.py; trainer_merit/jockey_merit/pace_shape stay
excluded, see that script's own docstring for why) show a real,
era-stable, systematic bias when grouped by each candidate category. A
category with a real bias is evidence worth building a proper leak-free
ADJ_TERM for; a flat residual across categories means the signal isn't
adding much beyond what the model already captures.

Fitting (track_barrier/closing_merit) is done per era-fold, leave-one-
era-out, exactly like wpr_base_anchor_fullmodel_roi_backtest.py - the
residual reported for a given era's rows always comes from a fit that
never saw that era.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import (
    load_combined, assign_era, ERA_BOUNDS, D_CACHE,
)
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FULL_TERMS


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def _t_stat(x):
    x = x[~np.isnan(x)]
    if len(x) < 5:
        return float("nan")
    se = x.std(ddof=1) / np.sqrt(len(x))
    return x.mean() / se if se > 0 else float("nan")


def report_bias(pooled, group_col, label, min_n=200):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    print(f"{'group':<20}{'n':>10}{'mean resid':>14}{'std resid':>12}{'t-stat':>10}   overall + by era")
    for val, g in pooled.groupby(group_col, dropna=False):
        if len(g) < min_n:
            continue
        resid = g["resid"].to_numpy()
        t = _t_stat(resid)
        flag = "  ** SIGNIFICANT **" if abs(t) >= 1.96 else ""
        per_era = []
        for era in [e[0] for e in ERA_BOUNDS]:
            eg = g[g["_era"] == era]
            if len(eg) >= 50:
                per_era.append(f"{era}={eg['resid'].mean():+.2f}")
        print(f"{str(val):<20}{len(g):>10,}{resid.mean():>+14.3f}{resid.std():>12.3f}{t:>+10.2f}{flag}")
        print(f"    by era: {', '.join(per_era)}")


def horse_level_examples(pooled, change_col, n_examples=6):
    """Concrete before/after: a handful of individual horses whose
    change_col flips from 0 to 1 (or vice versa) across consecutive
    runs, showing target/pred/resid on each side - not just an
    aggregate number."""
    print(f"\n--- Horse-level examples: {change_col} ---")
    flips = pooled[pooled[change_col] == 1].sort_values("date")
    if len(flips) == 0:
        print("  (no rows with this flag set)")
        return
    sample_horses = flips["horse_id"].drop_duplicates().sample(
        min(n_examples, flips["horse_id"].nunique()), random_state=42)
    for hid in sample_horses:
        hist = pooled[pooled["horse_id"] == hid].sort_values("date")
        row = hist[hist[change_col] == 1].iloc[0]
        prior = hist[hist["date"] < row["date"]]
        if len(prior) == 0:
            continue
        prior_row = prior.iloc[-1]
        print(f"  horse_id={hid}: prior run {prior_row['date'].date()} "
              f"target={prior_row['target']:.1f} pred={prior_row['pred']:.1f} "
              f"resid={prior_row['resid']:+.1f}  ->  {change_col} run "
              f"{row['date'].date()} target={row['target']:.1f} pred={row['pred']:.1f} "
              f"resid={row['resid']:+.1f}")


def run():
    combined = load_combined()
    D = load_D()

    print("\nMerging jockey/trainer/age/sex/weight_restriction from race_results...")
    side_cols = ["horse_id", "date", "race_id", "jockey", "trainer",
                 "horse_age", "horse_sex", "weight_restriction"]
    side = combined[side_cols].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side = side.dropna(subset=["date"]).drop_duplicates(
        subset=["horse_id", "date", "race_id"], keep="first")

    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side, on=key_cols, how="left")
    assert len(D) == before, "signal merge changed row count"

    print("\nComputing jockey_change/trainer_change (own-history, prior-run-only, leak-free)...")
    D = D.sort_values(["horse_id", "date"])
    D["prior_jockey"] = D.groupby("horse_id")["jockey"].shift(1)
    D["prior_trainer"] = D.groupby("horse_id")["trainer"].shift(1)
    D["jockey_change"] = ((D["jockey"] != D["prior_jockey"]) & D["prior_jockey"].notna()).astype(int)
    D["trainer_change"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(int)
    print(f"  jockey_change rate: {D['jockey_change'].mean()*100:.1f}%  "
          f"trainer_change rate: {D['trainer_change'].mean()*100:.1f}%")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    print("\nFitting the current-scope model (base_ewm5 + track_barrier + closing_merit + "
          "own-history terms) leave-one-era-out to get an honest held-out residual per row...")
    pooled_parts = []
    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        held_out["_base"] = base_with_anchor(held_out, "ewm5")
        held_out["pred"] = held_out["_base"].to_numpy() + wp._cap_adj_sum(
            held_out[FULL_TERMS].to_numpy()).sum(axis=1)
        held_out["resid"] = held_out["target"] - held_out["pred"]
        pooled_parts.append(held_out)
        print(f"  era {era}: {len(held_out):,} held-out rows scored")

    pooled = pd.concat(pooled_parts, ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} rows, "
          f"overall mean residual {pooled['resid'].mean():+.3f} "
          f"(std {pooled['resid'].std():.3f})")

    report_bias(pooled, "jockey_change", "JOCKEY CHANGE (own-history: different jockey than last run)")
    report_bias(pooled, "trainer_change", "TRAINER CHANGE (own-history: different trainer than last run)")
    horse_level_examples(pooled, "jockey_change")
    horse_level_examples(pooled, "trainer_change")

    pooled["age_band"] = pd.cut(pd.to_numeric(pooled["horse_age"], errors="coerce"),
                                 bins=[0, 3, 4, 5, 6, 7, 100],
                                 labels=["<=3", "4", "5", "6", "7", "8+"])
    report_bias(pooled, "age_band", "HORSE AGE (banded)")
    report_bias(pooled, "horse_sex", "HORSE SEX")
    report_bias(pooled, "weight_restriction", "RACE WEIGHT BASIS (SW/WFA/HCP/CW/QLTY/SWP)")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("a real, era-stable bias here is a green light to build a proper leak-free")
    print("ADJ_TERM candidate for it, not a result to ship blind on its own.")
    print("\nDone.")


if __name__ == "__main__":
    run()
