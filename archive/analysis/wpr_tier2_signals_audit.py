"""
wpr_tier2_signals_audit.py - Tier 2 of the user's original signal
wishlist (see chat, Sep 2026 - the start of this session): jockey's
record at this specific track, and stable-wide current form (the
trainer's recent-window momentum, distinct from trainer_win_pct_365d's
longer trailing window). Same residual-audit-first approach as Tier 1
(wpr_new_signals_tier1_audit.py): does the CURRENT model's held-out
residual show a real, era-stable systematic bias when grouped by each
candidate, before committing to a full leak-free ADJ_TERM build.

JOCKEY-TRACK WIN RATE: for each (jockey, track) pair, an expanding,
LEAK-FREE win rate as of each race - only prior races at that exact
track by that exact jockey, shift(1) so the current row's own outcome
never leaks into its own rate. Genuinely different from jockey_merit
(trailing 90-day win rate, ANY track) - this isolates "is this jockey
specifically good at THIS track", not general current form.

STABLE-WIDE CURRENT FORM: a trainer's OWN recent-window (30-day)
rolling win rate across ALL its runners, expanding + shift(1), same
leak-free discipline. Distinct from trainer_win_pct_365d (a full-year
trailing window, already captured by trainer_merit) - this is meant to
catch a SHORT-TERM hot/cold stable streak trainer_merit's longer window
smooths away.

MODEL SCOPE: same testable-this-deep composition as every other 10-
year script (base_ewm5 + track_barrier + closing_merit + own-history +
the just-shipped trainer_change/pop_distance/pop_going) - trainer_
merit/jockey_merit/pace_shape stay excluded (recency-limited data /
fold-aware leak-safety, same reasons as always).

NO EM DASHES policy: hyphens only in this file.
"""
import pickle

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_calc_10yr_retest import load_combined, assign_era, ERA_BOUNDS, D_CACHE
from wpr_base_anchor_roi_backtest import base_with_anchor
from wpr_base_anchor_fullmodel_roi_backtest import fit_terms_on_fold, FITTED_TERMS, _merit_batch

OWN_HISTORY_KEEP = ["own_first_up", "own_second_up", "own_long_spell"]
NEW_TERMS = ["trainer_change", "pop_distance", "pop_going"]
FULL_TERMS = FITTED_TERMS + OWN_HISTORY_KEEP + NEW_TERMS

NEW_TERM_FEATURES = {
    "trainer_change": ("trainer_change_raw", wp._TRAINER_CHANGE_FEATURES),
    "pop_distance": ("dist_vs_last", wp._POP_DISTANCE_FEATURES),
    "pop_going": ("going_delta", wp._POP_GOING_FEATURES),
}


def load_D():
    print(f"Loading cached D from {D_CACHE} ...")
    with open(D_CACHE, "rb") as f:
        D = pickle.load(f)
    print(f"  {len(D):,} rows")
    return D


def fit_new_term(fit_half, apply_to, value_col, features, label):
    trn = fit_half.dropna(subset=[value_col, "target", "career_avg"])
    trn = trn.rename(columns={value_col: features[0]}) if value_col != features[0] else trn
    model = wp._fit_simple_adj_model(trn, features, label)
    for _f in apply_to:
        _f.loc[:, label] = _merit_batch(_f[value_col], _f["field_size"], model, features)
    return model


def additive_predict(frame):
    base = base_with_anchor(frame, "ewm5")
    return base.to_numpy() + wp._cap_adj_sum(frame[FULL_TERMS].to_numpy()).sum(axis=1)


def _t_stat(x):
    x = x[~np.isnan(x)]
    if len(x) < 5:
        return float("nan")
    se = x.std(ddof=1) / np.sqrt(len(x))
    return x.mean() / se if se > 0 else float("nan")


def report_bias(pooled, group_col, label, min_n=200, bands=None):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    print(f"{'group':<20}{'n':>10}{'mean resid':>14}{'std resid':>12}{'t-stat':>10}   by era")
    groups = bands if bands else sorted(pooled[group_col].dropna().unique())
    for val in groups:
        g = pooled[pooled[group_col] == val] if bands is None else pooled[pooled["_band"] == val]
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


def run():
    combined = load_combined()
    D = load_D()

    print("\nMerging jockey/trainer/track and computing won (positionFinish==1)...")
    side_cols = ["horse_id", "date", "race_id", "jockey", "trainer", "positionFinish"]
    side = combined[side_cols].copy()
    side["date"] = pd.to_datetime(side["date"], errors="coerce")
    side["race_id"] = side["race_id"].astype(str)
    side["won"] = (pd.to_numeric(side["positionFinish"], errors="coerce") == 1).astype(int)
    side = side.dropna(subset=["date"]).drop_duplicates(subset=["horse_id", "date", "race_id"], keep="first")

    D = D.copy()
    D["race_id"] = D["race_id"].astype(str)
    key_cols = ["horse_id", "date", "race_id"]
    before = len(D)
    D = D.merge(side[key_cols + ["jockey", "trainer", "won"]], on=key_cols, how="left")
    assert len(D) == before, "signal merge changed row count"
    D = D.sort_values(["horse_id", "date"])
    D["prior_trainer"] = D.groupby("horse_id")["trainer"].shift(1)
    D["trainer_change_raw"] = ((D["trainer"] != D["prior_trainer"]) & D["prior_trainer"].notna()).astype(float)

    print("\nBuilding leak-free jockey-track win rate (expanding, shift(1))...")
    # NOTE: jt is sorted into a DIFFERENT row order than D (grouped by
    # jockey+track for the expanding calc) - assigning back via .to_numpy()
    # would silently misalign every row to the wrong horse/race. .copy()
    # preserves D's original index labels through the sort/groupby
    # (groupby.transform always returns a result aligned to ITS OWN
    # caller's index, not reset), so a plain Series assignment (no
    # to_numpy()) lets pandas re-align by that shared index correctly.
    jt = D[["jockey", "track", "date", "won"]].copy().sort_values(["jockey", "track", "date"])
    jt["jt_wins"] = jt.groupby(["jockey", "track"])["won"].transform(lambda s: s.shift(1).expanding().sum())
    jt["jt_starts"] = jt.groupby(["jockey", "track"])["won"].transform(lambda s: s.shift(1).expanding().count())
    jt["jockey_track_win_pct"] = jt["jt_wins"] / jt["jt_starts"].replace(0, np.nan)
    D["jockey_track_win_pct"] = jt["jockey_track_win_pct"]
    D["jockey_track_starts"] = jt["jt_starts"]
    print(f"  coverage (>=5 prior starts at this track by this jockey): "
          f"{(D['jockey_track_starts'] >= 5).mean()*100:.1f}%")

    print("\nBuilding leak-free trainer stable-wide 30-day rolling win rate...")
    # set_index("date") below REPLACES the row-identity index with date
    # values (which repeat across many rows) - capture the original index
    # explicitly first so it can be restored before assigning back to D,
    # rather than relying on (broken) positional/date alignment.
    tr = D[["trainer", "date", "won"]].copy()
    tr["_orig_idx"] = tr.index
    tr = tr.sort_values(["trainer", "date"]).set_index("date")

    def _rolling_30d(g):
        g = g.sort_index()
        shifted = g["won"].shift(1)
        shifted.index = g.index
        return shifted.rolling("30D").mean()

    tr["stable_form_30d"] = tr.groupby("trainer", group_keys=False).apply(_rolling_30d)
    tr = tr.reset_index(drop=True).set_index("_orig_idx")
    D["stable_form_30d"] = tr["stable_form_30d"]
    print(f"  coverage: {D['stable_form_30d'].notna().mean()*100:.1f}%")

    D["_era"] = assign_era(D["date"])
    era_names = [e[0] for e in ERA_BOUNDS]
    print(f"\nEra row counts:\n{D['_era'].value_counts().reindex(era_names)}")

    print("\nFitting the current-scope model leave-one-era-out to get an honest "
          "held-out residual per row...")
    pooled_parts = []
    for era in era_names:
        fit_half = D[D["_era"] != era].copy()
        held_out = D[D["_era"] == era].copy()
        if len(held_out) < 200:
            continue
        fit_terms_on_fold(fit_half, [fit_half, held_out], "wpr_form_history.csv.gz")
        for new_term, (value_col, features) in NEW_TERM_FEATURES.items():
            fit_new_term(fit_half, [fit_half, held_out], value_col, features, new_term)
        for _f in (fit_half, held_out):
            for term in NEW_TERMS:
                _f[term] = _f[term] - _f.groupby("race_id")[term].transform("mean")
            _f[FULL_TERMS] = _f[FULL_TERMS].fillna(0.0)
        held_out["pred"] = additive_predict(held_out)
        held_out["resid"] = held_out["target"] - held_out["pred"]
        pooled_parts.append(held_out)
        print(f"  era {era}: {len(held_out):,} held-out rows scored")

    pooled = pd.concat(pooled_parts, ignore_index=True)
    print(f"\nPooled leak-free held-out set: {len(pooled):,} rows, "
          f"overall mean residual {pooled['resid'].mean():+.3f}")

    pooled["jt_band"] = pd.cut(
        pooled["jockey_track_win_pct"].where(pooled["jockey_track_starts"] >= 5),
        bins=[0, 0.05, 0.10, 0.15, 0.20, 1.0],
        labels=["0-5%", "5-10%", "10-15%", "15-20%", "20%+"])
    report_bias(pooled, "jt_band", "JOCKEY-TRACK WIN RATE (>=5 prior starts at this track by this jockey)")

    pooled["stable_band"] = pd.cut(
        pooled["stable_form_30d"],
        bins=[0, 0.05, 0.10, 0.15, 0.20, 1.0],
        labels=["0-5%", "5-10%", "10-15%", "15-20%", "20%+"])
    report_bias(pooled, "stable_band", "TRAINER STABLE-WIDE 30-DAY WIN RATE")

    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("a real, era-stable bias here is a green light to build a proper leak-free")
    print("ADJ_TERM candidate for it, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
