"""
wpr_adj_term_ablation_and_stability.py - answers the user's "I don't
trust the current additive model with adjustments (they're too many
and too volatile)" concern (see chat, Sep 2026) with data, in two parts:

1. LEAVE-ONE-TERM-OUT MAE ABLATION: for each ADJ_TERM, scores the full
   additive model's held-out MAE and a variant with that ONE term
   zeroed out (every other term unchanged) - leak-free bidirectional
   H1/H2 split, population terms refit on the fit-half only, scored on
   the held-out half. A term whose removal does not hurt (or improves)
   held-out MAE is a candidate for cutting; a term whose removal
   clearly hurts is earning its keep.

   NOTE (Sep 2026, user's explicit call): this used to be a ROI/edge
   ablation via the WPR-price softmax method, matching how the joint-
   training rejection and the base-anchor MAE finding were both gated.
   Dropped back to plain MAE here after the base-anchor ROI backtest's
   fitted beta was found pinned at the floor of its grid in every fold
   - a signature of a genuinely weak, not-yet-trustworthy price/edge
   translation. Gating a model-architecture question (which ADJ_TERMS
   earn their keep) through a pricing method that is itself unvalidated
   risks exactly the "these numbers feel wrong" reaction the ROI
   backtest got. ROI/betting-strategy validation is being deliberately
   deferred to its own dedicated piece of work, done properly, once the
   additive architecture itself is settled - not re-litigated per
   candidate change in the meantime. MAE is a direct, uncontroversial
   measure of prediction accuracy that does not depend on that pricing
   layer at all.

2. RETRAIN-STABILITY CHECK (unchanged - never depended on ROI/pricing):
   for each of the four TRAINED-MODEL terms (track_barrier, closing_
   merit, trainer_merit, jockey_merit), fits the term twice,
   independently, on H1 and on H2, then scores the SAME full population
   with BOTH fits and compares the two outputs directly (correlation,
   mean absolute difference, spread) - not an accuracy check, a direct
   measure of how much a term's value for the identical horse/race
   would have come out differently if fit on a different slice of
   history. High divergence here IS the "volatile" the user is worried
   about, made concrete instead of assumed.

SCOPE: pace_shape is excluded from both parts (fixed at 0.0 everywhere,
consistently across every variant so it does not distort the
comparison) - same reason scratch_joint_model_kfold_eval.py and
scratch_joint_model_roi_eval.py both exclude it: _fit_pace_shape_model's
leak-safe window is hardcoded to the global max date, not fold-aware,
so a fold-based refit of it would not be genuinely leak-free. The six
own-history terms (own_distance, own_going, own_first_up, own_second_up,
own_trend, own_long_spell) need no refitting (they are pure per-horse
lookups, already correctly computed by build_training_frame) and so are
not part of the stability check (nothing to refit) - they ARE part of
the ablation (each can still be zeroed out and MAE compared).

Does NOT modify wpr_projection.py, does NOT touch wpr_models/*.joblib
or config.json. Read-only, safe to run repeatedly.

NO EM DASHES policy: hyphens only in this file.
"""
import pickle
from pathlib import Path

import numpy as np
import pandas as pd

import wpr_projection as wp
from wpr_base_anchor_fullmodel_roi_backtest import (
    _track_barrier_batch, _merit_batch, _closing_merit_batch,
)

FORM_CSV = "wpr_form_history.csv.gz"

TRAINED_TERMS = ["track_barrier", "closing_merit", "trainer_merit", "jockey_merit"]
OWN_HISTORY_TERMS = ["own_distance", "own_going", "own_first_up", "own_second_up",
                      "own_trend", "own_long_spell"]
ABLATION_TERMS = TRAINED_TERMS + OWN_HISTORY_TERMS  # pace_shape excluded, see docstring

_CACHE = Path("/tmp/claude-0/-home-user-TopRate/95a262de-71bd-5daf-b05e-b7e3031f09dd/scratchpad/adj_term_ablation_D_cache.pkl")


def _load_D():
    if _CACHE.exists():
        print(f"Loading cached prepped D from {_CACHE} (skipping rebuild)...")
        with open(_CACHE, "rb") as f:
            D = pickle.load(f)
        # Older cache generations (from the ROI-ablation version of this
        # script) may still carry sp/won/price columns - harmless if
        # present, not required now that ablation is MAE-based.
        return D

    print("Building training frame (n_jobs=-1, parallel) ...")
    D = wp.build_training_frame(FORM_CSV, n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"{len(D):,} training rows")

    # trainer_win_pct_365d/jockey_win_pct_90d are NOT part of build_training_
    # frame()'s own output (confirmed in wp._load_trainer_jockey_by_horse_date's
    # own docstring: only ever captured in toprate_runners.csv at daily-fetch
    # time, never in the form-history archive) - fit_trained_terms's trainer_
    # merit/jockey_merit fitting needs them. Missing here in every earlier
    # version of this script (a real bug, never caught because the script was
    # never actually run until now) - same merge pattern scratch_joint_model_
    # roi_eval.py already uses.
    print("Merging trainer/jockey trailing win-rate from toprate_runners.csv...")
    _name_map, _tj_lookup = wp._load_trainer_jockey_by_horse_date(FORM_CSV)
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    if "going" in D.columns:
        g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} rows, {len(D):,} remain")

    D["_base"] = wp._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wp._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]) \
        .fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()

    med = D[wp.FEATURES].median()
    D[wp.FEATURES] = D[wp.FEATURES].fillna(med)

    # pace_shape excluded (see module docstring) - fixed at 0.0 everywhere,
    # consistently, so it cancels out of every comparison below.
    D["pace_shape"] = 0.0

    print(f"Caching prepped D to {_CACHE} ...")
    with open(_CACHE, "wb") as f:
        pickle.dump(D, f)
    return D


def _closing_raw_resid_one(pairs, pace_baseline_lookup):
    vals = []
    for sect, bucket in pairs:
        exp = pace_baseline_lookup.get(bucket)
        if exp is not None and sect is not None and sect == sect:
            vals.append(float(sect) - float(exp))
    return (float(np.mean(vals)), float(len(vals))) if vals else (np.nan, 0.0)


def fit_trained_terms(fit_half, apply_to):
    """Fits the four trained-model population terms on fit_half ONLY,
    applies to every frame in apply_to (in place). Returns the four
    fitted models/lookups so the stability check can re-apply them to a
    DIFFERENT population later."""
    # NOTE: fit_half must NOT be re-copied/rebound here - the caller
    # constructs apply_to as [fit_half, held_out] using this exact
    # object, so setting track_code via the apply_to loop below only
    # reaches the SAME fit_half later used for track_barrier's own
    # _fit_simple_adj_model call if the reference is preserved. An
    # earlier `fit_half = fit_half.copy()` here silently broke that
    # aliasing (a real bug, only surfaced once this script was actually
    # run end to end for the first time) - track_barrier's fit crashed
    # with KeyError: ['track_code'] because the rebound local copy never
    # got the column the apply_to loop set on the ORIGINAL object.
    track_categories = sorted(fit_half["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    trainer_merit_trn = wp._fit_coverage_aware_trn(fit_half, ["trainer_win_pct_365d"])
    trainer_merit_model = wp._fit_simple_adj_model(trainer_merit_trn, wp._TRAINER_MERIT_FEATURES, "trainer_merit")
    jockey_merit_trn = wp._fit_coverage_aware_trn(fit_half, ["jockey_win_pct_90d"])
    jockey_merit_model = wp._fit_simple_adj_model(jockey_merit_trn, wp._JOCKEY_MERIT_FEATURES, "jockey_merit")
    for _f in apply_to:
        _f.loc[:, "track_code"] = _f["track"].map(track_code_map).fillna(-1).astype(int)
    track_barrier_model = wp._fit_simple_adj_model(fit_half, wp._TRACK_BARRIER_FEATURES, "track_barrier")
    pace_baseline_lookup = wp._fit_pace_baseline(FORM_CSV, fit_half["date"].max())
    for _f in apply_to:
        _computed = [_closing_raw_resid_one(p, pace_baseline_lookup) for p in _f["closing_pairs"]]
        _f.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        _f.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
    closing_merit_model = wp._fit_simple_adj_model(fit_half, wp._CLOSING_MERIT_FEATURES, "closing_merit")

    # Batch (vectorized) equivalents of the live per-row term functions -
    # see wpr_base_anchor_fullmodel_roi_backtest.py's own docstring for
    # these: reusing the per-row originals in a Python loop over a
    # backtest's hundreds of thousands of rows means that many individual
    # model.predict() calls, confirmed directly to stall a fold for 50+
    # minutes with no progress.
    for _f in apply_to:
        _f.loc[:, "track_barrier"] = _track_barrier_batch(_f, track_code_map, track_barrier_model)
        _f.loc[:, "trainer_merit"] = _merit_batch(
            _f["trainer_win_pct_365d"], _f["field_size"], trainer_merit_model, wp._TRAINER_MERIT_FEATURES)
        _f.loc[:, "jockey_merit"] = _merit_batch(
            _f["jockey_win_pct_90d"], _f["field_size"], jockey_merit_model, wp._JOCKEY_MERIT_FEATURES)
        _f.loc[:, "closing_merit"] = _closing_merit_batch(_f, closing_merit_model)
        for _term in TRAINED_TERMS:
            _f[_term] = _f[_term] - _f.groupby("race_id")[_term].transform("mean")
        _f[wp.ADJ_TERMS] = _f[wp.ADJ_TERMS].fillna(0.0)

    return {
        "track_code_map": track_code_map,
        "track_barrier_model": track_barrier_model,
        "trainer_merit_model": trainer_merit_model,
        "jockey_merit_model": jockey_merit_model,
        "closing_merit_model": closing_merit_model,
        "pace_baseline_lookup": pace_baseline_lookup,
    }


def _additive_predict(frame, drop_term=None):
    terms = [t for t in wp.ADJ_TERMS if t != drop_term] if drop_term else list(wp.ADJ_TERMS)
    return frame["_base"].to_numpy() + wp._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def fit_and_score(fit_half, held_out):
    """Fits the trained terms on fit_half, applies to both frames, then
    computes held-out MAE for the FULL additive model and one LEAVE-
    ONE-TERM-OUT variant per ADJ_TERM in ABLATION_TERMS - all scored on
    held_out, all using ONLY fit_half's fits. Returns a {variant: (mae,
    n)} dict plus the fitted models (for the stability check)."""
    fit_half = fit_half.copy()
    held_out = held_out.copy()
    models = fit_trained_terms(fit_half, [fit_half, held_out])

    variants = ["full"] + [f"minus_{t}" for t in ABLATION_TERMS]
    maes = {}
    for v in variants:
        drop = None if v == "full" else v[len("minus_"):]
        pred = _additive_predict(held_out, drop_term=drop)
        mae = float(np.abs(held_out["target"].to_numpy() - pred).mean())
        maes[v] = (mae, len(held_out))
    return maes, models


def run_ablation(D):
    # Split by the COVERED subset's own median date, not the whole
    # dataset's - trainer_win_pct_365d/jockey_win_pct_90d only exist in
    # toprate_runners.csv's recent daily-snapshot window (~20% overall
    # coverage, per _fit_coverage_aware_trn's own docstring), which sits
    # almost entirely in the recent tail of this multi-year archive. A
    # plain whole-dataset median split can put that ENTIRE window inside
    # one half, leaving the other with zero rows to fit trainer_merit/
    # jockey_merit from at all (confirmed directly: first real run of
    # this script hit exactly that - "0 covered rows, skipping fit").
    # Splitting on the covered subset's own median instead guarantees
    # real coverage on both sides; track_barrier/closing_merit (covered
    # across the whole archive) still get plenty of data in both halves
    # regardless of exactly where this cutoff falls.
    covered = D[D["trainer_win_pct_365d"].notna()]
    mid = covered["date"].quantile(0.5) if len(covered) else D["date"].quantile(0.5)
    h1, h2 = D[D["date"] < mid].copy(), D[D["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()}) "
          f"[split on trainer/jockey-merit coverage's own median date]")

    print("\nFitting on H1, scoring held-out H2...")
    maes_h2, models_h1 = fit_and_score(h1, h2)
    print("\nFitting on H2, scoring held-out H1...")
    maes_h1, models_h2 = fit_and_score(h2, h1)

    print(f"\n{'='*70}\nLEAVE-ONE-TERM-OUT MAE ABLATION (bidirectional held-out, pooled)\n{'='*70}")
    variants = list(maes_h2.keys())
    full_mae = None
    print(f"{'variant':<20}{'MAE (H2 held-out)':>20}{'MAE (H1 held-out)':>20}{'pooled avg MAE':>18}{'delta vs full':>16}")
    for v in variants:
        m2, n2 = maes_h2[v]
        m1, n1 = maes_h1[v]
        pooled_avg = (m2 * n2 + m1 * n1) / (n2 + n1)
        if v == "full":
            full_mae = pooled_avg
        delta = pooled_avg - full_mae if full_mae is not None else float("nan")
        flag = ""
        if v != "full":
            flag = "  <-- removing HURTS (higher MAE)" if delta > 0.01 else (
                   "  <-- removing HELPS or neutral" if delta < -0.01 else "  <-- ~neutral")
        print(f"{v:<20}{m2:>20.4f}{m1:>20.4f}{pooled_avg:>18.4f}{delta:>+16.4f}{flag}")

    print("\nReading this: 'full' is the current shipped-equivalent MAE (both terms in).")
    print("For each 'minus_X' row, a POSITIVE delta means removing that term makes MAE")
    print("WORSE (the term is earning its keep); a delta near zero or negative means the")
    print("term isn't helping (or is actively hurting) accuracy - a candidate to cut.")

    return h1, h2, models_h1, models_h2


def run_stability(h1, h2, models_h1, models_h2):
    """Applies the H1-fit and H2-fit trained-term models to the SAME
    fixed population (the pooled full dataset) and compares the two
    independently-fit outputs directly - no target/accuracy involved,
    purely "how much does this term's value for the same row shift
    depending on which half of history it was fit on"."""
    print(f"\n{'='*70}\nRETRAIN-STABILITY CHECK (same rows, scored by two independent fits)\n{'='*70}")
    pooled = pd.concat([h1, h2], ignore_index=True).copy()

    def _apply(models, frame):
        frame = frame.copy()
        tcm = models["track_code_map"]
        frame.loc[:, "track_code"] = frame["track"].map(tcm).fillna(-1).astype(int)
        frame.loc[:, "track_barrier"] = _track_barrier_batch(frame, tcm, models["track_barrier_model"])
        frame.loc[:, "trainer_merit"] = _merit_batch(
            frame["trainer_win_pct_365d"], frame["field_size"],
            models["trainer_merit_model"], wp._TRAINER_MERIT_FEATURES)
        frame.loc[:, "jockey_merit"] = _merit_batch(
            frame["jockey_win_pct_90d"], frame["field_size"],
            models["jockey_merit_model"], wp._JOCKEY_MERIT_FEATURES)
        _computed = [_closing_raw_resid_one(p, models["pace_baseline_lookup"]) for p in frame["closing_pairs"]]
        frame.loc[:, "closing_raw_resid"] = [c[0] for c in _computed]
        frame.loc[:, "closing_n_pairs"] = [c[1] for c in _computed]
        frame.loc[:, "closing_merit"] = _closing_merit_batch(frame, models["closing_merit_model"])
        for _term in TRAINED_TERMS:
            frame[_term] = frame[_term] - frame.groupby("race_id")[_term].transform("mean")
        return frame

    scored_h1fit = _apply(models_h1, pooled)
    scored_h2fit = _apply(models_h2, pooled)

    print(f"\n{'n same-row comparisons':>28}: {len(pooled):,}")
    print(f"{'term':<16}{'corr':>10}{'mean|diff|':>14}{'std(diff)':>12}{'p90|diff|':>12}")
    for t in TRAINED_TERMS:
        a = scored_h1fit[t].to_numpy()
        b = scored_h2fit[t].to_numpy()
        mask = ~(np.isnan(a) | np.isnan(b))
        diff = a[mask] - b[mask]
        corr = np.corrcoef(a[mask], b[mask])[0, 1] if mask.sum() > 1 else float("nan")
        print(f"{t:<16}{corr:>10.3f}{np.mean(np.abs(diff)):>14.3f}{np.std(diff):>12.3f}{np.percentile(np.abs(diff),90):>12.3f}")

    print("\nReading this: corr close to 1.0 and small mean|diff| = stable (this term's ")
    print("value for a given horse/race barely depends on which half of history fit it).")
    print("Low corr or large mean|diff| relative to the term's own typical magnitude =")
    print("volatile - this term would give a meaningfully different number to the user")
    print("depending on the accident of which retrain window it was fit on.")


def run():
    D = _load_D()
    h1, h2, models_h1, models_h2 = run_ablation(D)
    run_stability(h1, h2, models_h1, models_h2)
    print("\nSame multiple-comparisons caveat as every backtest in this codebase:")
    print("treat this as a hypothesis, not a result to ship blind.")
    print("\nDone.")


if __name__ == "__main__":
    run()
