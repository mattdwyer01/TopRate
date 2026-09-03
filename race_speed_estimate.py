"""
race_speed_estimate.py
----------------------
Automated race-speed (early-tempo) estimate.

WHAT IT DOES
  For a race, estimates how it will be run early - a 0-1 score plus a
  Hot / Fast / Even / Slow label - using a TRAINED model.

THE MODEL (search-validated)
  The feature set comes from a systematic held-out variable search
  (27 May): every pre-race variable was tested, and the model is fitted
  on the combination that best predicts raceShapeEarly on races it was
  NOT trained on. The model itself was a LinearRegression until an Aug
  2026 retrain (train(), see below) found LightGBM on the SAME features
  measurably better held-out (+0.270 vs +0.261 on a fresh split) -
  feature set unchanged, model type only. The artifacts are:
    race_speed_model.joblib   - the fitted model (LightGBM, Aug 2026+)
    race_speed_config.json    - feature order, medians, banding quantiles

  The features are per-RACE aggregates of the field's prior-run history:
  field-mean past margins, past race-shapes, barriers, distance, settling
  estimates, etc. (full list in race_speed_config.json).

HONEST CONFIDENCE - read before relying on this.
  Held-out correlation with actual raceShapeEarly is +0.27 (R2 ~7.3%),
  re-measured on retrain - see config.json's heldout_corr for the current
  number. That is a REAL signal - it survived held-out evaluation, it is not
  overfitting - but it is MODEST. Race tempo is substantially decided on
  the day (jockey tactics, gate speed) and cannot be read fully from
  pre-race data. So the Hot/Fast/Even/Slow label is a LOW-CONFIDENCE
  estimate, not a reliable prediction. Any use that feeds the WPR
  projection must be a small, gentle adjustment proportionate to this
  modest reliability - never a large swing.

  This replaced an earlier hand-built lead-seeker formula which scored
  only +0.01. The systematic search improved it to +0.24.

USAGE
  python race_speed_estimate.py --race <race_id>
  python race_speed_estimate.py --validate
  python race_speed_estimate.py --retrain

NO EM DASHES policy: hyphens only in this file.
"""

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

_DIR = Path(__file__).parent
FORM_CSV = _DIR / "wpr_form_history.csv.gz"
RUNNERS_CSV = _DIR / "toprate_runners.csv"
MODEL_PATH = _DIR / "race_speed_model.joblib"
CONFIG_PATH = _DIR / "race_speed_config.json"

_MODEL = None
_CFG = None


def _load_model():
    """Load the trained race-speed model and config once."""
    global _MODEL, _CFG
    if _MODEL is not None:
        return
    if not MODEL_PATH.exists() or not CONFIG_PATH.exists():
        raise FileNotFoundError(
            f"race_speed_model.joblib / race_speed_config.json not found "
            f"in {_DIR}. Retrain with the variable-search script.")
    import joblib
    _MODEL = joblib.load(MODEL_PATH)
    _CFG = json.load(open(CONFIG_PATH))


def _prior_means(fh, race_date):
    """Build per-horse prior-mean lookups for every signal the model
    needs, restricted to runs before race_date."""
    cols = ["positionSettled", "field_size", "sect_ld_early", "sect_i_early",
            "sect_i_to800", "margin800m", "raceShapeEarly", "wpr",
            # candidates being tested (Aug 2026 reload - richer early-race
            # positional/sectional profile, see _race_features' own
            # before/after correlation check): position600m/800m give the
            # model TWO more early-race snapshots per horse than the single
            # positionSettled point; sect_i_to600 extends the already-used
            # sect_i_to800 with one more early-sectional data point;
            # margin600m is the early-race counterpart of margin800m.
            "position600m", "position800m", "sect_i_to600", "margin600m"]
    prior = fh[fh["date"] < race_date]
    out = {}
    for c in cols:
        if c not in prior.columns:
            out[c] = {}
            continue
        s = prior.dropna(subset=[c])
        out[c] = s.groupby("horse_lc")[c].mean().to_dict()

    # rel_by_distband (candidate, Aug 2026 reload): does THIS horse settle
    # differently at DIFFERENT distances (e.g. closer to the pace at
    # sprint trips, further back at staying trips)? positionSettled above
    # is a single all-distances average - this instead buckets a horse's
    # own prior relative-settle by 200m distance band (same _dist_band
    # convention wpr_projection.py's own_distance/track_barrier use), so
    # _race_features can prefer the band matching TODAY's trip when
    # available. Keyed by (horse_lc, dist_band).
    out["rel_by_distband"] = {}
    if {"positionSettled", "field_size", "distance"} <= set(prior.columns):
        ps_d = pd.to_numeric(prior["positionSettled"], errors="coerce")
        fs_d = pd.to_numeric(prior["field_size"], errors="coerce")
        dist_d = pd.to_numeric(prior["distance"], errors="coerce")
        valid_d = (ps_d > 0) & (fs_d > 0) & dist_d.notna()
        if valid_d.any():
            rel_d = (ps_d[valid_d] / fs_d[valid_d]).clip(0, 1)
            band_d = (dist_d[valid_d] // 200 * 200).astype(int)
            out["rel_by_distband"] = pd.DataFrame({
                "horse_lc": prior.loc[valid_d, "horse_lc"],
                "dist_band": band_d, "rel": rel_d,
            }).groupby(["horse_lc", "dist_band"])["rel"].mean().to_dict()
    return out


def _race_features(race_runners, pmeans):
    """Build the per-race feature row the model expects."""
    rel, barrier, ld, ie, t8, m8, prse, pwpr = ([] for _ in range(8))
    rel800, rel600, t6, m6, rel_distmatch = [], [], [], [], []
    rel_by_distband = pmeans.get("rel_by_distband", {})
    for _, r in race_runners.iterrows():
        hl = str(r.get("horse", "")).strip().lower()
        ps = pmeans["positionSettled"].get(hl, np.nan)
        fs = pmeans["field_size"].get(hl, np.nan)
        rel_val = (ps / fs) if (ps == ps and fs == fs and fs > 0) else np.nan
        rel.append(rel_val)
        b = r.get("barrier")
        barrier.append(float(b) if b is not None and str(b) != "nan"
                       else np.nan)
        ld.append(pmeans["sect_ld_early"].get(hl, np.nan))
        ie.append(pmeans["sect_i_early"].get(hl, np.nan))
        t8.append(pmeans["sect_i_to800"].get(hl, np.nan))
        m8.append(pmeans["margin800m"].get(hl, np.nan))
        prse.append(pmeans["raceShapeEarly"].get(hl, np.nan))
        pwpr.append(pmeans["wpr"].get(hl, np.nan))
        # richer early-race positional/sectional profile (candidates)
        p8 = pmeans["position800m"].get(hl, np.nan)
        rel800.append((p8 / fs) if (p8 == p8 and fs == fs and fs > 0) else np.nan)
        p6 = pmeans["position600m"].get(hl, np.nan)
        rel600.append((p6 / fs) if (p6 == p6 and fs == fs and fs > 0) else np.nan)
        t6.append(pmeans["sect_i_to600"].get(hl, np.nan))
        m6.append(pmeans["margin600m"].get(hl, np.nan))
        # distance-matched relative settle: prefer this horse's own
        # relative settle at TODAY's 200m distance band; falls back to
        # NaN (not the unconditional rel_val) when no matching-band prior
        # run exists, so the field-level aggregate below reflects only
        # genuine distance-matched coverage, not a silently diluted mix.
        dist_today = r.get("distance")
        try:
            db_today = int(float(dist_today) // 200 * 200)
        except (TypeError, ValueError):
            db_today = None
        rel_distmatch.append(rel_by_distband.get((hl, db_today), np.nan)
                             if db_today is not None else np.nan)
    relA = np.array(rel, dtype=float)
    ldA = np.array(ld, dtype=float)
    rel800A = np.array(rel800, dtype=float)
    rel600A = np.array(rel600, dtype=float)
    relDistA = np.array(rel_distmatch, dtype=float)

    def nanmean(a):
        a = np.array(a, dtype=float)
        return float(np.nanmean(a)) if np.isfinite(a).any() else np.nan

    return {
        "n_leaders": float(np.nansum(relA <= 0.20)),
        "n_onpace": float(np.nansum(relA <= 0.40)),
        "mean_rel": nanmean(relA),
        "min_rel": float(np.nanmin(relA)) if np.isfinite(relA).any() else np.nan,
        "std_rel": float(np.nanstd(relA)) if np.isfinite(relA).any() else np.nan,
        "field_size": float(len(race_runners)),
        "mean_barrier": nanmean(barrier),
        "mean_ld": nanmean(ldA),
        "min_ld": float(np.nanmin(ldA)) if np.isfinite(ldA).any() else np.nan,
        "mean_ie": nanmean(ie),
        "mean_t8": nanmean(t8),
        "mean_m8": nanmean(m8),
        "mean_prse": nanmean(prse),
        "std_prse": float(np.nanstd(np.array(prse, dtype=float)))
            if np.isfinite(np.array(prse, dtype=float)).any() else np.nan,
        "mean_pwpr": nanmean(pwpr),
        "distance": float(race_runners["distance"].iloc[0])
            if "distance" in race_runners.columns else np.nan,
        # --- candidates being tested (Aug 2026 reload) - richer
        # early-race positional/sectional profile, see train()'s own
        # before/after held-out correlation check for the result ---
        "mean_rel800": nanmean(rel800A),
        "std_rel800": float(np.nanstd(rel800A)) if np.isfinite(rel800A).any() else np.nan,
        "mean_rel600": nanmean(rel600A),
        "std_rel600": float(np.nanstd(rel600A)) if np.isfinite(rel600A).any() else np.nan,
        "mean_t6": nanmean(t6),
        "mean_m6": nanmean(m6),
        "mean_rel_distmatch": nanmean(relDistA),
        "n_distmatch": float(np.isfinite(relDistA).sum()),
    }


def _tempo_label(predicted_rse):
    """Band predicted raceShapeEarly into a tempo label. HIGHER rse =
    faster early pace = Hot. raceShapeEarly's sign convention (confirmed
    against the Pace Bias doc and directly replicated on 476,719 real
    rows this session - see chat) is: POSITIVE = faster than standard,
    NEGATIVE = slower. A fast, hot-tempo race therefore has a HIGH
    (positive) raceShapeEarly, not a low one.

    BUG FIX (Aug 2026 v1, found while building the own_pace ADJ_TERM
    candidate): the four comparisons used to check q["slow"] FIRST (the
    LARGEST threshold), so almost every race was labelled "Hot"
    regardless of its actual predicted shape - confirmed on real data
    (100% "Hot" on a 419-race sample). Fixed by checking thresholds in
    ascending order.

    BUG FIX (Aug 2026 v2, found while investigating why own_pace/
    settle_pace both failed their held-out backtests): v1's fix corrected
    the CHECK ORDER but kept the underlying assumption that LOW rse means
    Hot - backwards. Verified directly: current live rs_label values,
    checked against ACTUAL measured raceShapeEarly across every month
    May-Aug 2026, showed "Hot" races averaging raceShapeEarly around -3
    to -8 (i.e. actually SLOW) and "Slow" races averaging around +1 (i.e.
    actually FAST) - a clean, persistent, monotonic inversion the v1 fix
    never touched. The y_quantiles in config.json (hot=10th percentile,
    slow=90th percentile of the raw distribution) are themselves fine -
    only which STRING gets returned for which quantile band was
    backwards. Fixed by mirroring which label each branch returns (no
    change to the quantile values or comparison operators needed).
    """
    q = _CFG["y_quantiles"]
    if predicted_rse <= q["hot"]:
        return "Slow"
    if predicted_rse <= q["fast"]:
        return "Even"
    if predicted_rse <= q["even"]:
        return "Fast"
    return "Hot"


def _score_from_rse(predicted_rse):
    """Map predicted raceShapeEarly to a 0-1 score, 1 = hottest (HIGH
    raceShapeEarly - see _tempo_label's docstring for the sign
    convention).

    BUG FIX (Aug 2026 v1): lo/hi were swapped, inverting the scale.

    BUG FIX (Aug 2026 v2, same discovery as _tempo_label's v2 fix): v1's
    lo/hi swap fix was itself built on the same backwards assumption (low
    rse = hot) that _tempo_label's v1 fix carried. q["hot"] and
    q["slow"] are already numerically correct as computed by train()
    (hot = the 10th percentile, i.e. the LOW end of the raw distribution;
    slow = the 90th percentile, the HIGH end) - that part was never
    broken. The bug was applying "1.0 -" on top of a lo/hi assignment
    that, without the inversion, already maps low rse -> score near 0
    and high rse -> score near 1 correctly. Fix: keep lo=q["hot"] (the
    low end), hi=q["slow"] (the high end) exactly as originally assigned,
    just drop the erroneous "1.0 -" (a first attempt at this fix
    swapped the key assignment INSTEAD of dropping the inversion, which
    cancels out and silently reproduces the original bug - caught by
    testing concrete values across the full range before shipping this).
    """
    q = _CFG["y_quantiles"]
    lo, hi = q["hot"], q["slow"]
    if hi == lo:
        return 0.5
    s = (predicted_rse - lo) / (hi - lo)
    return float(min(1.0, max(0.0, s)))


def estimate_race_speed(race_runners, race_date, fh, pmeans=None):
    """Estimate tempo for one race. Same signature as before so existing
    single-race callers (estimate_one) are unchanged: pmeans defaults to
    None, computed internally exactly as before. Callers scoring MANY
    races for the same day should compute _prior_means(fh, day_cutoff)
    ONCE and pass it in here - every race on a given day shares the
    same "prior" cutoff (the date-only precision means race_date is
    identical across the whole day), so re-deriving pmeans per race was
    the same expensive full-history groupby repeated once per race for
    an identical result each time. Returns dict: score, label,
    predicted_rse, field_size."""
    _load_model()
    if pmeans is None:
        pmeans = _prior_means(fh, race_date)
    feat = _race_features(race_runners, pmeans)
    med = _CFG["medians"]
    row = []
    for f in _CFG["features"]:
        v = feat.get(f)
        if v is None or (isinstance(v, float) and np.isnan(v)):
            v = med.get(f, 0.0)
        row.append(v)
    X = pd.DataFrame([row], columns=_CFG["features"])
    predicted_rse = float(_MODEL.predict(X)[0])
    return {
        "score": round(_score_from_rse(predicted_rse), 3),
        "label": _tempo_label(predicted_rse),
        "predicted_rse": round(predicted_rse, 2),
        "field_size": len(race_runners),
    }


def _load_form():
    if not FORM_CSV.exists():
        sys.exit(f"ERROR: {FORM_CSV.name} not found.")
    fh = pd.read_csv(FORM_CSV, dtype={"horse": str, "horse_id": str},
                     low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    for c in ["positionSettled", "field_size", "sect_ld_early",
              "sect_i_early", "sect_i_to800", "margin800m",
              "raceShapeEarly", "wpr"]:
        if c in fh.columns:
            fh[c] = pd.to_numeric(fh[c], errors="coerce")
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    return fh.sort_values(["horse_lc", "date"])


def estimate_one(race_id):
    if not RUNNERS_CSV.exists():
        sys.exit(f"ERROR: {RUNNERS_CSV.name} not found.")
    rdf = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                      low_memory=False)
    rdf["distance"] = pd.to_numeric(rdf["distance"], errors="coerce")
    rdf["barrier"] = pd.to_numeric(rdf["barrier"], errors="coerce")
    race = rdf[rdf["race_id"].astype(str) == str(race_id)]
    if len(race) == 0:
        sys.exit(f"No race found with race_id {race_id}.")
    race_date = pd.to_datetime(race["date"].iloc[0], errors="coerce")
    fh = _load_form()
    res = estimate_race_speed(race, race_date, fh)
    venue = race["venue"].iloc[0] if "venue" in race.columns else "?"
    print("=" * 60)
    print(f"RACE SPEED ESTIMATE - race {race_id}")
    print(f"{venue}  field {res['field_size']}")
    print("=" * 60)
    print(f"  tempo label   : {res['label']}")
    print(f"  score (0-1)   : {res['score']}  (1 = hottest)")
    print(f"  predicted rse : {res['predicted_rse']}")
    print(f"  (low-confidence estimate - held-out corr ~{_CFG['heldout_corr']:+.2f})")
    print("=" * 60)


def _load_and_prep_form():
    """Load + dedupe wpr_form_history.csv.gz for training: one row per
    horse+date (collapses repeated captures of the same historical run),
    barrier trials excluded. Separate from _load_form() (kept sorted by
    horse_lc/date, no dedup) since serving-time prior-means lookups don't
    need dedup (a mean over a few duplicate identical-value rows is the
    same mean) but training-row counting does (each race must be counted
    once, not once per capture)."""
    fh = pd.read_csv(FORM_CSV, dtype={"horse": str, "horse_id": str},
                     low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    for c in ["positionSettled", "field_size", "sect_ld_early",
              "sect_i_early", "sect_i_to800", "margin800m",
              "raceShapeEarly", "wpr", "barrier", "distance", "raceNumber"]:
        if c in fh.columns:
            fh[c] = pd.to_numeric(fh[c], errors="coerce")
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    fh = fh.sort_values("date").drop_duplicates(subset=["horse_lc", "date"], keep="last")
    return fh


def train(out_dir="."):
    """Retrain the race-speed model.

    Aug 2026 backtest (see confidence/race-speed search scratch scripts,
    not committed): tested adding barrier-relative and going/track-grading
    features on top of the existing 16 - neither gave a real held-out
    gain, and combining them with a nonlinear model made things WORSE
    (LinearRegression + barrier: +0.265 vs LightGBM + barrier: +0.265,
    both below LightGBM alone). The one genuine improvement was swapping
    the model itself: LightGBM on the SAME 16 features beat the original
    LinearRegression on a fresh held-out split (+0.270 vs +0.261). Feature
    set unchanged; model type only.

    Race key: (track, date, raceNumber) within wpr_form_history.csv.gz -
    confirmed by direct inspection to correctly group a historical race's
    runners (every runner in a group shares the same raceShapeEarly).
    race_id in that file is NOT usable for this - it identifies which
    race a row's capture was taken FOR, not the historical race the row
    itself describes, and is null on almost every row.
    """
    import lightgbm as lgb
    from sklearn.metrics import mean_absolute_error
    import joblib

    print("Loading form history...")
    fh = _load_and_prep_form()
    print(f"  {len(fh):,} rows (one per horse+date), {fh['horse_lc'].nunique():,} horses")

    fh = fh.dropna(subset=["track", "raceNumber", "raceShapeEarly"])
    fh["race_key"] = (fh["track"].astype(str) + "|" + fh["date"].astype(str)
                      + "|" + fh["raceNumber"].astype(str))

    race_meta = (fh.groupby("race_key")
                   .agg(date=("date", "first"), rse=("raceShapeEarly", "first"),
                        n=("horse_lc", "count"))
                   .reset_index())
    race_meta = race_meta[race_meta["n"] >= 4]
    print(f"  {len(race_meta):,} races with 4+ runners and a known raceShapeEarly")

    cut = race_meta["date"].quantile(0.70)
    train_races = race_meta[race_meta["date"] < cut]
    test_races = race_meta[race_meta["date"] >= cut]
    print(f"  split at {cut.date()}: {len(train_races):,} train, {len(test_races):,} test")

    fh_by_race = fh.groupby("race_key")
    pmeans_cache = {}

    def prior_means_cached(cutoff_date):
        if cutoff_date not in pmeans_cache:
            pmeans_cache[cutoff_date] = _prior_means(fh, cutoff_date)
        return pmeans_cache[cutoff_date]

    def build_rows(race_df):
        rows, ys = [], []
        for day, day_races in race_df.groupby(race_df["date"].dt.normalize()):
            pmeans = prior_means_cached(day)
            for _, rr in day_races.iterrows():
                runners = fh_by_race.get_group(rr["race_key"])
                rows.append(_race_features(runners, pmeans))
                ys.append(rr["rse"])
        return pd.DataFrame(rows), np.array(ys, dtype=float)

    print("Building training rows...")
    Xtr, ytr = build_rows(train_races)
    print("Building held-out rows...")
    Xte, yte = build_rows(test_races)

    features = list(Xtr.columns)
    med = Xtr.median()
    Xtr_f = Xtr.fillna(med)
    Xte_f = Xte.fillna(med)

    model = lgb.LGBMRegressor(n_estimators=200, max_depth=3, learning_rate=0.05,
                              num_leaves=8, random_state=42, verbosity=-1)
    model.fit(Xtr_f, ytr)
    pred_te = model.predict(Xte_f)
    heldout_corr = float(np.corrcoef(pred_te, yte)[0, 1])
    heldout_mae = float(mean_absolute_error(yte, pred_te))
    print(f"  held-out correlation: {heldout_corr:+.3f}")
    print(f"  held-out MAE: {heldout_mae:.3f}")

    # Tempo-label bucket cutpoints. BUG FIX (Aug 2026 v1, found while
    # investigating a skewed live label distribution - 826/1024 August
    # 2026 races landing in "Fast", only 1 "Slow", far from the intended
    # ~10/25/30/25% split): these used to be computed from the TRAIN
    # TARGET's own distribution (ytr - actual raceShapeEarly), then
    # applied to bucket the MODEL'S PREDICTIONS. That's a mismatch - with
    # only +0.277 held-out correlation (R^2 ~7.7%), the model's
    # predictions are far less variable than the real outcomes they're
    # trying to predict (regression to the mean, as any weak model's
    # predictions must be), so predicted values rarely reach the
    # threshold levels computed from the much wider actual-value spread -
    # confirmed directly: predicted_rse on a 1,024-race August sample had
    # a 25th-75th percentile range of just -0.37 to +0.47, while the
    # actual-value quantiles used as thresholds spanned -4.2 to +4.1.
    # v1's fix: compute the thresholds from the model's OWN predictions
    # on the TRAINING set (pred_tr) instead.
    #
    # BUG FIX v2 (Sep 2026, user-flagged: "all races... predicted hot or
    # fast" on the live dashboard): v1 was still wrong, in the same
    # direction as the bug it fixed - pred_tr is the model's predictions
    # on the exact rows it was FIT to, which is never what live serving
    # sees (every real call is out-of-sample by definition). Confirmed
    # directly: scoring 1,496 real historical races through the actual
    # live estimate_race_speed() call path gave predicted_rse quantiles
    # (p10=-0.60, p35=-0.04, p65=+0.45, p90=+1.21) running a full +0.4 to
    # +0.6 higher across the board than pred_tr's quantiles - a live label
    # split of Hot 49%/Fast 33%/Even 15%/Slow 4%, nowhere near the
    # intended ~35/30/25/10%. pred_te (the held-out test predictions,
    # already computed two lines up for heldout_corr/heldout_mae) is
    # sitting right there and IS genuinely out-of-sample, the same way
    # every live call is - fit the quantiles on that instead.
    hot, fast, even, slow = np.quantile(pred_te, [0.10, 0.35, 0.65, 0.90])

    Path(out_dir).mkdir(exist_ok=True)
    joblib.dump(model, Path(out_dir) / "race_speed_model.joblib")
    json.dump({
        "features": features,
        "medians": med.to_dict(),
        "heldout_corr": heldout_corr,
        "y_quantiles": {"hot": float(hot), "fast": float(fast),
                        "even": float(even), "slow": float(slow)},
        "n_train": int(len(Xtr)),
    }, open(Path(out_dir) / "race_speed_config.json", "w"), indent=1)
    print(f"  written -> {out_dir}/race_speed_model.joblib, race_speed_config.json")


def validate():
    _load_model()
    print("=" * 60)
    print("RACE SPEED MODEL")
    print(f"  features    : {len(_CFG['features'])}")
    print(f"  trained on  : {_CFG['n_train']} races")
    print(f"  held-out correlation : {_CFG['heldout_corr']:+.3f}")
    print(f"  (R2 ~ {_CFG['heldout_corr']**2*100:.1f}% - modest but real)")
    print("=" * 60)


def main():
    ap = argparse.ArgumentParser(description="Automated race-speed estimate.")
    ap.add_argument("--race", default=None, help="race_id to estimate")
    ap.add_argument("--validate", action="store_true",
                    help="report the model's held-out performance")
    ap.add_argument("--retrain", action="store_true",
                    help="retrain the model from wpr_form_history.csv.gz")
    args = ap.parse_args()
    if args.retrain:
        train(out_dir=str(_DIR))
    elif args.validate:
        validate()
    elif args.race:
        estimate_one(args.race)
    else:
        ap.print_help()


if __name__ == "__main__":
    main()
