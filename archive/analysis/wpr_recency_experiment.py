"""
wpr_recency_experiment.py - does the recency half-life matter?

Rolling walk-forward test of the projection's memory setting. The runner
population grew ~60x and skewed to lower-grade meetings; this asks whether the
current 60-day recency half-life predicts CURRENT races as well as some other
setting, measured out of sample the way the model is actually used.

NOTHING in production changes. This only reports numbers. Adopt a new setting
only if it beats 60-day on rolling OOS MAE-after-offset by more than the
cutoff-to-cutoff noise.

DESIGN (leak-free, mirrors production = model + calibration offset)
  For each monthly cutoff C over the last N months:
    fit slice   = rows with date <  C - 1 month
    calib slice = rows with date in [C - 1 month, C)
    test slice  = rows with date in [C, C + 1 month)
  Fit the projection on fit (recency-weighted by the setting). Measure the
  calibration offset = median(target - pred) on calib. Apply model + offset to
  test. Accumulate test errors. The offset is always measured on data BEFORE
  the test month, so there is no leakage.

SETTINGS SWEPT
  half-life weighting: none (equal), 365, 180, 90, 60 (current), 30 days
  recent-only window:  train on last 365d only, last 180d only (no weighting)

USAGE
  python wpr_recency_experiment.py --jobs -1            # build frame + run
  python wpr_recency_experiment.py --rebuild --jobs -1  # force frame rebuild
  python wpr_recency_experiment.py --months 12          # cutoffs to walk

NO EM DASHES policy: hyphens only.
"""

import sys
import numpy as np
import pandas as pd
from pathlib import Path

import wpr_projection as W

_FRAME_CACHE = "wpr_training_frame_exp.parquet"
_FRAME_CACHE_PKL = "wpr_training_frame_exp.pkl"


def _save_frame(D):
    try:
        D.to_parquet(_FRAME_CACHE)
        return _FRAME_CACHE
    except Exception:
        D.to_pickle(_FRAME_CACHE_PKL)
        return _FRAME_CACHE_PKL


def _load_cached():
    if Path(_FRAME_CACHE).exists():
        try:
            return pd.read_parquet(_FRAME_CACHE)
        except Exception:
            pass
    if Path(_FRAME_CACHE_PKL).exists():
        return pd.read_pickle(_FRAME_CACHE_PKL)
    return None


def _weights(dates, ref, half_life):
    """Exponential-decay weights by age in days from ref. None = equal."""
    if half_life is None:
        return None
    age = (ref - pd.to_datetime(dates)).dt.days.clip(lower=0).values.astype(float)
    return 0.5 ** (age / float(half_life))


def load_frame(form_history_csv="wpr_form_history.csv", rebuild=False, n_jobs=1):
    """Build the feature frame once and cache it. Reuse on later runs."""
    cached = None if rebuild else _load_cached()
    if cached is not None:
        print("Loading cached frame ...")
        D = cached
    else:
        print(f"Building feature frame (n_jobs={n_jobs}) ...")
        D = W.build_training_frame(form_history_csv, n_jobs=n_jobs)
        dest = _save_frame(D)
        print(f"  cached -> {dest}")
    D = D.dropna(subset=["target", "date"]).sort_values("date").reset_index(drop=True)
    D["date"] = pd.to_datetime(D["date"])
    med = D[W.FEATURES].median()
    D[W.FEATURES] = D[W.FEATURES].fillna(med)
    print(f"  {len(D):,} rows  span {D['date'].min().date()} -> {D['date'].max().date()}")
    return D


def _fit_predict(Dfit, Dtest, half_life, recent_window_days=None):
    """Fit projection on Dfit (optionally recency-weighted or recent-only),
    return predictions on Dtest."""
    from sklearn.ensemble import HistGradientBoostingRegressor
    fit = Dfit
    sw = None
    ref = Dfit["date"].max()
    if recent_window_days is not None:
        cut = ref - pd.Timedelta(days=recent_window_days)
        fit = Dfit[Dfit["date"] >= cut]
    else:
        sw = _weights(fit["date"], ref, half_life)
    if len(fit) < 200:
        return None
    m = HistGradientBoostingRegressor(max_iter=350, max_depth=3,
                                      learning_rate=0.04, random_state=42)
    m.fit(fit[W.FEATURES], fit["target"], sample_weight=sw)
    return m.predict(Dtest[W.FEATURES])


def walk_forward(D, settings, months=12):
    """Roll a monthly cutoff backward from the latest month and accumulate
    out-of-sample errors per setting."""
    last = D["date"].max().normalize().replace(day=1)
    cutoffs = [last - pd.DateOffset(months=k) for k in range(months, 0, -1)]
    # per-setting accumulators of per-cutoff (mae_after_offset, median_bias, offset)
    acc = {name: [] for name in settings}
    per_test_err = {name: [] for name in settings}   # (residual, field_size, race_class)

    for C in cutoffs:
        fit_end = C - pd.DateOffset(months=1)
        Dfit = D[D["date"] < fit_end]
        Dcal = D[(D["date"] >= fit_end) & (D["date"] < C)]
        Dtest = D[(D["date"] >= C) & (D["date"] < C + pd.DateOffset(months=1))]
        if len(Dfit) < 500 or len(Dcal) < 50 or len(Dtest) < 50:
            continue
        for name, cfg in settings.items():
            pred_cal = _fit_predict(Dfit, Dcal, cfg.get("half_life"),
                                    cfg.get("recent_window_days"))
            if pred_cal is None:
                continue
            offset = float(np.median(Dcal["target"].values - pred_cal))
            pred_te = _fit_predict(Dfit, Dtest, cfg.get("half_life"),
                                   cfg.get("recent_window_days"))
            if pred_te is None:
                continue
            resid = Dtest["target"].values - (pred_te + offset)
            acc[name].append((np.abs(resid).mean(), float(np.median(resid)), offset))
            for r, fs, rc in zip(resid, Dtest.get("field_size", pd.Series([np.nan]*len(Dtest))),
                                  Dtest.get("race_class", pd.Series([None]*len(Dtest)))):
                per_test_err[name].append((r, fs, rc))
    return acc, per_test_err, cutoffs


def report(acc, per_test_err):
    print("\n" + "=" * 72)
    print("ROLLING WALK-FORWARD  (MAE after each setting's own offset)")
    print("=" * 72)
    print(f"{'setting':22s} {'OOS MAE':>9s} {'+/-':>6s} {'med bias':>9s} {'avg offset':>11s} {'cuts':>5s}")
    rows = []
    for name, vals in acc.items():
        if not vals:
            print(f"{name:22s}   (insufficient data)")
            continue
        maes = np.array([v[0] for v in vals])
        biases = np.array([v[1] for v in vals])
        offs = np.array([v[2] for v in vals])
        rows.append((name, maes.mean(), maes.std(), np.median(biases), offs.mean(), len(vals)))
    rows.sort(key=lambda r: r[1])
    for name, mae, sd, bias, off, n in rows:
        print(f"{name:22s} {mae:9.3f} {sd:6.3f} {bias:+9.2f} {off:+11.2f} {n:5d}")

    if len(rows) >= 2:
        best = rows[0]
        cur = next((r for r in rows if r[0] == "half_life_60 (current)"), None)
        print("\nBest setting:", best[0], f"(OOS MAE {best[1]:.3f})")
        if cur:
            delta = cur[1] - best[1]
            noise = max(best[2], cur[2])
            verdict = ("ADOPT: beats current by more than noise"
                       if delta > noise else
                       "KEEP CURRENT: improvement within cutoff-to-cutoff noise")
            print(f"vs current 60d (OOS MAE {cur[1]:.3f}): delta {delta:+.3f}, "
                  f"noise ~{noise:.3f}  ->  {verdict}")

    # composition breakdown: best vs current, by field-size bucket
    print("\n" + "-" * 72)
    print("COMPOSITION: OOS MAE by field size (best vs current)")
    names = [rows[0][0]] + (["half_life_60 (current)"] if any(
        r[0] == "half_life_60 (current)" for r in rows) else [])
    for name in names:
        errs = per_test_err.get(name, [])
        if not errs:
            continue
        df = pd.DataFrame(errs, columns=["resid", "field_size", "race_class"])
        df["abserr"] = df["resid"].abs()
        print(f"  [{name}]")
        for lo, hi, lbl in [(0, 8, "<=7"), (8, 13, "8-12"), (13, 99, "13+")]:
            g = df[(df["field_size"] >= lo) & (df["field_size"] < hi)]
            if len(g):
                print(f"     field {lbl:5s}  n={len(g):5d}  MAE={g['abserr'].mean():.3f}  "
                      f"bias={g['resid'].median():+.2f}")


def main():
    rebuild = "--rebuild" in sys.argv
    n_jobs = 1
    if "--jobs" in sys.argv:
        try:
            n_jobs = int(sys.argv[sys.argv.index("--jobs") + 1])
        except (IndexError, ValueError):
            pass
    months = 12
    if "--months" in sys.argv:
        try:
            months = int(sys.argv[sys.argv.index("--months") + 1])
        except (IndexError, ValueError):
            pass

    settings = {
        "no_weighting (equal)":     {"half_life": None},
        "half_life_365":            {"half_life": 365},
        "half_life_180":            {"half_life": 180},
        "half_life_90":             {"half_life": 90},
        "half_life_60 (current)":   {"half_life": 60},
        "half_life_30":             {"half_life": 30},
        "recent_365d_only":         {"recent_window_days": 365},
        "recent_180d_only":         {"recent_window_days": 180},
    }

    D = load_frame(rebuild=rebuild, n_jobs=n_jobs)
    acc, per_test_err, cutoffs = walk_forward(D, settings, months=months)
    print(f"\nwalk-forward cutoffs used: {len([c for c in cutoffs])} monthly steps "
          f"ending {cutoffs[-1].date()}")
    report(acc, per_test_err)


if __name__ == "__main__":
    main()
