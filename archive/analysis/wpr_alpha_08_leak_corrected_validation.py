"""
wpr_alpha_08_leak_corrected_validation.py - re-checks the alpha=0.8
_BASE_BLEND_ALPHA decision after discovering (Sep 2026, while testing a
fresh ML model) that wpr.build_training_frame()'s own internal wpr_nett
merge is NOT point-in-time correct: it joins onto wpr_form_history.csv.gz
via run_id, which every row in a horse's scraped history batch shares
(whichever race triggered that scrape) - so EVERY historical row for a
horse gets stamped with the SAME wpr_nett value (whatever TopRate's
rating was as of the LATEST scrape), not that row's own pre-race value.
Verified directly: e.g. horse_id 300668 showed wpr_nett=84.1 identically
across 12 rows spanning 2026-04-27 to 2026-08-28.

WHY THIS MATTERS FOR ALPHA SPECIFICALLY: _BASE_BLEND_ALPHA controls how
much weight wpr_nett gets vs ewm3 (a genuinely causal, point-in-time
recency-weighted feature computed from strictly-prior real runs). A
LEAKED wpr_nett (frozen at each horse's future/latest-known rating)
looks artificially more predictive in a held-out MAE test than a real
point-in-time value would - and that artificial advantage grows with
however much weight alpha gives it. So the original alpha=0.8 vs 0.5
comparison (wpr_alpha_08_proper_validation.py, itself using this same
leaky build_training_frame() output) was very plausibly biased toward
FAVOURING HIGHER alpha, not just noisy.

GOOD NEWS, VERIFIED SEPARATELY: this leak does NOT affect the live
dashboard (project_race() reads cur_wpr_nett fresh from today's own
toprate_runners.csv row every time, never a historical run_id merge)
NOR any of this session's "real model" recompute scripts (wpr_full_
history_current_model_breakdown.py and everything built on top of it) -
those all source wpr_nett the same correct way project_race() does.
Verified directly: toprate_runners.csv's OWN wpr_nett column varies
properly per race for a given horse (e.g. "A Pound Of Salt": 73.1, 83.1,
78.9, 83.4, 82.0, 81.9 across 6 different dates) - a genuinely
different, correct data path from build_training_frame()'s internal
merge. Only build_training_frame()-based offline validation (this
alpha decision, the piecewise-calibration-removal decision, and this
session's other MAE-based tests that used add_base()) is in question.

METHOD: reuses wpr_alpha_08_proper_validation.py's exact methodology
(K=4 chronological folds, each alpha gets its OWN freshly-refit
piecewise base calibration per fold - never reusing calibration fit for
a different alpha, per wpr_projection.py's own documented requirement)
but with wpr_nett corrected: dropped from build_training_frame()'s
output and re-merged from toprate_runners.csv by (horse, date, race_id),
the same clean point-in-time-correct source the live model and every
"real model" script this session already uses.

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
from wpr_bet_selection_post_retrain import merge_price_pfm, report, RUNNERS_CSV

CACHE_PATH = Path("/tmp/wpr_full_training_frame_cache.pkl")
ALPHA_CANDIDATES = [0.5, 0.7, 0.8, 0.9, 1.0]
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]
N_FOLDS = 4
PRICE_CAP = 26.0
EDGE_THRESHOLDS = [0.05, 0.10, 0.20]


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
    with open(CACHE_PATH, "wb") as fh:
        pickle.dump((form_mtime, full), fh)
    return full


def fix_wpr_nett_leak(full):
    """Drops build_training_frame()'s own (leaky, frozen-per-horse)
    wpr_nett and re-merges the point-in-time-correct version straight
    from toprate_runners.csv, keyed by (horse, date, race_id) - the same
    clean source project_race() and every real-model script use."""
    tr = pd.read_csv(RUNNERS_CSV, dtype={"race_id": str}, low_memory=False,
                      usecols=["horse", "date", "race_id", "wpr_nett"])
    tr["date"] = pd.to_datetime(tr["date"], errors="coerce")
    tr = tr.rename(columns={"wpr_nett": "wpr_nett_fixed"})
    tr = tr.dropna(subset=["date"]).drop_duplicates(subset=["horse", "date", "race_id"], keep="first")
    full = full.drop(columns=["wpr_nett"], errors="ignore")
    full["race_id"] = full["race_id"].astype(str)
    before = len(full)
    full = full.merge(tr, on=["horse", "date", "race_id"], how="left")
    assert len(full) == before, "merge changed row count - key not unique"
    full = full.rename(columns={"wpr_nett_fixed": "wpr_nett"})
    print(f"  wpr_nett (leak-fixed) coverage: {full['wpr_nett'].notna().sum():,} / {len(full):,}")
    return full


def raw_base_at_alpha(frame, alpha):
    nett, ewm3 = frame["wpr_nett"], frame["ewm3"]
    both = nett.notna() & ewm3.notna()
    blended = pd.Series(np.where(both, alpha * nett + (1 - alpha) * ewm3, nett.fillna(ewm3)), index=frame.index)
    return blended.fillna(frame["avg_last3"]).fillna(frame["career_avg"])


def fit_piecewise_calibration(train_raw_base, train_target):
    p10, p80 = np.percentile(train_raw_base, [10, 80])
    segments = {}
    for name, mask in [
        ("low", train_raw_base <= p10),
        ("mid", (train_raw_base > p10) & (train_raw_base <= p80)),
        ("high", train_raw_base > p80),
    ]:
        x, y = train_raw_base[mask], train_target[mask]
        if mask.sum() < 30:
            segments[name] = (0.0, 1.0)
            continue
        slope, intercept = np.polyfit(x, y, 1)
        segments[name] = (intercept, slope)
    return p10, p80, segments


def apply_piecewise_calibration(raw_base, calib):
    p10, p80, segments = calib
    low_i, low_s = segments["low"]
    mid_i, mid_s = segments["mid"]
    high_i, high_s = segments["high"]
    return np.select(
        [raw_base <= p10, raw_base > p80],
        [low_i + low_s * raw_base, high_i + high_s * raw_base],
        default=mid_i + mid_s * raw_base,
    )


def fit_and_score_alpha(train, test, alpha):
    train = train.copy()
    test = test.copy()
    add_track_barrier(train, [train, test])
    add_closing_merit([train, test], train["date"].max())
    edges_t, lookup_t = fit_bucket_lookup(train, "trainer_win_pct_365d")
    edges_j, lookup_j = fit_bucket_lookup(train, "jockey_win_pct_90d")
    apply_bucket(train, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(train, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")
    apply_bucket(test, "trainer_win_pct_365d", edges_t, lookup_t, "trainer_merit")
    apply_bucket(test, "jockey_win_pct_90d", edges_j, lookup_j, "jockey_merit")

    train_raw = raw_base_at_alpha(train, alpha)
    calib = fit_piecewise_calibration(train_raw.to_numpy(), train["target"].to_numpy())
    train["_base_cand"] = apply_piecewise_calibration(train_raw.to_numpy(), calib)
    test_raw = raw_base_at_alpha(test, alpha)
    test["_base_cand"] = apply_piecewise_calibration(test_raw.to_numpy(), calib)

    for f in (train, test):
        f["adj_total"] = wpr._cap_adj_sum(f[wpr.ADJ_TERMS].to_numpy()).sum(axis=1) * wpr._CALIB_ADJ_SLOPE
        f["wprp_proj_cand"] = f["_base_cand"] + f["adj_total"]

    best_beta, best_brier = 0.15, float("inf")
    for b in BETA_GRID:
        rows = []
        for rid, g in train.groupby("race_id"):
            if len(g) < 4:
                continue
            pv = g["wprp_proj_cand"].to_numpy(dtype=float)
            e = np.exp(b * (pv - pv.max()))
            p = e / e.sum()
            rows.extend(zip(p, g["won"]))
        arr = pd.DataFrame(rows, columns=["p", "won"])
        brier = float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("inf")
        if brier < best_brier:
            best_brier, best_beta = brier, b

    def _prob(g):
        pv = g["wprp_proj_cand"].to_numpy(dtype=float)
        e = np.exp(best_beta * (pv - pv.max()))
        return pd.Series(e / e.sum(), index=g.index)

    test["model_prob"] = test.groupby("race_id", group_keys=False).apply(_prob)

    def _edge(g):
        p_mkt = (1.0 / g["sp"]) / (1.0 / g["sp"]).sum()
        return g["model_prob"] - p_mkt

    test["edge"] = test.groupby("race_id", group_keys=False).apply(_edge)

    mae = (test["target"] - test["_base_cand"]).abs().mean()
    top_idx = test.groupby("race_id")["wprp_proj_cand"].idxmax()
    tops = test.loc[top_idx]
    high = tops[tops["model_prob"] >= 0.5]
    fav_actual = high["won"].mean() if len(high) else float("nan")
    fav_implied = high["model_prob"].mean() if len(high) else float("nan")

    return test, mae, best_beta, len(high), fav_actual, fav_implied


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = add_base(full)
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    print(f"\nScoped rows: {len(full):,}")
    full = full.sort_values("date").reset_index(drop=True)
    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    summary = []
    for alpha in ALPHA_CANDIDATES:
        print(f"\n{'='*90}\nalpha = {alpha}\n{'='*90}")
        fold_maes, fold_fav_gaps = [], []
        all_test_scored = []
        for i in range(N_FOLDS):
            test = full[full["_fold"] == i]
            train = full[full["_fold"] != i]
            scored, mae, beta, n_fav, fav_actual, fav_implied = fit_and_score_alpha(train, test, alpha)
            fold_maes.append(mae)
            gap = (fav_actual - fav_implied) * 100 if n_fav else float("nan")
            fold_fav_gaps.append(gap)
            all_test_scored.append(scored)
            print(f"  fold {i}: MAE={mae:.4f}  beta={beta}  >=50% group n={n_fav}  "
                  f"implied={fav_implied*100:.1f}% actual={fav_actual*100:.1f}% gap={gap:+.1f}pp")

        pooled = pd.concat(all_test_scored, ignore_index=True)
        avg_mae = np.mean(fold_maes)
        print(f"\n  avg MAE across folds: {avg_mae:.4f} (std {np.std(fold_maes):.4f})")
        print(f"  avg favourite-calibration gap: {np.nanmean(fold_fav_gaps):+.1f}pp")
        print(f"  Summary-tab-style edge/ROI (pooled across all 4 held-out folds):")
        roi_by_thr = {}
        for thr in EDGE_THRESHOLDS:
            sub = pooled[(pooled["edge"] >= thr) & (pooled["sp"] <= PRICE_CAP)]
            report(sub, f"edge>={thr:.2f}, price<=${PRICE_CAP:.0f}")
        summary.append((alpha, avg_mae, np.nanmean(fold_fav_gaps)))

    print(f"\n{'='*90}\nSUMMARY (leak-corrected)\n{'='*90}")
    print(f"{'alpha':>8}  {'avg MAE':>10}  {'fav-calib gap':>15}")
    for alpha, mae, gap in summary:
        print(f"{alpha:>8}  {mae:>10.4f}  {gap:>+14.1f}pp")

    print("\nSame multiple-comparisons caveat as always: one backtest, not a guarantee.")


if __name__ == "__main__":
    run()
