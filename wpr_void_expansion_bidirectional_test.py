"""
wpr_void_expansion_bidirectional_test.py - the second-direction check
requested on top of wpr_void_expansion_test.py's result (baseline held-out
MAE 6.351 -> candidate 6.241 with the expanded STRONG list, a real
improvement, but measured on ONLY train_wpr_projection()'s own single
chronological direction: fit on the oldest 70%, test on the newest 15%).

This codebase's own established bar for trusting a candidate change (see
wpr_own_pace_backtest.py, and every ADJ_TERMS decision in wpr_projection.py's
own changelog comments) requires BOTH directions of a swapped chronological
split to agree - a result that only holds one way is noise, not a real
effect. train_wpr_projection() itself has no "reverse direction" option (it
always fits oldest->newest), so this script extracts its own core logic
(base computation, void filter, surface filter, then the population-lookup
fits: track_barrier and closing_merit, both fit trn-only and therefore
direction-sensitive; trainer_merit/jockey_merit, which _fit_merit_lookup
fits from its OWN internal coverage-aware cutoff on the FULL frame
regardless of direction - see that function's own docstring - so those two
are computed once and reused unchanged in both directions) and evaluates
held-out MAE (base + capped sum(ADJ_TERMS), the exact live projection
formula - see _additive_predict in train_wpr_projection) in both:

  Direction A (forward, matches production): trn = oldest 70% of dates,
    te = newest 15%.
  Direction B (reversed): trn = newest 70% of dates, te = oldest 15%.

Same non-destructive design as wpr_void_expansion_test.py: wpr_void.STRONG
is monkeypatched in-process only (never written to wpr_void.py on disk) and
restored before exit either way. No model artifacts are saved by this
script at all (it only needs the held-out MAE number, not a shippable
model).

NO EM DASHES policy: hyphens only.
"""
import time

import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
import wpr_void

FORM_CSV = "wpr_form_history.csv.gz"

NEW_STRONG = [
    "reared", "took no part", "difficult to load", "fractious",
    "struck head", "stewards queried", "stewards query",
    "resented kickback", "failed to handle", "cardiac",
    "amiss", "flatfooted",
]
ORIGINAL_STRONG = list(wpr_void.STRONG)


def prepare_frame():
    """Mirrors train_wpr_projection()'s own row-prep exactly (merge trainer/
    jockey trailing win-rate, void filter using whatever wpr_void.STRONG
    currently is, surface filter, _base/_y) but stops short of fitting any
    models or writing anything - the caller does the (direction-aware)
    fitting."""
    print("  building training frame (build_features - the slow step)...")
    D = wpr.build_training_frame(FORM_CSV, n_jobs=-1).dropna(subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} training rows")

    _name_map, _tj_lookup = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        n_void = int(sum(void_mask))
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: excluded {n_void:,} compromised runs, {len(D):,} rows remain")

    if "going" in D.columns:
        g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} blank-going rows, {len(D):,} remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()
    return D


def fit_track_barrier(trn):
    tb_resid = trn["target"] - trn["career_avg"]
    tb_band = [wpr._barrier_band(b, f) for b, f in zip(trn["barrier"], trn["field_size"])]
    tb_dist_band = (trn["cur_distance"] // 200 * 200).astype(int)
    tb_frame = pd.DataFrame({"track": trn["track"], "dist_band": tb_dist_band,
                              "band": tb_band, "residual": tb_resid}).dropna(subset=["track", "band", "residual"])
    tb_global = tb_frame.groupby("band")["residual"].mean().to_dict()
    lookup = {}
    for (trk, db), g in tb_frame.groupby(["track", "dist_band"]):
        stats = g.groupby("band")["residual"].agg(["mean", "count"])
        shrunk = {}
        for b in ["Inside", "Mid", "Wide"]:
            if b in stats.index:
                n, m = stats.loc[b, "count"], stats.loc[b, "mean"]
                shrunk[b] = (n * m + wpr._TRACK_BARRIER_K * tb_global.get(b, 0.0)) / (n + wpr._TRACK_BARRIER_K)
            else:
                shrunk[b] = tb_global.get(b, 0.0)
        center = float(np.mean(list(shrunk.values())))
        lookup[f"{trk}|{int(db)}"] = {
            b: float(max(-wpr._OWN_DELTA_CAP, min(wpr._OWN_DELTA_CAP, shrunk[b] - center))) for b in shrunk
        }
    return lookup


def fit_pace_baseline_reversed(cutoff_date):
    """Mirrors wpr._fit_pace_baseline exactly, except fitting on dates ON OR
    AFTER cutoff_date (the 'trn' side of the REVERSED direction) instead of
    strictly before it. _fit_pace_baseline itself has no direction argument
    (see its own docstring - always trn = before cutoff), so this is a
    deliberate, minimal local copy for the one line that needs to flip,
    same precedent as wpr_own_pace_backtest.py's own add_track_barrier."""
    fh = pd.read_csv(FORM_CSV, low_memory=False)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = wpr._dedup_scrape_baseline(fh, verbose=False)
    fh = fh[(fh.get("isBarrierTrial") != True) & (fh.get("is_jumpout") != True)]
    fh = fh[fh["date"] >= pd.to_datetime(cutoff_date)]
    sect = pd.to_numeric(fh.get("sect_i_l600"), errors="coerce")
    early = pd.to_numeric(fh.get("raceShapeEarly"), errors="coerce")
    d = pd.DataFrame({"sect": sect, "early": early}).dropna()
    d["bucket"] = d["early"].apply(wpr._closing_merit_bucket)
    d = d.dropna(subset=["bucket"])
    return {k: float(v) for k, v in d.groupby("bucket")["sect"].mean().items()}


def additive_predict(frame):
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)


def held_out_mae_both_directions(D, label):
    # trainer_merit/jockey_merit: direction-independent by design (see
    # _fit_merit_lookup's own docstring - it derives its own coverage-aware
    # cutoff from the FULL frame regardless of what trn/te split the caller
    # is using), so fit ONCE and apply to both directions' te.
    trainer_edges, trainer_lookup = wpr._fit_merit_lookup(D, "trainer_win_pct_365d")
    jockey_edges, jockey_lookup = wpr._fit_merit_lookup(D, "jockey_win_pct_90d")

    results = {}
    for direction, (trn, te) in [
        ("A: forward (oldest 70% trn, newest 15% te - matches production)",
         (D[D["date"] < D["date"].quantile(0.70)],
          D[D["date"] >= D["date"].quantile(0.85)])),
        ("B: reversed (newest 70% trn, oldest 15% te)",
         (D[D["date"] > D["date"].quantile(0.30)],
          D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        te = te.copy()
        tb_lookup = fit_track_barrier(trn)
        te["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, tb_lookup)
            for trk, dist, bar, fs in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])
        ]
        te["trainer_merit"] = [wpr._merit_term(wpr._merit_bucket(v, trainer_edges), trainer_lookup)
                                for v in te["trainer_win_pct_365d"]]
        te["jockey_merit"] = [wpr._merit_term(wpr._merit_bucket(v, jockey_edges), jockey_lookup)
                               for v in te["jockey_win_pct_90d"]]
        cutoff = trn["date"].min() if "reversed" in direction else trn["date"].max()
        if "reversed" in direction:
            pace_lookup = fit_pace_baseline_reversed(cutoff)
        else:
            pace_lookup = wpr._fit_pace_baseline(FORM_CSV, cutoff)
        te["closing_merit"] = [wpr._closing_merit_term(p, pace_lookup) for p in te["closing_pairs"]]

        scored = te.dropna(subset=["_base"] + wpr.ADJ_TERMS)
        mae = mean_absolute_error(scored["target"], additive_predict(scored))
        print(f"  [{label}] direction {direction}: n_trn={len(trn):,} n_te={len(scored):,} MAE={mae:.4f}")
        results[direction] = mae
    return results


def run():
    try:
        print("=== BASELINE (current STRONG list) ===")
        wpr_void.STRONG = list(ORIGINAL_STRONG)
        t0 = time.time()
        D_base = prepare_frame()
        res_base = held_out_mae_both_directions(D_base, "BASELINE")
        print(f"  baseline done in {time.time() - t0:.0f}s")

        print("\n=== CANDIDATE (STRONG + 11 new incident/health markers) ===")
        wpr_void.STRONG = ORIGINAL_STRONG + NEW_STRONG
        t0 = time.time()
        D_cand = prepare_frame()
        res_cand = held_out_mae_both_directions(D_cand, "CANDIDATE")
        print(f"  candidate done in {time.time() - t0:.0f}s")
    finally:
        wpr_void.STRONG = ORIGINAL_STRONG

    print("\n=== SUMMARY ===")
    for direction in res_base:
        b, c = res_base[direction], res_cand[direction]
        print(f"  {direction}")
        print(f"    baseline={b:.4f}  candidate={c:.4f}  "
              f"{'better' if c < b else 'worse'} ({c - b:+.4f})")
    both_better = all(res_cand[d] < res_base[d] for d in res_base)
    print(f"\n{'BOTH directions improved - clears this codebase own adoption bar.' if both_better else 'NOT both directions improved - per this codebase own standard (every ADJ_TERMS decision required both), this does NOT clear the bar.'}")


if __name__ == "__main__":
    run()
