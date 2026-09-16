"""
wpr_confidence_gated_price_test.py - follow-up to wpr_confidence_weighted_
price_test.py, which found blanket confidence-weighting (shrink EVERY
runner toward the field mean by (conf/100)^p) genuinely fixed the top-1%
overconfidence gap (0.068 -> 0.024) but made held-out Brier and ROI worse
almost everywhere else - it was discounting plenty of well-supported,
reasonably-confident runners that never had a problem in the first place.

THIS VERSION GATES THE SHRINK: only runners BELOW a confidence threshold
get discounted at all; anyone at or above it keeps their raw WPR
unchanged, exactly like the current live pricing. Within the gated zone,
the shrink ramps linearly from full effect at conf=0 to no effect at
conf=threshold (continuous at the boundary, no discontinuity):

  shrink_factor = 1.0                      if conf >= threshold
                = (conf / threshold)        if conf <  threshold
  effective_wpr = field_mean + (wpr - field_mean) * shrink_factor

This should, in principle, only touch the minority of runners that
actually have a wide confidence interval (typically lightly-raced horses,
gear-change debuts, etc) while leaving the well-supported majority of the
field byte-identical to today's pricing - avoiding the blanket version's
failure mode of degrading rows that were never a problem.

METHODOLOGY: same as the blanket version - _load_resulted() (fresh
wprp_proj/wprp_conf), search/held-out date split, grid over threshold in
{20, 30, 40, 50} (plus baseline = threshold 0, meaning the gate never
opens = identical to today's pricing), selected by held-out Brier.
Reports Brier, top-tail reliability, ROI, and ADDITIONALLY the fraction
of rows the gate actually touches at the winning threshold (to confirm
it really is a minority, not accidentally re-creating the blanket
version).

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted, CONFIG_PATH
import json

from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import EDGE_THRESHOLDS

DAYS_BACK = 90
THRESHOLD_GRID = [20.0, 30.0, 40.0, 50.0, 0.0]  # 0.0 = gate never opens = baseline


def add_effective_wpr(data, threshold, beta):
    probs = pd.Series(np.nan, index=data.index)
    touched = pd.Series(False, index=data.index)
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        wpr = g["wprp_proj"].to_numpy(dtype=float)
        conf = g["wprp_conf"].to_numpy(dtype=float)
        conf = np.clip(np.nan_to_num(conf, nan=50.0), 0, 100)
        if threshold <= 0:
            eff = wpr
        else:
            field_mean = wpr.mean()
            gated = conf < threshold
            shrink = np.where(gated, conf / threshold, 1.0)
            eff = field_mean + (wpr - field_mean) * shrink
            touched.loc[g.index] = gated
        e = np.exp(beta * (eff - eff.max()))
        probs.loc[g.index] = e / e.sum()
    return probs, touched


def brier(p, won):
    return float(((p - won) ** 2).mean())


def run():
    print(f"Loading resulted races (fresh wprp_proj/wprp_conf via compute_wpr_projection, "
          f"{DAYS_BACK} days back)...")
    d = _load_resulted(days_back=DAYS_BACK)
    d = d.dropna(subset=["wprp_proj", "wprp_conf", "won", "race_id", "date"])
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races, "
          f"{d['date'].min()} .. {d['date'].max()}")

    cur_beta = 0.15
    if CONFIG_PATH.exists():
        cur_beta = json.load(open(CONFIG_PATH)).get("beta", 0.15)
    print(f"using shipped beta={cur_beta}")

    cut = d["date"].quantile(0.60)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"search < {cut.date()}: {trn['race_id'].nunique():,} races, "
          f"held-out: {tst['race_id'].nunique():,} races")

    print("\n" + "=" * 78)
    print("GRID: confidence gate threshold, search vs held-out Brier")
    print("=" * 78)
    search_brier, held_brier, held_probs, held_touched = {}, {}, {}, {}
    for thr in THRESHOLD_GRID:
        trn_p, _ = add_effective_wpr(trn, thr, cur_beta)
        tst_p, tst_touched = add_effective_wpr(tst, thr, cur_beta)
        valid_trn = trn_p.dropna()
        valid_tst = tst_p.dropna()
        sb = brier(valid_trn, trn.loc[valid_trn.index, "won"])
        hb = brier(valid_tst, tst.loc[valid_tst.index, "won"])
        search_brier[thr] = sb
        held_brier[thr] = hb
        held_probs[thr] = tst_p
        held_touched[thr] = tst_touched
        pct_touched = tst_touched.loc[valid_tst.index].mean() * 100
        label = "baseline (gate closed)" if thr <= 0 else f"threshold={thr:.0f}"
        print(f"  {label:24s}  search Brier={sb:.4f}   held-out Brier={hb:.4f}   "
              f"gate touches {pct_touched:.1f}% of held-out rows")

    best_thr = min([t for t in THRESHOLD_GRID if t > 0], key=lambda t: search_brier[t])
    baseline_thr = 0.0
    print(f"\nbest gate threshold (search-selected, excluding baseline): {best_thr}")
    print(f"  held-out Brier: baseline={held_brier[baseline_thr]:.4f}   "
          f"gated (threshold={best_thr})={held_brier[best_thr]:.4f}")

    print("\n" + "=" * 78)
    print("TOP-TAIL RELIABILITY: baseline vs best gated variant")
    print("=" * 78)
    for name, thr in [("baseline", baseline_thr), (f"gated threshold={best_thr}", best_thr)]:
        probs = held_probs[thr].dropna()
        sub = tst.loc[probs.index].copy()
        sub["p"] = probs
        print(f"\n-- {name} --")
        for top_pct in (0.05, 0.02, 0.01):
            top_thr = sub["p"].quantile(1 - top_pct)
            top = sub[sub["p"] >= top_thr]
            print(f"  top {top_pct*100:.0f}% (n={len(top)}): pred={top['p'].mean():.3f}  "
                  f"actual={top['won'].mean():.3f}  gap={top['p'].mean()-top['won'].mean():+.3f}")

    print("\n" + "=" * 78)
    print("ROI CHECK: baseline vs best gated variant")
    print("=" * 78)
    for name, thr in [("baseline", baseline_thr), (f"gated threshold={best_thr}", best_thr)]:
        probs = held_probs[thr].dropna()
        sub = tst.loc[probs.index].copy()
        sub["p"] = probs
        sp = pd.to_numeric(sub["fixed_win_price"], errors="coerce")
        sp_fb = pd.to_numeric(sub["starting_price_sp"], errors="coerce")
        sub["sp"] = sp.fillna(sp_fb)
        sub = sub.dropna(subset=["sp"])
        sub = sub[sub["sp"] > 1.0]
        sub["mkt_prob"] = sub.groupby("race_id")["sp"].transform(lambda x: (1 / x) / (1 / x).sum())
        sub["edge_wpr"] = sub["p"] - sub["mkt_prob"]
        print(f"\n-- {name} --  n={len(sub):,}")
        for thr2 in EDGE_THRESHOLDS:
            report(sub[sub["edge_wpr"] >= thr2], f"edge>={thr2:.2f}")


if __name__ == "__main__":
    run()
