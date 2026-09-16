"""
wpr_confidence_weighted_price_test.py - tests a genuinely different way to
calculate wpr_price/wprp_blend_prob: shrink a runner's WPR toward the
field mean by an amount tied to the model's OWN confidence score, before
applying the existing softmax - instead of treating every runner's WPR as
equally trustworthy regardless of how uncertain the model itself is about
that specific runner.

WHY THIS EXISTS (see chat, Sep 2026): every pricing test tonight (beta
grid search, isotonic recalibration, field-size-conditioned beta) treated
the softmax input (wprp_proj) as fixed and only tuned the TRANSFORM. This
is a different lever: wprp_conf (0-100, derived from the q10/q90 quantile
interval width - already computed, already validated, currently UNUSED
in pricing at all) is a real, per-runner signal about how much to trust
that specific WPR number. A concrete real example that motivated this
(session's earlier jockey_merit dig): a jockey on 1-of-2 rides (50% win
rate) got treated identically to one on 50-of-100 rides by a term that
only sees the RATE, not the sample size behind it - the same failure mode
could show up in wprp_proj itself for a lightly-raced horse with a wide
confidence interval but an extreme-looking rating.

MECHANISM: effective_wpr = field_mean + (wpr - field_mean) * (conf/100)^p
  conf=100 (fully confident) -> effective_wpr = wpr (unchanged)
  conf=0   (no confidence)   -> effective_wpr = field_mean (no separation
                                 from the pack, no information asserted)
  p controls how aggressively confidence shrinks - p=1 linear, p>1 only
  discounts genuinely low-confidence runners, p<1 discounts more broadly.
Then the EXISTING softmax (same beta, same formula) runs on effective_wpr
instead of raw wpr - ranking is unaffected only if shrinkage doesn't flip
relative order (it can't within a single runner's own value, but CAN
change relative gaps between runners with different confidence - which
is the whole point: the model asserts less separation when it's less
sure).

METHODOLOGY: same _load_resulted() (fresh wprp_proj/wprp_conf via the
real compute_wpr_projection() entry point), search/held-out date split
like calibrate_price_beta.py, grid over p in {0.5, 1.0, 1.5, 2.0, 999
(999 ~= no shrink, the current baseline)}, selected by held-out Brier.
Reports Brier, the top-1%/top-5% reliability gap (where the real,
smaller residual overconfidence was found earlier tonight), and ROI at
EDGE_THRESHOLDS for baseline vs the best confidence-weighted variant.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from calibrate_price_beta import _load_resulted, CONFIG_PATH
import json

from wpr_bet_selection_post_retrain import report
from wpr_slope_roi_test import EDGE_THRESHOLDS

DAYS_BACK = 90
P_GRID = [0.5, 1.0, 1.5, 2.0, 999.0]  # 999 ~= no shrink (baseline)


def add_effective_wpr(data, p, beta):
    """Per-race: shrink wpr toward the race's own mean by (conf/100)^p,
    then softmax the result at `beta`. p=999 collapses (conf/100)^999 to
    ~0 for any conf<100 - to actually represent "no shrink" (the
    baseline) we special-case p>=999 as a pure passthrough instead,
    since raising a fraction to the 999th power would zero out anything
    less than 100% confidence, the OPPOSITE of "no shrink"."""
    probs = pd.Series(np.nan, index=data.index)
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        wpr = g["wprp_proj"].to_numpy(dtype=float)
        conf = g["wprp_conf"].to_numpy(dtype=float)
        conf = np.clip(np.nan_to_num(conf, nan=50.0), 0, 100)  # missing conf -> neutral 50
        if p >= 999:
            eff = wpr
        else:
            field_mean = wpr.mean()
            shrink = (conf / 100.0) ** p
            eff = field_mean + (wpr - field_mean) * shrink
        e = np.exp(beta * (eff - eff.max()))
        probs.loc[g.index] = e / e.sum()
    return probs


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
    print(f"using shipped beta={cur_beta} (this test isolates the confidence-weighting "
          f"effect, not re-tuning beta itself)")

    cut = d["date"].quantile(0.60)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"search < {cut.date()}: {trn['race_id'].nunique():,} races, "
          f"held-out: {tst['race_id'].nunique():,} races")

    print("\n" + "=" * 78)
    print("GRID: confidence-shrink power p, search vs held-out Brier")
    print("=" * 78)
    search_brier, held_brier, held_probs = {}, {}, {}
    for p in P_GRID:
        trn_p = add_effective_wpr(trn, p, cur_beta)
        tst_p = add_effective_wpr(tst, p, cur_beta)
        sb = brier(trn_p.dropna(), trn.loc[trn_p.dropna().index, "won"])
        hb = brier(tst_p.dropna(), tst.loc[tst_p.dropna().index, "won"])
        search_brier[p] = sb
        held_brier[p] = hb
        held_probs[p] = tst_p
        label = "no-shrink baseline" if p >= 999 else f"p={p}"
        print(f"  {label:20s}  search Brier={sb:.4f}   held-out Brier={hb:.4f}")

    best_p = min([p for p in P_GRID if p < 999], key=lambda p: search_brier[p])
    baseline_p = 999.0
    print(f"\nbest confidence-weighted p (search-selected, excluding baseline): {best_p}")
    print(f"  held-out Brier: baseline={held_brier[baseline_p]:.4f}   "
          f"confidence-weighted (p={best_p})={held_brier[best_p]:.4f}")

    print("\n" + "=" * 78)
    print("TOP-TAIL RELIABILITY: baseline vs best confidence-weighted variant")
    print("=" * 78)
    for name, p in [("baseline", baseline_p), (f"conf-weighted p={best_p}", best_p)]:
        probs = held_probs[p].dropna()
        sub = tst.loc[probs.index].copy()
        sub["p"] = probs
        print(f"\n-- {name} --")
        for top_pct in (0.05, 0.02, 0.01):
            thr = sub["p"].quantile(1 - top_pct)
            top = sub[sub["p"] >= thr]
            print(f"  top {top_pct*100:.0f}% (n={len(top)}): pred={top['p'].mean():.3f}  "
                  f"actual={top['won'].mean():.3f}  gap={top['p'].mean()-top['won'].mean():+.3f}")

    print("\n" + "=" * 78)
    print("ROI CHECK: baseline vs best confidence-weighted variant")
    print("=" * 78)
    for name, p in [("baseline", baseline_p), (f"conf-weighted p={best_p}", best_p)]:
        probs = held_probs[p].dropna()
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
        for thr in EDGE_THRESHOLDS:
            report(sub[sub["edge_wpr"] >= thr], f"edge>={thr:.2f}")


if __name__ == "__main__":
    run()
