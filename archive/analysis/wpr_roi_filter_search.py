"""
wpr_roi_filter_search.py - "what other rules can we apply to bring ROI
closer to breakeven?" follow-up to wpr_tiered_base_roi_test.py, which
confirmed the new tiered base (PR #173) still loses money at every edge
threshold tested so far (edge>=0.05/0.10/0.20, price<=$26).

Tests a shortlist of additional, well-motivated filters ON TOP of the
edge>=0.05 and edge>=0.10 base filters, using the SAME pooled held-out
K=4-fold scored data as wpr_tiered_base_roi_test.py's NEW (tiered) model
run (reconstructed here identically, not reusing a cached object):

  1. TIGHTER PRICE CAPS ($8/$10/$15/$20, vs the existing $26): horse
     racing markets have a well-documented favourite-longshot bias (longer
     prices are systematically overbet by the public, so bookies can
     shade them even further from fair value) - a model that likes a
     longshot for a "big edge" may just be walking into that bias, worse
     the longer the price.
  2. MARKET-RANK AGREEMENT (only bet when the pick is ALSO the market's
     rank-1/rank-2/rank-3 by price, not just when it clears an edge
     threshold): targets this session's own earlier "selection effect"
     finding - backing disagreement with a more accurate market mostly
     selects for the model's own estimation noise, not real information.
     A pick the market also rates highly, that the model likes EVEN MORE,
     is a different (more plausible) kind of signal than a pick the
     market has drifted out to $15 that the model still likes.
  3. MINIMUM ABSOLUTE model_prob FLOOR (>=0.10/0.15/0.20): a relative
     edge (model_prob - market_prob) can be "big" in relative terms while
     both probabilities are tiny (e.g. 3% vs 1.5%) - a pure longshot bet
     dressed up as a large edge. Requiring a floor on the model's own
     absolute confidence filters these out.
  4. FIELD SIZE bands (<=8 / 9-12 / >=13): smaller fields concentrate
     probability mass on fewer runners (less market noise to exploit but
     also less room for the model to disagree profitably); worth checking
     directly rather than assuming a direction.

Each filter is applied ALONE (on top of the edge threshold) first, then
the single best-looking one or two are combined, to see whether combining
compounds the improvement or just shrinks the sample into noise.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_tiered_base_roi_test import (
    N_FOLDS, PRICE_CAP, new_base, fit_and_score,
)
from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak
from wpr_signal_strike_margin_combo_test import merge_margin
from wpr_bet_selection_post_retrain import report
import wpr_projection as wpr

EDGE_THRESHOLDS = [0.05, 0.10]
PRICE_CAPS = [8.0, 10.0, 15.0, 20.0, 26.0]
PROB_FLOORS = [0.0, 0.10, 0.15, 0.20]
MARKET_RANK_MAX = [1, 2, 3, None]
FIELD_SIZE_BANDS = [("<=8", lambda f: f["field_size"] <= 8),
                    ("9-12", lambda f: (f["field_size"] >= 9) & (f["field_size"] <= 12)),
                    (">=13", lambda f: f["field_size"] >= 13),
                    ("all", lambda f: pd.Series(True, index=f.index))]


def build_pooled():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = merge_margin(full)
    non_pop_terms = [t for t in wpr.ADJ_TERMS
                     if t not in ("track_barrier", "closing_merit", "trainer_merit", "jockey_merit")]
    full = full.dropna(subset=["target", "career_avg"] + non_pop_terms +
                        ["barrier", "field_size", "track", "cur_distance"])
    sp = pd.to_numeric(full["fixed_win_price"], errors="coerce")
    sp_fallback = pd.to_numeric(full["starting_price_sp"], errors="coerce")
    full["sp"] = sp.fillna(sp_fallback)
    full = full.dropna(subset=["sp"])
    full = full[full["sp"] > 1.0]
    full = full.sort_values("date").reset_index(drop=True)
    fold_edges = np.array_split(np.arange(len(full)), N_FOLDS)
    full["_fold"] = -1
    for i, idx in enumerate(fold_edges):
        full.loc[idx, "_fold"] = i

    all_test = []
    for i in range(N_FOLDS):
        test = full[full["_fold"] == i]
        train = full[full["_fold"] != i]
        scored, mae, beta = fit_and_score(train, test, new_base, "NEW")
        all_test.append(scored)
        print(f"  fold {i}: MAE={mae:.4f}  beta={beta}")
    pooled = pd.concat(all_test, ignore_index=True)

    def _mkt_rank(g):
        return g["sp"].rank(method="min")

    pooled["mkt_rank"] = pooled.groupby("race_id", group_keys=False).apply(_mkt_rank)
    return pooled


def run():
    print("Rebuilding pooled held-out scored data (NEW tiered base, same as wpr_tiered_base_roi_test.py)...")
    pooled = build_pooled()
    print(f"Pooled rows: {len(pooled):,}")

    for thr in EDGE_THRESHOLDS:
        base = pooled[pooled["edge"] >= thr]
        print(f"\n{'='*100}\nBASELINE: edge>={thr:.2f}, price<=${PRICE_CAP:.0f} (matches wpr_tiered_base_roi_test.py)\n{'='*100}")
        report(base[base["sp"] <= PRICE_CAP], "baseline")

        print(f"\n--- 1. TIGHTER PRICE CAPS (edge>={thr:.2f}) ---")
        for cap in PRICE_CAPS:
            report(base[base["sp"] <= cap], f"price<=${cap:.0f}")

        print(f"\n--- 2. MARKET-RANK AGREEMENT (edge>={thr:.2f}, price<=${PRICE_CAP:.0f}) ---")
        capped = base[base["sp"] <= PRICE_CAP]
        for max_rank in MARKET_RANK_MAX:
            sub = capped if max_rank is None else capped[capped["mkt_rank"] <= max_rank]
            label = f"mkt_rank<={max_rank}" if max_rank else "no rank filter"
            report(sub, label)

        print(f"\n--- 3. MINIMUM model_prob FLOOR (edge>={thr:.2f}, price<=${PRICE_CAP:.0f}) ---")
        for floor in PROB_FLOORS:
            sub = capped[capped["model_prob"] >= floor]
            report(sub, f"model_prob>={floor:.2f}")

        print(f"\n--- 4. FIELD SIZE bands (edge>={thr:.2f}, price<=${PRICE_CAP:.0f}) ---")
        for label, fn in FIELD_SIZE_BANDS:
            sub = capped[fn(capped)]
            report(sub, f"field_size {label}")

    print(f"\n{'='*100}\nBEST-LOOKING COMBINATIONS (edge>=0.05, mkt_rank<=2, tighter price cap)\n{'='*100}")
    base = pooled[pooled["edge"] >= 0.05]
    for cap in [10.0, 15.0, 20.0, 26.0]:
        for max_rank in [1, 2, 3]:
            sub = base[(base["sp"] <= cap) & (base["mkt_rank"] <= max_rank)]
            report(sub, f"price<=${cap:.0f}, mkt_rank<={max_rank}")

    print("\nSame caveats as always: leak-free-for-wpr_nett K-fold, but one dataset/attempt. Testing many "
          "filter combinations at once raises real multiple-comparisons risk - a filter that looks best "
          "here is a hypothesis for a future walk-forward period, not a result to ship blindly.")


if __name__ == "__main__":
    run()
