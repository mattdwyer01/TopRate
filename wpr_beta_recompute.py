"""
wpr_beta_recompute.py - fast recompute of price/edge fields after a beta
change (config.json's softmax sharpness), WITHOUT the ~18-minute full
projection backfill.

wpr_price/wpr_rank (project_race) and wprp_blend_prob/rank/price/edge*
(compute_edge_scores) are pure functions of {wprp_proj values already
stored in toprate_runners.csv for that race, beta, market price} - they
do NOT depend on prior_runs/build_features at all. So a beta-only change
never needs the expensive full re-projection (wprp_proj/wprp_base/
wprp_adj are completely unaffected by beta) - only these downstream
price/edge fields need refreshing, across EVERY race (resulted AND
pending), not just resulted ones (unlike wpr_backfill_historical_
projections.py, which only ever needs to touch resulted rows since
that's all the Review tab's accuracy stats use).

Mirrors the exact two scoping conventions already used by
toprate_daily.py so the recomputed numbers are bit-identical to what a
live/backfill run under the new beta would have produced:
  - wpr_price/wpr_rank (compute_wpr_projection's own project_race call):
    softmax over ALL rows in the race group, scratched included (a
    known, pre-existing quirk of this column - not introduced here).
  - wprp_blend_*/wprp_edge* (compute_edge_score): softmax over only
    non-scratched ("active") rows, via wpr.compute_edge_scores() itself
    (not reimplemented) so it's guaranteed identical to the live path.

USAGE
  python wpr_beta_recompute.py

Writes toprate_runners.csv in place. Does NOT rebuild toprate_data.json -
run toprate_daily.py --rebuild-only separately after.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import wpr_projection as wpr
from toprate_daily import load_runners, save_runners


def run():
    print("Loading runners_df...")
    runners_df = load_runners()
    beta = wpr.get_price_beta()
    print(f"Recomputing price/edge fields under beta={beta} for all races...")

    proj_all = pd.to_numeric(runners_df["wprp_proj"], errors="coerce")
    scratched = pd.to_numeric(runners_df.get("scratched"), errors="coerce").fillna(0) == 1
    market_price = (pd.to_numeric(runners_df.get("fixed_win_price"), errors="coerce")
                     .combine_first(pd.to_numeric(runners_df.get("starting_price_sp"), errors="coerce"))
                     .combine_first(pd.to_numeric(runners_df.get("price_top"), errors="coerce")))

    n_races = runners_df["race_id"].nunique()
    n_price = n_blend = 0
    for gi, (race_id, idx) in enumerate(runners_df.groupby("race_id").groups.items()):
        if gi > 0 and gi % 1000 == 0:
            print(f"  ... {gi:,}/{n_races:,} races")

        # --- wpr_price/wpr_rank: ALL rows (scratched included, matching
        # project_race's own scoping - see module docstring) ---
        pv_all = proj_all.loc[idx].to_numpy(dtype=float)
        valid = np.isfinite(pv_all)
        if valid.sum() >= 2:
            pv = pv_all[valid]
            e = np.exp(beta * (pv - pv.max()))
            price = np.minimum(1.0 / (e / e.sum()), 999.0)
            rank = (-pv).argsort().argsort() + 1
            vidx = np.array(idx)[valid]
            runners_df.loc[vidx, "wprp_price"] = np.round(price, 2)
            runners_df.loc[vidx, "wprp_rank"] = rank
            n_price += valid.sum()

        # --- wprp_blend_*/wprp_edge*: active (non-scratched) rows only,
        # via the real compute_edge_scores() so it's bit-identical to the
        # live path (see module docstring) ---
        active_idx = [i for i in idx if not scratched.loc[i]]
        if not active_idx:
            continue
        runners = [{"wprp_proj": proj_all.loc[i], "market_price": market_price.loc[i]}
                   for i in active_idx]
        results = wpr.compute_edge_scores(runners)
        for i, res in zip(active_idx, results):
            if res.get("blend_prob") is not None:
                runners_df.at[i, "wprp_blend_prob"] = res.get("blend_prob")
                runners_df.at[i, "wprp_blend_rank"] = res.get("blend_rank")
                runners_df.at[i, "wprp_blend_price"] = res.get("blend_price")
                n_blend += 1
            else:
                for col in ["wprp_blend_prob", "wprp_blend_rank", "wprp_blend_price"]:
                    runners_df.at[i, col] = None
            if res.get("has_edge"):
                runners_df.at[i, "wprp_edge"] = res.get("edge")
                runners_df.at[i, "wprp_edge_prob"] = res.get("model_prob")
                runners_df.at[i, "wprp_edge_mkt_prob"] = res.get("market_prob")
            else:
                for col in ["wprp_edge", "wprp_edge_prob", "wprp_edge_mkt_prob"]:
                    runners_df.at[i, col] = None

    print(f"Done: {n_price:,} wpr_price/rank rows, {n_blend:,} blend rows recomputed "
          f"across {n_races:,} races.")
    save_runners(runners_df)
    print("Saved toprate_runners.csv")


if __name__ == "__main__":
    run()
