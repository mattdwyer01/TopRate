"""
calibrate_price_beta.py - re-derive the wprp_price softmax beta from real
resulted-race outcomes, and write it into wpr_models/config.json.

WHY
  project_race() turns projected WPR into an implied win probability via a
  softmax: p = exp(beta * (wpr - wpr.max())) / sum(...). beta controls how
  much win probability separation a given WPR gap implies. It was set to
  0.4 as a fixed constant when the model was built and never re-derived
  against actual results.

  A calibration check against resulted races (see margin_analysis.py's
  neighbour, this script) found beta=0.4 badly overconfident on the
  model's own biggest favourites: implied win probability ~49% for its
  top decile of picks, actual win rate ~27%. A grid search minimising
  Brier score against real outcomes, validated on a held-out date split
  (first 70% of resulted races to search, last 30% to verify), landed at
  beta ~0.15-0.20 with a clearly better held-out Brier score (~0.090 vs
  ~0.096 at beta=0.4) and a near-flat calibration table across deciles.

  This does NOT touch the WPR projection model itself (projection.joblib,
  confidence.joblib, or the projected WPR numbers/ranking) - only the
  softmax parameter that converts a projected WPR gap into a displayed
  price/probability. Ranking is unaffected (softmax is rank-preserving for
  any beta > 0); only the price numbers change.

  WHY wprp_proj IS RECOMPUTED, NOT READ FROM toprate_runners.csv (Sep 2026)
  compute_wpr_projection() in toprate_daily.py only ever (re)computes
  wprp_proj for the day just fetched - it never retroactively rewrites
  historical rows (by design, so the Review tab's predicted-vs-actual
  accuracy audit reflects what was ACTUALLY predicted at the time, not a
  hindsight-revised number). So after any model change (like adding
  trainer_merit/jockey_merit), toprate_runners.csv's wprp_proj column
  stays stale for nearly all of history until enough new days accumulate
  under the new model - reading it directly here would calibrate beta
  against the OLD model almost entirely. _load_resulted() instead
  recomputes wprp_proj for every resulted row using the CURRENTLY SHIPPED
  config.json (same convention already used for calibrate_edge_score.py's
  means/stds: fit population artifacts once, apply to all data, on the
  basis that walk-forward validation already confirmed the approach
  generalizes - see wpr_trainer_jockey_adj_strike_eval.py). This is slower
  (rebuilds the full training frame, ~5-10 min) than the old direct CSV
  read, acceptable for a script meant to be re-run quarterly, not daily.

USAGE
  python calibrate_price_beta.py           # report only
  python calibrate_price_beta.py --write   # also update wpr_models/config.json

Descriptive/re-calibration only. No change to projection.joblib or
confidence.joblib.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
CONFIG_PATH = Path("wpr_models") / "config.json"
BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40]


def _load_resulted():
    from wpr_bet_selection_post_retrain import build_new_proj_frame
    df = build_new_proj_frame()
    df = df.dropna(subset=["wprp_proj", "won", "race_id", "date"])
    return df


def _brier(data, beta):
    """Mean squared error between softmax(beta) win prob and actual win,
    across every runner in every race with >= 4 finishers."""
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    if len(arr) == 0:
        return float("nan")
    return float(((arr["p"] - arr["won"]) ** 2).mean())


def calibrate(write=False):
    d = _load_resulted()
    cut = d["date"].quantile(0.70)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"resulted races: {d['race_id'].nunique():,}  "
          f"(train < {cut.date()}: {trn['race_id'].nunique():,}, "
          f"held-out: {tst['race_id'].nunique():,})")
    print("\nbeta | train Brier | held-out Brier")
    best_beta, best_brier = None, float("inf")
    for beta in BETA_GRID:
        b_trn, b_tst = _brier(trn, beta), _brier(tst, beta)
        flag = ""
        print(f"  beta={beta:.2f}   train {b_trn:.4f}   held-out {b_tst:.4f}{flag}")
        if b_trn < best_brier:
            best_brier, best_beta = b_trn, beta

    cur_beta = None
    if CONFIG_PATH.exists():
        cur_beta = json.load(open(CONFIG_PATH)).get("beta")
    held_out_best = _brier(tst, best_beta)
    held_out_cur = _brier(tst, cur_beta) if cur_beta is not None else None
    print(f"\nbest beta (train-selected): {best_beta}")
    print(f"  held-out Brier at best beta: {held_out_best:.4f}")
    if held_out_cur is not None:
        print(f"  held-out Brier at current config beta ({cur_beta}): "
              f"{held_out_cur:.4f}")

    if write:
        if not CONFIG_PATH.exists():
            print(f"\n{CONFIG_PATH} not found, cannot write.")
            return best_beta
        cfg = json.load(open(CONFIG_PATH))
        old = cfg.get("beta")
        cfg["beta"] = float(best_beta)
        json.dump(cfg, open(CONFIG_PATH, "w"), indent=1)
        print(f"\nwrote beta {old} -> {best_beta} to {CONFIG_PATH}")
    return best_beta


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true",
                    help="write the selected beta into wpr_models/config.json")
    args = ap.parse_args()
    calibrate(write=args.write)
