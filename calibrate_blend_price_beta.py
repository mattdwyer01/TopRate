"""
calibrate_blend_price_beta.py - re-derive the softmax beta for the BLEND
score (wprp_proj + trainer_win_pct_365d + jockey_win_pct_90d + pfm_score,
the same edge_score blend compute_edge_scores() already uses for ranking),
and write it into wpr_models/config.json under "edge_score.blend_beta".

WHY
  compute_edge_scores()'s blend_price/blend_prob softmax had NO beta at
  all (implicit beta=1, un-calibrated) - unlike wpr_price's own softmax
  over wprp_proj, which calibrate_price_beta.py properly re-derived
  against real outcomes (grid search + Brier score + held-out
  validation, landing on beta ~0.15-0.20 vs the original hardcoded 0.4).
  This script applies that exact same discipline to the blend score
  instead (user request, Sep 2026, after the blend was found to beat
  wprp_proj alone on both AUC (~0.68 vs ~0.58) and top-1 strike rate
  (~27% vs ~23-25%) in this session's own walk-forward checks - see
  calibrate_edge_score.py's docstring for the full numbers).

  Reuses the ALREADY-FITTED feature means/stds from wpr_models/
  config.json's "edge_score" block (calibrate_edge_score.py's own job) -
  this script only fits beta on top of that existing score, exactly the
  same division of labour calibrate_price_beta.py has with the
  projection model (it doesn't refit projection.joblib either, only
  beta).

  Same "missing wprp_proj forces score=0" rule as compute_edge_scores'
  own _score, for byte-identical behaviour between this calibration and
  what runs in production.

USAGE
  python calibrate_blend_price_beta.py           # report only
  python calibrate_blend_price_beta.py --write   # also update wpr_models/config.json

Descriptive/re-calibration only. Does not touch projection.joblib,
confidence.joblib, or the edge_score means/stds themselves.

NO EM DASHES policy: hyphens only in this file.
"""
import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
CONFIG_PATH = Path("wpr_models") / "config.json"
BETA_GRID = [0.10, 0.15, 0.20, 0.25, 0.30, 0.40, 0.50, 0.70, 1.00,
             1.50, 2.00, 3.00, 4.00, 5.00, 7.00, 10.00]


def _blend_score(row, feats, means, stds):
    wpr_v = row.get("wprp_proj")
    if wpr_v is None or wpr_v != wpr_v:
        return 0.0
    zs = []
    for f in feats:
        v = row.get(f)
        std = stds.get(f, 0.0)
        if v is None or v != v or not std:
            continue
        zs.append((float(v) - means.get(f, 0.0)) / std)
    return float(np.mean(zs)) if zs else 0.0


def _load_resulted(feats, means, stds):
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str},
                     low_memory=False)
    df["resulted"] = pd.to_numeric(df.get("resulted"), errors="coerce")
    df = df[df["resulted"] == 1].copy()
    df["finish_position"] = pd.to_numeric(df.get("finish_position"), errors="coerce")
    df["date"] = pd.to_datetime(df.get("date"), errors="coerce")
    for f in feats:
        df[f] = pd.to_numeric(df.get(f), errors="coerce")
    df = df.dropna(subset=["finish_position", "race_id", "date"])
    df["won"] = (df["finish_position"] == 1).astype(float)
    df["score"] = df.apply(lambda r: _blend_score(r, feats, means, stds), axis=1)
    return df


def _brier(data, beta):
    """Mean squared error between softmax(beta) win prob and actual win,
    across every runner in every race with >= 4 finishers."""
    rows = []
    for rid, g in data.groupby("race_id"):
        if len(g) < 4:
            continue
        sv = g["score"].to_numpy(dtype=float)
        e = np.exp(beta * (sv - sv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    if len(arr) == 0:
        return float("nan")
    return float(((arr["p"] - arr["won"]) ** 2).mean())


def calibrate(write=False):
    if not CONFIG_PATH.exists():
        print(f"{CONFIG_PATH} not found, cannot calibrate.")
        return None
    cfg = json.load(open(CONFIG_PATH))
    edge_cfg = cfg.get("edge_score")
    if not edge_cfg:
        print(f"No edge_score block in {CONFIG_PATH} - run calibrate_edge_score.py "
              "--write first (this script only fits beta on top of its means/stds).")
        return None
    feats, means, stds = edge_cfg["features"], edge_cfg["means"], edge_cfg["stds"]

    d = _load_resulted(feats, means, stds)
    cut = d["date"].quantile(0.70)
    trn, tst = d[d["date"] < cut], d[d["date"] >= cut]
    print(f"resulted races: {d['race_id'].nunique():,}  "
          f"(train < {cut.date()}: {trn['race_id'].nunique():,}, "
          f"held-out: {tst['race_id'].nunique():,})")
    print("\nbeta | train Brier | held-out Brier")
    best_beta, best_brier = None, float("inf")
    for beta in BETA_GRID:
        b_trn, b_tst = _brier(trn, beta), _brier(tst, beta)
        print(f"  beta={beta:.2f}   train {b_trn:.4f}   held-out {b_tst:.4f}")
        if b_trn < best_brier:
            best_brier, best_beta = b_trn, beta

    cur_beta = edge_cfg.get("blend_beta")
    held_out_best = _brier(tst, best_beta)
    held_out_cur = _brier(tst, cur_beta) if cur_beta is not None else _brier(tst, 1.0)
    print(f"\nbest beta (train-selected): {best_beta}")
    print(f"  held-out Brier at best beta: {held_out_best:.4f}")
    print(f"  held-out Brier at {'current config' if cur_beta is not None else 'un-calibrated (beta=1.0)'} "
          f"beta ({cur_beta if cur_beta is not None else 1.0}): {held_out_cur:.4f}")

    if write:
        cfg["edge_score"]["blend_beta"] = float(best_beta)
        json.dump(cfg, open(CONFIG_PATH, "w"), indent=1)
        print(f"\nwrote edge_score.blend_beta {cur_beta} -> {best_beta} to {CONFIG_PATH}")
    return best_beta


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true",
                    help="write the selected beta into wpr_models/config.json")
    args = ap.parse_args()
    calibrate(write=args.write)
