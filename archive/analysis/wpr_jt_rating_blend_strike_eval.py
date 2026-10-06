"""
wpr_jt_rating_blend_strike_eval.py - does blending TopRate's own
jockey_rating/trainer_rating (distinct from the jockey_win_pct_90d/
trainer_win_pct_365d win-percentage stats already tried and rejected in
the earlier blend work) into the ranking improve top-1 strike rate?

WHY THIS EXISTS
  "The TopRate Model Assessment" doc lists "Jockey rating" and "Trainer
  rating" as direct inputs to TopRate's own official model, separate from
  win-percentage trailing stats. toprate_runners.csv has jockey_rating/
  trainer_rating columns (95-100% coverage every month, a healthy live
  field) that have never been tested this session - only the win-pct
  versions were (as part of the earlier, now-reverted blend).

  Cheap to test: like wpr_pfm_blend_strike_eval.py and
  wpr_market_blend_strike_eval.py, everything needed already sits in
  toprate_runners.csv for the current resulted-race window - no
  build_training_frame rebuild required.

METHODOLOGY: per-race z-score blend of wprp_proj against a combined
jockey+trainer rating z-score, swept across blend weights, evaluated for
top-1 strike rate on a chronological half-split, BOTH directions. Only a
weight that beats BOTH pure-model and pure-jt-rating endpoints on BOTH
halves counts as genuine complementary signal (same bar as the market/pfm
blend tests).

USAGE
  python wpr_jt_rating_blend_strike_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
WEIGHT_GRID = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]


def _load():
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["resulted"] = pd.to_numeric(df["resulted"], errors="coerce")
    df["scratched"] = pd.to_numeric(df["scratched"], errors="coerce")
    df["won"] = pd.to_numeric(df["won"], errors="coerce")
    df["wprp_proj"] = pd.to_numeric(df["wprp_proj"], errors="coerce")
    df["jockey_rating"] = pd.to_numeric(df["jockey_rating"], errors="coerce")
    df["trainer_rating"] = pd.to_numeric(df["trainer_rating"], errors="coerce")
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    sub = df[(df["resulted"] == 1) & (df["scratched"] != 1)].dropna(
        subset=["wprp_proj", "jockey_rating", "trainer_rating", "won", "race_id", "date"])
    return sub


def _zscore_per_race(g, col):
    v = g[col].to_numpy(dtype=float)
    std = v.std()
    if std == 0 or len(v) < 2:
        return np.zeros(len(v))
    return (v - v.mean()) / std


def add_blend_scores(data):
    data = data.copy()
    data["jt_rating"] = (data["jockey_rating"] + data["trainer_rating"]) / 2.0
    out_model = np.zeros(len(data))
    out_jt = np.zeros(len(data))
    for _, g in data.groupby("race_id"):
        idx = data.index.get_indexer(g.index)
        out_model[idx] = _zscore_per_race(g, "wprp_proj")
        out_jt[idx] = _zscore_per_race(g, "jt_rating")
    data["model_z"] = out_model
    data["jt_z"] = out_jt
    return data


def top1_strike_rate(data, weight):
    data = data.copy()
    data["blend"] = (1 - weight) * data["model_z"] + weight * data["jt_z"]
    data["rank"] = data.groupby("race_id")["blend"].rank(ascending=False, method="first")
    top1 = data[data["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def run():
    sub = _load()
    sub = add_blend_scores(sub)
    print(f"Total rows: {len(sub):,} ({sub['race_id'].nunique():,} races)")

    mid = sub["date"].quantile(0.5)
    h1, h2 = sub[sub["date"] < mid], sub[sub["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    print(f"{'weight (jt share)':>18s} | {'H1 top-1 strike':>20s} | {'H2 top-1 strike':>20s}")
    results = []
    for w in WEIGHT_GRID:
        r1, k1, n1 = top1_strike_rate(h1, w)
        r2, k2, n2 = top1_strike_rate(h2, w)
        print(f"{w:18.1f} | {k1:4d}/{n1:5d} = {r1:5.2f}%    | {k2:4d}/{n2:5d} = {r2:5.2f}%")
        results.append((w, r1, r2))

    pure_model = results[0]
    pure_jt = results[-1]
    best_h1 = max(results, key=lambda r: r[1])
    best_h2 = max(results, key=lambda r: r[2])
    print(f"\nPure model (w=0.0): H1={pure_model[1]:.2f}%, H2={pure_model[2]:.2f}%")
    print(f"Pure jt_rating (w=1.0): H1={pure_jt[1]:.2f}%, H2={pure_jt[2]:.2f}%")
    print(f"Best weight on H1: {best_h1[0]:.1f} ({best_h1[1]:.2f}%)")
    print(f"Best weight on H2: {best_h2[0]:.1f} ({best_h2[2]:.2f}%)")

    beats_both = (0.0 < best_h1[0] < 1.0) and (0.0 < best_h2[0] < 1.0) and \
        (best_h1[1] > max(pure_model[1], pure_jt[1])) and \
        (best_h2[2] > max(pure_model[2], pure_jt[2]))
    if beats_both:
        print("\nAn INTERMEDIATE blend weight beats both pure model and pure jt_rating on BOTH "
              "halves - real complementary information, worth pursuing.")
    else:
        print("\nNo intermediate weight clearly beats both endpoints on both halves - jt_rating "
              "does not add genuine complementary signal beyond wprp_proj (or beyond whichever "
              "endpoint already wins).")


if __name__ == "__main__":
    run()
