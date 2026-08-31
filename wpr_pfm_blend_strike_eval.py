"""
wpr_pfm_blend_strike_eval.py - does blending pfm_score (TopRate's own
"Form Factor Assessment" - see the Form Factor Assessment Model doc) with
wprp_proj improve top-1 strike rate over either alone?

WHY THIS EXISTS
  pfm_score/pfm_score_rank is TopRate's own separate machine-learning
  "Form Factor" model (rating profile strength via ratings, form, trainer/
  jockey, and expected in-running position - explicitly NOT using market
  price). It has only been populated in our scrape since ~24 July 2026
  (0% coverage before, ramping to ~92% by August - see chat; the older
  pf_ai_score/pf_ai_rank columns are DEAD, no code writes them any more,
  pfm_score is the live replacement).

  On the population where both exist: pfm_score_rank==1 strike rate
  (27.4%) BEATS wprp_rank==1 on the exact same races (25.4%), and the two
  models pick the SAME top horse only 56.7% of the time - real
  disagreement, not redundant signal. That's a strong prior that a blend
  could beat both.

METHODOLOGY: identical in spirit to wpr_market_blend_strike_eval.py -
per-race z-score both signals, blend at a range of weights, check top-1
strike rate on a chronological half-split, both directions. Small sample
(only ~6 weeks, ~1,925 races) since pfm_score coverage only started in
July - treat any result here as suggestive, not final, until more weeks
of coverage accumulate.

USAGE
  python wpr_pfm_blend_strike_eval.py

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
    df["pfm_score"] = pd.to_numeric(df["pfm_score"], errors="coerce")
    df["wprp_proj"] = pd.to_numeric(df["wprp_proj"], errors="coerce")
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    sub = df[(df["resulted"] == 1) & (df["scratched"] != 1)].dropna(
        subset=["won", "pfm_score", "wprp_proj", "race_id", "date"])
    return sub


def _zscore_per_race(g, col):
    v = g[col].to_numpy(dtype=float)
    std = v.std()
    if std == 0 or len(v) < 2:
        return np.zeros(len(v))
    return (v - v.mean()) / std


def add_blend_scores(data):
    data = data.copy()
    out_model = np.zeros(len(data))
    out_pfm = np.zeros(len(data))
    for _, g in data.groupby("race_id"):
        idx = g.index
        pos = data.index.get_indexer(idx)
        out_model[pos] = _zscore_per_race(g, "wprp_proj")
        out_pfm[pos] = _zscore_per_race(g, "pfm_score")
    data["model_z"] = out_model
    data["pfm_z"] = out_pfm
    return data


def top1_strike_rate(data, weight):
    data = data.copy()
    data["blend"] = (1 - weight) * data["model_z"] + weight * data["pfm_z"]
    data["rank"] = data.groupby("race_id")["blend"].rank(ascending=False, method="first")
    top1 = data[data["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def run():
    sub = _load()
    sub = add_blend_scores(sub)
    print(f"Total rows: {len(sub):,} ({sub['race_id'].nunique():,} races), "
          f"{sub['date'].min().date()} to {sub['date'].max().date()}")

    mid = sub["date"].quantile(0.5)
    h1, h2 = sub[sub["date"] < mid], sub[sub["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    print(f"{'weight (pfm share)':>20s} | {'H1 top-1 strike':>20s} | {'H2 top-1 strike':>20s}")
    results = []
    for w in WEIGHT_GRID:
        r1, k1, n1 = top1_strike_rate(h1, w)
        r2, k2, n2 = top1_strike_rate(h2, w)
        print(f"{w:20.1f} | {k1:4d}/{n1:5d} = {r1:5.2f}%    | {k2:4d}/{n2:5d} = {r2:5.2f}%")
        results.append((w, r1, r2))

    pure_model = results[0]
    pure_pfm = results[-1]
    best_h1 = max(results, key=lambda r: r[1])
    best_h2 = max(results, key=lambda r: r[2])
    print(f"\nPure wprp_proj (w=0.0): H1={pure_model[1]:.2f}%, H2={pure_model[2]:.2f}%")
    print(f"Pure pfm_score (w=1.0): H1={pure_pfm[1]:.2f}%, H2={pure_pfm[2]:.2f}%")
    print(f"Best weight on H1: {best_h1[0]:.1f} ({best_h1[1]:.2f}%)")
    print(f"Best weight on H2: {best_h2[0]:.1f} ({best_h2[1]:.2f}%)")

    beats_both = (0.0 < best_h1[0] < 1.0) and (0.0 < best_h2[0] < 1.0) and \
        (best_h1[1] > max(pure_model[1], pure_pfm[1])) and \
        (best_h2[2] > max(pure_model[2], pure_pfm[2]))
    if beats_both:
        print("\nAn intermediate blend weight beats BOTH signals alone on BOTH halves - real "
              "complementary information, worth pursuing as a genuine ranking change.")
    else:
        print("\nNo intermediate weight clearly beats both pure signals on both halves. Small "
              "sample (~6 weeks) - re-run this once more weeks of pfm_score coverage "
              "accumulate before drawing a firm conclusion either way.")


if __name__ == "__main__":
    run()
