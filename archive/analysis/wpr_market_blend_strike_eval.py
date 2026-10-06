"""
wpr_market_blend_strike_eval.py - does blending the market's own implied
probability INTO the ranking (not just comparing against it afterward)
improve top-1 strike rate?

WHY THIS EXISTS
  TopRate's own official price model (per "The TopRate Model Assessment"
  doc) explicitly lists "the current market price of the horse" as one of
  its regression inputs. Our wprp_proj does NOT use market price as an
  input anywhere - it's built purely from wpr_nett/ewm3/ADJ_TERMS, then
  compared against the market afterward (wprp_edge) as a separate "is this
  a value bet" signal. That design choice is plausibly why the market
  favourite beats our own top pick head-to-head in this project's own
  baseline numbers (32.5% vs 25.4% top-1 strike rate, see chat) - the
  market prices in information (late scratchings, connections' mood,
  insider sentiment) our model never sees.

  This tests the obvious fix: blend proj and the market's own
  (overround-removed) implied probability, per race, at a range of blend
  weights, and see whether any INTERMEDIATE weight beats BOTH pure model
  and pure market - i.e. whether the model carries genuine information
  the market doesn't already have, once combined properly. If the best
  point is just w=1 (pure market), the model adds nothing to picking
  winners beyond what the market already prices in.

  Cheap to test: everything needed (wprp_proj, starting price, won,
  race_id, date) is already sitting in toprate_runners.csv - no model
  rebuild required.

CAVEAT: like every walk-forward test in this project, market favourite
already wins ~32.5% of races vs the model's ~25%, so a HIGH blend weight
will mechanically push strike rate toward the market's own number - that
alone doesn't mean the model has been improved, only that it now agrees
with the market more often. The only genuinely interesting result is an
intermediate weight beating BOTH endpoints (w=0 and w=1), on BOTH
chronological halves independently - proof the two signals are
complementary, not just "the market is a better picker".

USAGE
  python wpr_market_blend_strike_eval.py

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
    df["sp"] = pd.to_numeric(df["starting_price_sp"], errors="coerce")
    df["sp"] = df["sp"].fillna(pd.to_numeric(df["price_top"], errors="coerce"))
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    sub = df[(df["resulted"] == 1) & (df["scratched"] != 1)].dropna(
        subset=["wprp_proj", "sp", "won", "race_id", "date"])
    return sub


def _zscore_per_race(g, col):
    v = g[col].to_numpy(dtype=float)
    std = v.std()
    if std == 0 or len(v) < 2:
        return np.zeros(len(v))
    return (v - v.mean()) / std


def add_blend_scores(data):
    """Per race: z-score wprp_proj, and z-score the overround-removed
    market implied probability (1/sp, normalised to sum to 1 within the
    race, then log so the z-score isn't dominated by extreme longshots)."""
    data = data.copy()
    out_model = np.zeros(len(data))
    out_mkt = np.zeros(len(data))
    for _, g in data.groupby("race_id"):
        idx = g.index
        raw_p = 1.0 / g["sp"].to_numpy(dtype=float)
        norm_p = raw_p / raw_p.sum()
        log_p = np.log(norm_p)
        out_model[data.index.get_indexer(idx)] = _zscore_per_race(g, "wprp_proj")
        gg = g.copy()
        gg["_logp"] = log_p
        out_mkt[data.index.get_indexer(idx)] = _zscore_per_race(gg, "_logp")
    data["model_z"] = out_model
    data["mkt_z"] = out_mkt
    return data


def top1_strike_rate(data, weight):
    data = data.copy()
    data["blend"] = (1 - weight) * data["model_z"] + weight * data["mkt_z"]
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

    print(f"{'weight (market share)':>22s} | {'H1 top-1 strike':>20s} | {'H2 top-1 strike':>20s}")
    results = []
    for w in WEIGHT_GRID:
        r1, k1, n1 = top1_strike_rate(h1, w)
        r2, k2, n2 = top1_strike_rate(h2, w)
        print(f"{w:22.1f} | {k1:4d}/{n1:5d} = {r1:5.2f}%    | {k2:4d}/{n2:5d} = {r2:5.2f}%")
        results.append((w, r1, r2))

    pure_model = results[0]
    pure_mkt = results[-1]
    best_h1 = max(results, key=lambda r: r[1])
    best_h2 = max(results, key=lambda r: r[2])
    print(f"\nPure model (w=0.0): H1={pure_model[1]:.2f}%, H2={pure_model[2]:.2f}%")
    print(f"Pure market (w=1.0): H1={pure_mkt[1]:.2f}%, H2={pure_mkt[2]:.2f}%")
    print(f"Best weight on H1: {best_h1[0]:.1f} ({best_h1[1]:.2f}%)")
    print(f"Best weight on H2: {best_h2[0]:.1f} ({best_h2[2]:.2f}%)")

    intermediate_wins = (0.0 < best_h1[0] < 1.0) and (0.0 < best_h2[0] < 1.0) and \
        (best_h1[1] > pure_mkt[1]) and (best_h2[2] > pure_mkt[2])
    if intermediate_wins:
        print("\nAn INTERMEDIATE blend weight beats pure market on BOTH halves - the model "
              "carries real complementary information beyond what the market already prices "
              "in. Worth pursuing as a genuine ranking change.")
    else:
        print("\nNo intermediate weight clearly beats pure market on both halves - blending in "
              "market price mostly just makes the ranking agree with the market more, rather "
              "than adding new information. Simply leaning toward the market (moving w up) may "
              "still lift strike rate, but that's a different, more limited claim than 'the "
              "model improves on the market'.")


if __name__ == "__main__":
    run()
