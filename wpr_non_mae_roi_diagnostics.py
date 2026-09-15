"""
wpr_non_mae_roi_diagnostics.py - user request: test the CURRENT shipped
base rating calc AND every ADJ_TERM using methods other than held-out
MAE and ROI. Three genuinely different lenses, none of which reduce to
either metric:

  PART 1: PROBABILITY CALIBRATION of wprp_blend_prob (the pure WPR-
  softmax win probability, see compute_edge_scores()'s own docstring -
  "blend_prob... softmax of wprp_proj over the whole scored field").
  Reliability table (predicted prob bucket vs actual win rate), Brier
  score, log-loss. Tests whether the probabilities the model outputs
  MEAN what they say (a 20%-chance pick should win ~20% of the time) -
  orthogonal to point-accuracy (MAE) and orthogonal to whether backing
  it beats the market (ROI).

  PART 2: RANKING QUALITY, two measures. (a) per-race Spearman between
  predicted rank and actual finish position. (b) pairwise concordance on
  the winner specifically (for every race, does the runner with the
  higher model probability rank ahead of the actual winner more often
  than chance, restricted to pairs where exactly one runner in the pair
  won) - a cleaner, win-focused analogue of AUC generalised to multi-
  way races, since Spearman over the full order is diluted by minor
  placings nobody bets on.

  PART 3: PER-ADJ_TERM DIRECTIONAL DIAGNOSTIC. For each of the 10
  shipped ADJ_TERMS, isolate its own contribution from wprp_contrib and
  check whether runners it nudges UP actually outperformed what the
  REST of the model (base + every other term) alone would have
  predicted, and by roughly the right amount - a term-level calibration
  check that an aggregate MAE-delta test cannot see (a term could have
  a negligible pooled MAE effect while still being internally sensible,
  or a "significant" MAE delta while pointing the wrong direction on
  average - this tells them apart).

Uses toprate_runners.csv directly (real, live, already-resulted
production data) rather than reconstructing a backtest - this is
diagnosing what actually shipped and actually happened, not a
leak-free-split re-simulation, so it sidesteps any risk of a backtest
methodology bug (like the pop_distance staleness bug found twice
tonight) - the tradeoff is these numbers describe the CURRENT live
config only, not "what if X were different".

NO EM DASHES policy: hyphens only.
"""
import json
import numpy as np
import pandas as pd
from scipy import stats

ADJ_TERMS = ["own_first_up", "own_second_up", "own_long_spell", "track_barrier",
             "closing_merit", "trainer_merit", "jockey_merit", "pace_shape",
             "pop_distance", "pop_going"]


def load():
    df = pd.read_csv("toprate_runners.csv", low_memory=False)
    df = df[df["scratched"].fillna(0).astype(float) != 1]
    df = df[df["resulted"].fillna(0).astype(float) == 1]
    df["field_size"] = df.groupby("race_id")["run_id"].transform("size")
    df = df[df["field_size"] >= 4]
    df["won"] = pd.to_numeric(df["won"], errors="coerce")
    df["finish_position"] = pd.to_numeric(df["finish_position"], errors="coerce")
    df["wprp_proj"] = pd.to_numeric(df["wprp_proj"], errors="coerce")
    df["wpr_actual"] = pd.to_numeric(df["wpr_actual"], errors="coerce")
    df["wprp_blend_prob"] = pd.to_numeric(df["wprp_blend_prob"], errors="coerce")
    df["wprp_rank"] = pd.to_numeric(df["wprp_rank"], errors="coerce")
    return df


def part1_calibration(df):
    print("=" * 78)
    print("PART 1: probability calibration (wprp_blend_prob vs actual win rate)")
    print("=" * 78)
    d = df.dropna(subset=["wprp_blend_prob", "won"]).copy()
    print(f"rows: {len(d):,}")

    brier = float(((d["wprp_blend_prob"] - d["won"]) ** 2).mean())
    eps = 1e-6
    p = d["wprp_blend_prob"].clip(eps, 1 - eps)
    logloss = float(-(d["won"] * np.log(p) + (1 - d["won"]) * np.log(1 - p)).mean())
    print(f"Brier score: {brier:.4f}  (0 = perfect, 0.25 = uninformative 50/50 guesser)")
    print(f"Log-loss:    {logloss:.4f}")

    d["bucket"] = pd.qcut(d["wprp_blend_prob"], 10, duplicates="drop")
    g = d.groupby("bucket", observed=True).agg(
        n=("won", "size"), mean_pred=("wprp_blend_prob", "mean"), actual_rate=("won", "mean"))
    g["se"] = np.sqrt(g["actual_rate"] * (1 - g["actual_rate"]) / g["n"])
    g["gap"] = g["actual_rate"] - g["mean_pred"]
    print("\nreliability table (predicted probability bucket vs realised win rate):")
    pd.set_option("display.width", 140)
    print(g)
    print("\n(a well-calibrated model has actual_rate tracking mean_pred closely, gap near 0,")
    print(" comfortably inside +/- 2*se of the mean_pred line at every bucket)")


def part2_ranking(df):
    print("\n" + "=" * 78)
    print("PART 2: ranking quality (rank correlation + winner concordance)")
    print("=" * 78)
    d = df.dropna(subset=["wprp_rank", "finish_position", "wprp_blend_prob"]).copy()

    rhos = []
    concordant, total_pairs = 0, 0
    for rid, g in d.groupby("race_id"):
        if len(g) < 4:
            continue
        if g["wprp_rank"].nunique() >= 2 and g["finish_position"].nunique() >= 2:
            rho, _ = stats.spearmanr(g["wprp_rank"], g["finish_position"])
            if rho == rho:
                rhos.append(rho)
        winner = g[g["won"] == 1]
        if len(winner) != 1:
            continue
        w_prob = winner["wprp_blend_prob"].iloc[0]
        others = g[g["won"] != 1]["wprp_blend_prob"].dropna()
        for op in others:
            total_pairs += 1
            if w_prob > op:
                concordant += 1
            elif w_prob == op:
                concordant += 0.5

    print(f"races with a computable rank correlation: {len(rhos):,}")
    print(f"mean per-race Spearman rho (predicted rank vs actual finish position): {np.mean(rhos):+.4f}")
    print(f"median: {np.median(rhos):+.4f}")

    conc_rate = concordant / total_pairs if total_pairs else float("nan")
    print(f"\nwinner-vs-nonwinner pairwise concordance: {conc_rate*100:.2f}%  "
          f"(n={total_pairs:,} pairs, 50% = coin flip, 100% = model always rated the "
          f"eventual winner above every beaten runner)")


def part3_per_term(df):
    print("\n" + "=" * 78)
    print("PART 3: per-ADJ_TERM directional diagnostic")
    print("=" * 78)
    d = df.dropna(subset=["wprp_contrib", "wprp_proj", "wpr_actual"]).copy()

    def parse(v):
        try:
            return json.loads(v)
        except Exception:
            return {}

    contrib = d["wprp_contrib"].apply(parse)
    for term in ADJ_TERMS:
        d[f"_c_{term}"] = contrib.apply(lambda c: c.get(term, 0.0) or 0.0)

    print(f"rows: {len(d):,}\n")
    header = f"{'term':<16}{'coverage%':>10}{'mean|val|':>11}{'corr':>9}{'slope':>9}"
    print(header)
    results = []
    for term in ADJ_TERMS:
        col = f"_c_{term}"
        vals = d[col]
        coverage = (vals != 0).mean() * 100
        # residual the rest of the model (base + every OTHER term) leaves
        # unexplained - if this term is well-calibrated, its own value
        # should correlate with this residual, ideally near slope 1.
        rest_pred = d["wprp_proj"] - vals
        resid = d["wpr_actual"] - rest_pred
        valid = vals.notna() & resid.notna() & (vals != 0)
        if valid.sum() < 30:
            print(f"{term:<16}{coverage:>9.1f}%{'(n<30, skipped)':>20}")
            continue
        corr = np.corrcoef(vals[valid], resid[valid])[0, 1]
        slope = np.polyfit(vals[valid], resid[valid], 1)[0]
        print(f"{term:<16}{coverage:>9.1f}%{vals[valid].abs().mean():>11.3f}{corr:>+9.3f}{slope:>+9.3f}")
        results.append((term, coverage, corr, slope, valid.sum()))

    print("\n(corr near 0 or negative = this term's own sign/magnitude does not track what")
    print(" actually happened beyond the rest of the model; slope near 1.0 = well-scaled,")
    print(" slope << 1 = term is directionally right but too aggressive relative to reality,")
    print(" slope >> 1 = term is too timid and could safely be given more weight)")

    print("\nquintile tables for the two largest-coverage terms (most exposure to inspect):")
    for term, coverage, corr, slope, n in sorted(results, key=lambda r: -r[1])[:2]:
        col = f"_c_{term}"
        sub = d[d[col] != 0].copy()
        rest_pred = sub["wprp_proj"] - sub[col]
        sub["resid"] = sub["wpr_actual"] - rest_pred
        sub["q"] = pd.qcut(sub[col], 5, duplicates="drop")
        print(f"\n{term}:")
        print(sub.groupby("q", observed=True).agg(n=("resid", "size"), mean_term_val=(col, "mean"),
                                                     mean_resid=("resid", "mean")))


if __name__ == "__main__":
    df = load()
    part1_calibration(df)
    part2_ranking(df)
    part3_per_term(df)
    print("\nDone.")
