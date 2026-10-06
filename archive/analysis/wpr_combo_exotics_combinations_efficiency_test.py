"""One-off scratch analysis: direct follow-up to
wpr_combo_5v10_exotics_capture_test.py, which found capture rates for
boxing the inner5/outer10 Combo pools and every "banker" hybrid in
between but explicitly left the actual bet COST (combinations count)
uncomputed - real user question, 2026-09-19: "How should I structure
exotic bets using the combo scores (within 5 & 10) to enhance strike
rate, but keep total combinations lower". This computes the actual
number of $1-unit combinations each structure needs (not just the avg
pool size) and reports capture rate PER 100 combinations - the real
efficiency metric for "more strike rate per dollar spent", not capture
rate alone (which trivially favours boxing the widest pool every time).

Bet-cost formulas (m = inner5 pool size, n = outer10 pool size for a
given race, m <= n always since inner5 subset of outer10; "boxed" means
backing every ordered arrangement, the standard way TAB combinations are
priced - a keyed/banker structure restricts SOME finishing positions to
the smaller inner5 pool and leaves the rest open to the larger outer10
pool, filled by whichever runners aren't already used in an earlier
position):
  Quinella (order doesn't matter for 2 positions - halves the trifecta-
  style ordered count): pure inner5 = C(m,2); pure outer10 = C(n,2);
  relax-last-1 (1st inner5, 2nd outer10) = m*(n-1) - 1st is ordered
  (inner5-only) but there's no "2nd inner5, 1st outer10" mirror needed
  since quinella itself is unordered - this is deliberately the ordered
  "trifecta-style" count for this ONE hybrid shape (1st restricted,
  2nd not), not equivalent to a boxed quinella of a mixed field.
  Trifecta (order matters - 1st/2nd/3rd distinct): pure inner5 =
  m*(m-1)*(m-2); relax-last-1 (1st&2nd inner5, 3rd outer10) =
  m*(m-1)*(n-2); relax-last-2 (1st inner5, 2nd&3rd outer10) =
  m*(n-1)*(n-2); pure outer10 = n*(n-1)*(n-2).
  First-four: pure inner5 = m*(m-1)*(m-2)*(m-3); relax-last-1/2/3 follow
  the same pattern (each relaxed position multiplies by an outer10 slot
  instead of an inner5 one, always accounting for slots already used by
  earlier, stricter positions); pure outer10 = n*(n-1)*(n-2)*(n-3).
  A race where m or n is too small for a given exotic (e.g. m<3 for a
  trifecta needing all-inner5) contributes 0 combinations and is
  excluded from that structure's own capture-rate denominator too (can't
  place a bet that doesn't have enough runners to fill it).

Same complete-case population as wpr_combo_5v10_exotics_capture_test.py
(2,019 races, currently-shipped 0.50/0.25/0.25 Combo weighting) - read-
only against toprate_runners.csv, writes nothing.
"""
import math

import pandas as pd

CSV = "toprate_runners.csv"

COMPOSITE_WEIGHT_WPR = 0.50
COMPOSITE_WEIGHT_TRR = 0.25
COMPOSITE_WEIGHT_PFM = 0.25
COMBO_INNER_GAP_FROM_TOP = 5
COMPOSITE_MAX_GAP_FROM_TOP = 10


def zscore_rescale(series: pd.Series, target_mean: float, target_std: float) -> pd.Series:
    z = (series - series.mean()) / series.std()
    return target_mean + z * target_std


def perm(n: int, k: int) -> int:
    """n!/(n-k)! - 0 if n < k (not enough runners to fill this exotic)."""
    if n < k:
        return 0
    result = 1
    for i in range(k):
        result *= (n - i)
    return result


def main():
    df = pd.read_csv(CSV, low_memory=False)
    df = df[df["scratched"] != 1]
    wpr_mean, wpr_std = df["wprp_proj"].mean(), df["wprp_proj"].std()

    df["complete"] = df["wprp_proj"].notna() & df["pfm_score"].notna() & df["toprate_rating"].notna()
    race_complete = df.groupby("race_id")["complete"].all()
    complete_race_ids = set(race_complete[race_complete].index)
    cdf = df[df["race_id"].isin(complete_race_ids)].copy()
    cdf = cdf[cdf["resulted"] == 1]
    print(f"Complete-case, resulted races: {cdf['race_id'].nunique()} races, "
          f"{cdf['date'].nunique()} dates, {len(cdf)} runners")

    cdf["pfm_rescaled"] = zscore_rescale(cdf["pfm_score"], wpr_mean, wpr_std)
    cdf["trr_rescaled"] = zscore_rescale(cdf["toprate_rating"], wpr_mean, wpr_std)
    cdf["combo"] = (
        COMPOSITE_WEIGHT_WPR * cdf["wprp_proj"]
        + COMPOSITE_WEIGHT_TRR * cdf["trr_rescaled"]
        + COMPOSITE_WEIGHT_PFM * cdf["pfm_rescaled"]
    )
    cdf["combo_top"] = cdf.groupby("race_id")["combo"].transform("max")
    cdf["combo_gap"] = cdf["combo_top"] - cdf["combo"]
    cdf["in_inner5"] = cdf["combo_gap"] <= COMBO_INNER_GAP_FROM_TOP
    cdf["in_outer10"] = cdf["combo_gap"] <= COMPOSITE_MAX_GAP_FROM_TOP

    pool_sizes = cdf.groupby("race_id").agg(m=("in_inner5", "sum"), n=("in_outer10", "sum"))

    by_place = {}
    for place in [1, 2, 3, 4]:
        rows = cdf[cdf["finish_position"] == place]
        by_place[place] = rows.groupby("race_id")["run_id"].apply(lambda s: s.iloc[0] if len(s) else None).to_dict()
    inner5_lookup = cdf.set_index(["race_id", "run_id"])["in_inner5"]
    outer10_lookup = cdf.set_index(["race_id", "run_id"])["in_outer10"]

    def in_pool(pool_lookup, rid, run_id):
        try:
            return bool(pool_lookup.loc[(rid, run_id)])
        except KeyError:
            return False

    def stats_for(n_places: int, required_pools_of_m: int, cost_fn):
        """required_pools_of_m: how many of the first n_places positions
        require inner5 (the rest require outer10). cost_fn(m, n) -> combos
        for one race."""
        hits, n_capturable, total_combos, n_priced_races = 0, 0, 0, 0
        for rid, row in pool_sizes.iterrows():
            m, n = int(row["m"]), int(row["n"])
            combos = cost_fn(m, n)
            if combos == 0:
                continue
            n_priced_races += 1
            total_combos += combos
            placegetters = [by_place[p].get(rid) for p in range(1, n_places + 1)]
            if any(pg is None for pg in placegetters):
                continue
            n_capturable += 1
            required_pools = [inner5_lookup] * required_pools_of_m + [outer10_lookup] * (n_places - required_pools_of_m)
            if all(in_pool(pool, rid, pg) for pool, pg in zip(required_pools, placegetters)):
                hits += 1
        capture_rate = 100 * hits / n_capturable if n_capturable else float("nan")
        avg_combos = total_combos / n_priced_races if n_priced_races else float("nan")
        efficiency = 100 * capture_rate / avg_combos if avg_combos else float("nan")
        return capture_rate, avg_combos, efficiency, n_priced_races

    print("\n=== QUINELLA (unordered top-2) ===")
    print(f"{'structure':>34}  {'races':>6}  {'capture %':>9}  {'avg combos':>10}  {'capture/100combos':>18}")
    variants = [
        ("inner5 boxed", 2, lambda m, n: math.comb(m, 2) if m >= 2 else 0),
        ("1st inner5, 2nd outer10", 1, lambda m, n: m * (n - 1) if m >= 1 and n >= 2 else 0),
        ("outer10 boxed", 0, lambda m, n: math.comb(n, 2) if n >= 2 else 0),
    ]
    for label, m_positions, cost_fn in variants:
        rate, combos, eff, races = stats_for(2, m_positions, cost_fn)
        print(f"{label:>34}  {races:>6}  {rate:>8.1f}%  {combos:>10.2f}  {eff:>17.2f}")

    print("\n=== TRIFECTA (ordered top-3) ===")
    print(f"{'structure':>34}  {'races':>6}  {'capture %':>9}  {'avg combos':>10}  {'capture/100combos':>18}")
    variants = [
        ("inner5 boxed", 3, lambda m, n: perm(m, 3)),
        ("relax last 1 (2x inner5, 1x outer10)", 2, lambda m, n: m * (m - 1) * (n - 2) if m >= 2 and n >= 3 else 0),
        ("relax last 2 (1x inner5, 2x outer10)", 1, lambda m, n: m * perm(n - 1, 2) if m >= 1 and n >= 3 else 0),
        ("outer10 boxed", 0, lambda m, n: perm(n, 3)),
    ]
    for label, m_positions, cost_fn in variants:
        rate, combos, eff, races = stats_for(3, m_positions, cost_fn)
        print(f"{label:>34}  {races:>6}  {rate:>8.1f}%  {combos:>10.2f}  {eff:>17.2f}")

    print("\n=== FIRST FOUR (ordered top-4) ===")
    print(f"{'structure':>34}  {'races':>6}  {'capture %':>9}  {'avg combos':>10}  {'capture/100combos':>18}")
    variants = [
        ("inner5 boxed", 4, lambda m, n: perm(m, 4)),
        ("relax last 1 (3x inner5, 1x outer10)", 3, lambda m, n: perm(m, 3) * (n - 3) if m >= 3 and n >= 4 else 0),
        ("relax last 2 (2x inner5, 2x outer10)", 2, lambda m, n: m * (m - 1) * perm(n - 2, 2) if m >= 2 and n >= 4 else 0),
        ("relax last 3 (1x inner5, 3x outer10)", 1, lambda m, n: m * perm(n - 1, 3) if m >= 1 and n >= 4 else 0),
        ("outer10 boxed", 0, lambda m, n: perm(n, 4)),
    ]
    for label, m_positions, cost_fn in variants:
        rate, combos, eff, races = stats_for(4, m_positions, cost_fn)
        print(f"{label:>34}  {races:>6}  {rate:>8.1f}%  {combos:>10.2f}  {eff:>17.2f}")


if __name__ == "__main__":
    main()
