"""One-off scratch analysis: does ordering/selecting runners by a COMPOSITE
score (blending projected WPR with form factor and TopRate rating) capture
more actual race winners within a "gap from top" band than WPR alone?
Real user question, 2026-09-19: "Can we order race tab by a different
score (perhaps a combo of wpr, form factor & toprate rating), so that we
are getting as many winners as possible within 5 wpr (or whatever our new
score is)".

This is a DIFFERENT question from every prior sweep this session: those
all measured betting-rule ROI/win% under the tracker's own solo-only
population; this measures a plain "is the winner in the shortlist"
capture rate against RACE FIELD SIZE, independent of the tracker's
jockey/price/speed_map filters entirely - it's about the underlying
ranking signal itself, not the betting rule built on top of it.

Read-only against toprate_runners.csv - writes nothing. Not gated by
speed_map (unlike every tracker sweep this session) so the usable window
is set by pfm_score's own rollout instead (~2026-08-16 onward, vs
speed_map's 2026-08-22) - checked directly, not assumed.

Methodology: complete-case only (a race is included only if EVERY
non-scratched runner has wprp_proj, pfm_score, AND toprate_rating - avoids
asymmetric treatment of runners with partial data, a real risk given
pfm_score's ~70-95% coverage in this window, unlike wprp_proj's ~97%).
Each candidate's non-WPR components are z-scored against their OWN full-
population mean/std (computed once, printed below) and rescaled onto
WPR's own mean/std, so a "gap of 5" carries roughly the same intuitive
meaning across every score tested, not just the WPR-only baseline.

For each score and gap threshold T: pool_size(T) = avg number of
non-scratched runners per race with (top_score - own_score) <= T;
capture_rate(T) = fraction of races where the ACTUAL winner is in that
pool. The real test isn't the raw capture rate (a looser threshold always
captures more, trivially) - it's whether a composite beats WPR-alone's
capture rate AT THE SAME pool size (i.e., a more efficient shortlist, not
just a bigger one).
"""
import pandas as pd

CSV = "toprate_runners.csv"


def zscore_rescale(series: pd.Series, target_mean: float, target_std: float) -> pd.Series:
    z = (series - series.mean()) / series.std()
    return target_mean + z * target_std


def main():
    df = pd.read_csv(CSV, low_memory=False)
    df = df[df["scratched"] != 1]

    wpr_mean, wpr_std = df["wprp_proj"].mean(), df["wprp_proj"].std()
    print(f"Population stats (all non-scratched rows): wprp_proj mean={wpr_mean:.2f} std={wpr_std:.2f}, "
          f"pfm_score mean={df['pfm_score'].mean():.2f} std={df['pfm_score'].std():.2f}, "
          f"toprate_rating mean={df['toprate_rating'].mean():.2f} std={df['toprate_rating'].std():.2f}")

    # Complete-case races: every non-scratched runner has all 3 fields.
    df["complete"] = df["wprp_proj"].notna() & df["pfm_score"].notna() & df["toprate_rating"].notna()
    race_complete = df.groupby("race_id")["complete"].all()
    complete_race_ids = set(race_complete[race_complete].index)
    cdf = df[df["race_id"].isin(complete_race_ids)].copy()
    cdf = cdf[cdf["resulted"] == 1]  # only races with a known outcome
    print(f"Complete-case, resulted races: {cdf['race_id'].nunique()} races, "
          f"{cdf['date'].nunique()} dates ({cdf['date'].min()} to {cdf['date'].max()}), "
          f"{len(cdf)} runners")

    cdf["pfm_rescaled"] = zscore_rescale(cdf["pfm_score"], wpr_mean, wpr_std)
    cdf["trr_rescaled"] = zscore_rescale(cdf["toprate_rating"], wpr_mean, wpr_std)

    scores = {
        "WPR only (baseline)": cdf["wprp_proj"],
        "Equal blend (WPR+pfm+trr)/3": (cdf["wprp_proj"] + cdf["pfm_rescaled"] + cdf["trr_rescaled"]) / 3,
        "WPR-weighted (60/20/20)": 0.6 * cdf["wprp_proj"] + 0.2 * cdf["pfm_rescaled"] + 0.2 * cdf["trr_rescaled"],
        "WPR + pfm only (avg)": (cdf["wprp_proj"] + cdf["pfm_rescaled"]) / 2,
        "WPR + trr only (avg)": (cdf["wprp_proj"] + cdf["trr_rescaled"]) / 2,
    }

    for label, score in scores.items():
        cdf["_score"] = score
        cdf["_top"] = cdf.groupby("race_id")["_score"].transform("max")
        cdf["_gap"] = cdf["_top"] - cdf["_score"]
        print(f"\n=== {label} ===")
        for T in [3, 4, 5, 6, 8, 10]:
            in_pool = cdf["_gap"] <= T
            pool_size = in_pool.groupby(cdf["race_id"]).sum().mean()
            winners = cdf[cdf["won"] == 1]
            capture_rate = (winners["_gap"] <= T).mean()
            print(f"  gap<={T:>2}: avg pool size={pool_size:5.2f}  winner capture rate={100*capture_rate:5.1f}%  "
                  f"(n races with winner={len(winners)})")

    # Gap-threshold pool sizes shrink under any averaged/blended score
    # purely from variance reduction (averaging two z-matched variables
    # narrows the spread), which confounds a same-T comparison above -
    # a blend can look "worse" at a given T just because its whole
    # distribution compressed, not because it ranks worse. A fixed TOP-K
    # per race sidesteps that confound entirely: every score gets exactly
    # the same number of candidates per race, so capture rate alone
    # decides which ranking is more efficient. (Kept as a cross-check;
    # the MATCHED-MARGIN comparison below is the one that answers the
    # real question, in the same "gap from top" terms the app already
    # uses, rather than a top-K shortlist.)
    print("\n\n=== Fixed top-K per race (cross-check, sidesteps the variance confound) ===")
    for label, score in scores.items():
        cdf["_score"] = score
        cdf["_rank"] = cdf.groupby("race_id")["_score"].rank(method="min", ascending=False)
        print(f"\n{label}:")
        for K in [1, 2, 3, 4, 5]:
            winners = cdf[cdf["won"] == 1]
            capture_rate = (winners["_rank"] <= K).mean()
            print(f"  top-{K}: winner capture rate={100*capture_rate:5.1f}%")

    # MATCHED-MARGIN comparison: real user request - "instead of picking
    # top 5, pick a margin (like wpr 5)". For each candidate score, find
    # the margin T' whose average pool size matches WPR-only's own
    # gap<=5 pool size (the app's current selectivity) via a fine-grained
    # scan, then compare capture rate AT THAT MATCHED SELECTIVITY - this
    # is the fair version of the naive same-T comparison at the top of
    # this script (that one was confounded by variance compression).
    cdf["_score"] = scores["WPR only (baseline)"]
    cdf["_top"] = cdf.groupby("race_id")["_score"].transform("max")
    cdf["_gap"] = cdf["_top"] - cdf["_score"]
    target_pool = (cdf["_gap"] <= 5).groupby(cdf["race_id"]).sum().mean()
    print(f"\n\n=== Matched-margin comparison (target pool size = WPR gap<=5 = {target_pool:.2f}) ===")
    for label, score in scores.items():
        cdf["_score"] = score
        cdf["_top"] = cdf.groupby("race_id")["_score"].transform("max")
        cdf["_gap"] = cdf["_top"] - cdf["_score"]
        best_T, best_diff, best_pool, best_capture = None, None, None, None
        for t_hundredths in range(1, 2001):  # scan 0.01 to 20.00 in 0.01 steps
            T = t_hundredths / 100
            in_pool = cdf["_gap"] <= T
            pool_size = in_pool.groupby(cdf["race_id"]).sum().mean()
            diff = abs(pool_size - target_pool)
            if best_diff is None or diff < best_diff:
                winners = cdf[cdf["won"] == 1]
                best_T, best_diff, best_pool = T, diff, pool_size
                best_capture = (winners["_gap"] <= T).mean()
        print(f"  {label:<32} matched margin={best_T:5.2f}  pool size={best_pool:5.2f}  "
              f"winner capture rate={100*best_capture:5.1f}%")


if __name__ == "__main__":
    main()
