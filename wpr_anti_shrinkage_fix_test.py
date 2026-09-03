"""
wpr_anti_shrinkage_fix_test.py - investigates a fix for the extrapolation
problem found in wpr_tier_specific_bias_check.py: the "minimal" tier
(wpr_nett+ewm5 only, used when track_wpr/best3 are unavailable) was fit
on just 936 rows, and its own training data doesn't reach anywhere near
Autumn Glow's raw level (103.75) - so its prediction there is a linear
EXTRAPOLATION past the fitted range, not an interpolation. wpr_nett/ewm5
are available on all 43,752 rows regardless of tier, so this tests
whether fitting that 2-signal relationship on the FULL population (not
just the 936 rows that happen to lack track_wpr/best3) gives a more
reliable coefficient at the extreme top, where the full population
actually has real data (elite horses with track_wpr/best3 available too)
even though the minimal-tier-only subset does not.

METHOD: for every row (all 43,752, regardless of actual tier), compute
what a "wpr_nett+ewm5 only" regression predicts under two fits:
  (a) CURRENT: fit on the 936-row minimal-tier-only subset (what's
      actually shipped for minimal-tier horses).
  (b) CANDIDATE: fit on the full 43,752-row population instead.
Then check bias specifically among HIGH raw-level rows (regardless of
tier) - if (b) shows less top-end bias than (a) on the SAME rows, the
extrapolation-from-a-tiny-subset theory is confirmed and the fix is
simple: fit the minimal tier's 2-signal coefficients on all available
data (every row has wpr_nett+ewm5), not just the subset that happens to
lack the other two signals.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak

N_FOLDS = 4


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target", "wpr_nett", "ewm5"]).sort_values("date").reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    full["_fold"] = -1
    for i, idx in enumerate(np.array_split(np.arange(len(full)), N_FOLDS)):
        full.loc[idx, "_fold"] = i

    has_track = full["track_wpr"].notna()
    has_best3 = full["best3"].notna()
    is_minimal_tier = ~has_track
    print(f"Minimal-tier rows (no track_wpr): {is_minimal_tier.sum():,}")
    print(f"Minimal-tier raw-level range: "
          f"{((full.loc[is_minimal_tier,'wpr_nett']+full.loc[is_minimal_tier,'ewm5'])/2).min():.1f} to "
          f"{((full.loc[is_minimal_tier,'wpr_nett']+full.loc[is_minimal_tier,'ewm5'])/2).max():.1f}")
    print(f"Full population raw-level range: "
          f"{((full['wpr_nett']+full['ewm5'])/2).min():.1f} to {((full['wpr_nett']+full['ewm5'])/2).max():.1f}")

    full["_raw_level"] = (full["wpr_nett"] + full["ewm5"]) / 2

    # K-fold predictions under both fits, scored on the SAME held-out rows
    pred_current = pd.Series(np.nan, index=full.index)
    pred_candidate = pd.Series(np.nan, index=full.index)
    for i in range(N_FOLDS):
        train = full[full["_fold"] != i]
        test = full[full["_fold"] == i]

        train_minimal = train[~train["track_wpr"].notna()]
        m_current = LinearRegression().fit(
            train_minimal[["wpr_nett", "ewm5"]].to_numpy(), train_minimal["target"].to_numpy())
        m_candidate = LinearRegression().fit(
            train[["wpr_nett", "ewm5"]].to_numpy(), train["target"].to_numpy())

        pred_current.loc[test.index] = m_current.predict(test[["wpr_nett", "ewm5"]].to_numpy())
        pred_candidate.loc[test.index] = m_candidate.predict(test[["wpr_nett", "ewm5"]].to_numpy())

        print(f"  fold {i}: CURRENT (936-row fit) coef={m_current.coef_.round(3)} "
              f"intercept={m_current.intercept_:.2f}  |  CANDIDATE (full-pop fit) "
              f"coef={m_candidate.coef_.round(3)} intercept={m_candidate.intercept_:.2f}")

    full["_pred_current"] = pred_current
    full["_pred_candidate"] = pred_candidate
    full["_bias_current"] = full["target"] - full["_pred_current"]
    full["_bias_candidate"] = full["target"] - full["_pred_candidate"]

    print(f"\n{'='*100}\nBIAS BY RAW-LEVEL BAND, EVERY ROW (both fits scored on the same held-out rows, "
          f"regardless of actual tier)\n{'='*100}")
    print(f"  {'band':>12} {'n':>7} {'CURRENT bias':>13} {'CANDIDATE bias':>15} {'CURRENT MAE':>12} "
          f"{'CANDIDATE MAE':>14}")
    bands = [(0, 60), (60, 70), (70, 80), (80, 90), (90, 95), (95, 100), (100, 200)]
    for lo, hi in bands:
        sub = full[(full["_raw_level"] >= lo) & (full["_raw_level"] < hi)]
        if len(sub) < 5:
            continue
        print(f"  {f'{lo}-{hi}':>12} {len(sub):>7,} {sub['_bias_current'].mean():>+13.2f} "
              f"{sub['_bias_candidate'].mean():>+15.2f} {sub['_bias_current'].abs().mean():>12.3f} "
              f"{sub['_bias_candidate'].abs().mean():>14.3f}")

    print(f"\n{'='*100}\nSAME, BUT ONLY ACTUAL MINIMAL-TIER ROWS (the ones this would actually change in "
          f"production)\n{'='*100}")
    print(f"  {'band':>12} {'n':>7} {'CURRENT bias':>13} {'CANDIDATE bias':>15} {'CURRENT MAE':>12} "
          f"{'CANDIDATE MAE':>14}")
    mini = full[is_minimal_tier]
    for lo, hi in bands:
        sub = mini[(mini["_raw_level"] >= lo) & (mini["_raw_level"] < hi)]
        if len(sub) < 5:
            continue
        print(f"  {f'{lo}-{hi}':>12} {len(sub):>7,} {sub['_bias_current'].mean():>+13.2f} "
              f"{sub['_bias_candidate'].mean():>+15.2f} {sub['_bias_current'].abs().mean():>12.3f} "
              f"{sub['_bias_candidate'].abs().mean():>14.3f}")

    print(f"\nOverall minimal-tier MAE: CURRENT={mini['_bias_current'].abs().mean():.4f}  "
          f"CANDIDATE={mini['_bias_candidate'].abs().mean():.4f}")

    print("\nWhat this tells us: if CANDIDATE (full-population fit) shows less top-band bias/MAE than "
          "CURRENT (936-row minimal-tier-only fit) on the SAME minimal-tier rows, the extrapolation "
          "theory is confirmed and the fix is straightforward - fit the minimal tier's coefficients on "
          "every row with wpr_nett+ewm5 (all 43,752), not just the 936 that happen to lack track_wpr/best3.")


if __name__ == "__main__":
    run()
