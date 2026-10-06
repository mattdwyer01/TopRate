"""
wpr_tiered_base_tail_bias_check.py - user-flagged concern: a horse (Autumn
Glow, wpr_nett=103.0, ewm5=104.5) got base=99.1 from the new tiered
regression (PR #173) - BELOW both of its own raw inputs, for a horse that
went on to win with actual WPR 107.0. The whole point of the additive
BASE+ADJUSTMENT architecture (see wpr_projection.py's module docstring)
was to avoid exactly this: a population-level model structurally
regressing rare high-WPR horses toward the dense middle of the training
population. A directly-fit OLS regression (this new base) can reintroduce
that same shrinkage if its slopes sum to less than 1 with a positive
intercept - which is exactly what shipped (0.3269+0.5778=0.9047,
intercept=+5.04). Overall MAE improving does NOT rule out this being
worse specifically at the top of the distribution (MAE is a population
average - it can improve in the dense middle while getting worse in the
sparse, high-value tail, and would not show that in an aggregate number).

METHOD: for the leak-corrected full dataset, compute OLD (alpha=0.40,
single global calibration) and NEW (tiered) base for every row, bucket by
wpr_nett+ewm5 raw level (deciles), and compare bias (target - base) in
each bucket - specifically the TOP decile, where this concern lives.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak
import wpr_projection as wpr

OLD_ALPHA = 0.40
OLD_CALIB_INTERCEPT = 6.5421
OLD_CALIB_BASE_SLOPE = 0.8839


def old_base(nett, ewm3):
    raw = OLD_ALPHA * nett + (1 - OLD_ALPHA) * ewm3
    return OLD_CALIB_INTERCEPT + OLD_CALIB_BASE_SLOPE * raw


def new_base(row):
    feat = {"wpr_nett": row["wpr_nett"], "ewm5": row["ewm5"],
            "track_wpr": row["track_wpr"], "best3": row["best3"]}
    return wpr._compute_base(feat)


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target", "wpr_nett", "ewm3", "ewm5"]).reset_index(drop=True)
    print(f"Scoped rows: {len(full):,}")

    full["_old_base"] = old_base(full["wpr_nett"], full["ewm3"])
    full["_new_base"] = full.apply(new_base, axis=1)

    full["_old_bias"] = full["target"] - full["_old_base"]
    full["_new_bias"] = full["target"] - full["_new_base"]

    # bucket by raw signal LEVEL (avg of wpr_nett/ewm5, the two always-on
    # inputs) - deciles, so the top bucket is exactly "the elite end" this
    # concern is about
    full["_raw_level"] = (full["wpr_nett"] + full["ewm5"]) / 2
    full["_decile"] = pd.qcut(full["_raw_level"], 10, labels=False, duplicates="drop")

    print(f"\n{'='*100}\nBIAS BY RAW-LEVEL DECILE (0=lowest-rated horses, 9=highest-rated)\n{'='*100}")
    print(f"  {'decile':>6} {'raw level range':>22} {'n':>7} {'OLD base bias':>15} {'NEW base bias':>15} "
          f"{'OLD avg base':>13} {'NEW avg base':>13} {'avg target':>11}")
    for d in sorted(full["_decile"].dropna().unique()):
        sub = full[full["_decile"] == d]
        lo, hi = sub["_raw_level"].min(), sub["_raw_level"].max()
        print(f"  {int(d):>6} {f'{lo:.1f}-{hi:.1f}':>22} {len(sub):>7,} "
              f"{sub['_old_bias'].mean():>+15.2f} {sub['_new_bias'].mean():>+15.2f} "
              f"{sub['_old_base'].mean():>13.2f} {sub['_new_base'].mean():>13.2f} {sub['target'].mean():>11.2f}")

    print(f"\n{'='*100}\nTOP 5% AND TOP 1% SPECIFICALLY (the rarest, most elite horses)\n{'='*100}")
    for pct in [0.05, 0.01]:
        cut = full["_raw_level"].quantile(1 - pct)
        sub = full[full["_raw_level"] >= cut]
        print(f"  top {pct*100:.0f}% (raw level >= {cut:.1f}, n={len(sub):,}): "
              f"OLD bias={sub['_old_bias'].mean():+.2f}  NEW bias={sub['_new_bias'].mean():+.2f}  "
              f"OLD avg base={sub['_old_base'].mean():.2f}  NEW avg base={sub['_new_base'].mean():.2f}  "
              f"avg target={sub['target'].mean():.2f}")

    print(f"\n{'='*100}\nOVERALL MAE (sanity check against the numbers already reported)\n{'='*100}")
    print(f"  OLD overall MAE: {full['_old_bias'].abs().mean():.4f}")
    print(f"  NEW overall MAE: {full['_new_bias'].abs().mean():.4f}")

    print("\nA more NEGATIVE bias in the top decile/percentile for NEW vs OLD means the new tiered base "
          "under-projects elite horses MORE than the old alpha blend did - exactly the failure mode the "
          "additive architecture exists to avoid, even if overall MAE looks better.")


if __name__ == "__main__":
    run()
