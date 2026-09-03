"""
wpr_tier_specific_bias_check.py - follow-up to wpr_tiered_base_tail_bias_
check.py: the AGGREGATE top-decile bias for the new tiered base actually
looks slightly BETTER than the old alpha blend (+0.93 vs +1.09), which
seems to contradict the user-flagged Autumn Glow case (new base 99.1,
below both its own raw inputs 103.0/104.5). Resolves this by splitting
bias-by-decile SEPARATELY for each of the three tiers (minimal/track/
full) - Autumn Glow specifically used the "minimal" tier (no track_wpr/
best3), so if that tier alone has worse top-end bias than the old model,
it would be masked in the all-tiers-pooled average by the richer track/
full tiers (which cover most of the elite-horse population and could be
doing fine, or even better).

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


def tier_of(row):
    has_track = pd.notna(row["track_wpr"])
    has_best3 = pd.notna(row["best3"])
    if has_track and has_best3:
        return "full"
    if has_track:
        return "track"
    return "minimal"


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target", "wpr_nett", "ewm3", "ewm5"]).reset_index(drop=True)

    full["_old_base"] = old_base(full["wpr_nett"], full["ewm3"])
    full["_new_base"] = full.apply(new_base, axis=1)
    full["_old_bias"] = full["target"] - full["_old_base"]
    full["_new_bias"] = full["target"] - full["_new_base"]
    full["_raw_level"] = (full["wpr_nett"] + full["ewm5"]) / 2
    full["_tier"] = full.apply(tier_of, axis=1)

    print(f"Tier counts: {full['_tier'].value_counts().to_dict()}")

    for tier in ["minimal", "track", "full"]:
        sub_tier = full[full["_tier"] == tier]
        print(f"\n{'='*100}\nTIER: {tier}  (n={len(sub_tier):,})\n{'='*100}")
        print(f"  {'top-%':>8} {'n':>7} {'OLD bias':>10} {'NEW bias':>10} {'OLD avg base':>13} "
              f"{'NEW avg base':>13} {'avg target':>11}")
        for pct, label in [(0.5, 'all'), (0.2, 'top20%'), (0.1, 'top10%'), (0.05, 'top5%'), (0.01, 'top1%')]:
            cut = sub_tier["_raw_level"].quantile(1 - pct) if pct < 0.5 else sub_tier["_raw_level"].min()
            piece = sub_tier[sub_tier["_raw_level"] >= cut]
            if len(piece) < 10:
                continue
            print(f"  {label:>8} {len(piece):>7,} {piece['_old_bias'].mean():>+10.2f} "
                  f"{piece['_new_bias'].mean():>+10.2f} {piece['_old_base'].mean():>13.2f} "
                  f"{piece['_new_base'].mean():>13.2f} {piece['target'].mean():>11.2f}")

    # Specifically reproduce the Autumn Glow case: minimal tier, raw_level
    # around 103.75 (avg of 103.0/104.5) - what's the bias for horses
    # in that exact neighborhood?
    print(f"\n{'='*100}\nMINIMAL-TIER horses near Autumn Glow's own raw level (100-108)\n{'='*100}")
    near = full[(full["_tier"] == "minimal") & (full["_raw_level"] >= 100) & (full["_raw_level"] <= 108)]
    print(f"  n={len(near)}")
    if len(near) > 0:
        print(f"  OLD: avg base={near['_old_base'].mean():.2f}  avg bias={near['_old_bias'].mean():+.2f}")
        print(f"  NEW: avg base={near['_new_base'].mean():.2f}  avg bias={near['_new_bias'].mean():+.2f}")
        print(f"  avg target={near['target'].mean():.2f}")
        print(f"\n  Individual rows:")
        for _, r in near.head(20).iterrows():
            print(f"    wpr_nett={r['wpr_nett']:.1f} ewm5={r['ewm5']:.1f}  "
                  f"OLD base={r['_old_base']:.1f}  NEW base={r['_new_base']:.1f}  target={r['target']:.1f}")


if __name__ == "__main__":
    run()
