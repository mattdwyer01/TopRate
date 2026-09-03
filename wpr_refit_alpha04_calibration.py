"""
wpr_refit_alpha04_calibration.py - one-shot refit of _CALIB_INTERCEPT/
_CALIB_BASE_SLOPE for the new _BASE_BLEND_ALPHA=0.4, following the exact
convention documented in wpr_projection.py's own docstring: "a single
global OLS fit (target ~ raw base) on the full resulted set at the current
_BASE_BLEND_ALPHA".

Uses the leak-corrected training frame (wpr_nett re-merged from
toprate_runners.csv by (horse, date, race_id), not build_training_frame()'s
contaminated run_id merge) so the fit isn't distorted by the same leak that
invalidated the original alpha=0.8 decision.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np

from wpr_alpha_08_leak_corrected_validation import build_full, fix_wpr_nett_leak
from wpr_best_anchor_signal_test import blend

ALPHA = 0.4


def run():
    full = build_full()
    full = fix_wpr_nett_leak(full)
    full = full.dropna(subset=["target"]).reset_index(drop=True)
    raw = blend(full, ALPHA)
    mask = raw.notna() & full["target"].notna()
    slope, intercept = np.polyfit(raw[mask], full["target"][mask], 1)
    mae = float((full["target"][mask] - (intercept + slope * raw[mask])).abs().mean())
    print(f"alpha={ALPHA}  n={mask.sum():,}")
    print(f"_CALIB_INTERCEPT = {intercept:.4f}")
    print(f"_CALIB_BASE_SLOPE = {slope:.4f}")
    print(f"full-data MAE at this fit: {mae:.4f}")


if __name__ == "__main__":
    run()
