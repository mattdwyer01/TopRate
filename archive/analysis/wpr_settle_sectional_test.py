"""
wpr_settle_sectional_test.py - tests whether RAW early-sectional speed
ratings improve on settling_estimate.py's coarse positionSettled/field_size
ratio for predicting where a horse will settle.

WHY THIS EXISTS: settling_estimate.py's run_style_tendency is an ORDINAL
measure (settled 3rd of 8 = 0.375, whether that horse was a nose behind
the leader or ten lengths back) - it captures RANK but not MAGNITUDE.
sect_i_early ("individualEarlySpeed" - see toprate_json_capture.py's own
field mapping) is a continuous early-speed RATING - the same kind of
number used throughout this codebase for speed comparisons, capturing
intensity, not just where-it-placed. A horse with a genuinely strong
early-speed rating relative to today's field should be more likely to
race forward regardless of how many runners happen to be in the race -
information positionSettled/field_size cannot carry.

CANDIDATE: add a race-relative sect_i_early signal to the existing linear
model (run_style_tendency + barrier_nudge): this horse's own TRAILING mean
sect_i_early, ranked against the OTHER runners' trailing means in TODAY's
actual field (a percentile within the race, mirroring how barrier_nudge
itself is expressed relative to today's field) - fully pre-race-safe
(each ingredient is a prior-history aggregate, the ranking uses only
today's already-known field).

Reuses wpr_settle_barrier_nudge_calibration_test.py's verified (dedup-
fixed, cross-checked against settling_estimate's own slow method)
load_and_prep/add_trailing_run_style machinery directly, rather than
re-deriving it and risking the same duplicate-row bug again.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

import settling_estimate as se
from wpr_settle_barrier_nudge_calibration_test import (
    load_and_prep, add_trailing_run_style, verify_against_slow_method, fit_ols,
)

FORM_CSV = "wpr_form_history.csv.gz"


def add_trailing_sect_early(fh):
    """Same vectorized groupby-cumsum-shift pattern as
    add_trailing_run_style, applied to sect_i_early instead of relative
    settle - trailing (strictly prior), per horse. Winsorized before
    averaging: sect_i_early has extreme outliers (min -243.9 on a field
    whose 25th-75th percentile is -8.7 to -2.6) that would otherwise
    dominate a raw mean."""
    raw = pd.to_numeric(fh["sect_i_early"], errors="coerce")
    lo, hi = raw.quantile([0.01, 0.99])
    clipped = raw.clip(lo, hi)
    valid = clipped.notna()
    val_valid = clipped.where(valid)

    g = fh["horse_lc"]
    csum_incl = val_valid.fillna(0).groupby(g).cumsum()
    ccount_incl = valid.astype(int).groupby(g).cumsum()
    csum_prior = csum_incl.groupby(g).shift(1)
    ccount_prior = ccount_incl.groupby(g).shift(1)
    fh["trailing_sect_i_early"] = csum_prior / ccount_prior.replace(0, np.nan)
    return fh


def add_race_relative_sect_rank(fh):
    """This horse's trailing_sect_i_early ranked (0-1 percentile, higher =
    faster early speed rating) against the OTHER runners in the SAME
    (track, date, raceNumber) race - today's actual field, fully
    pre-race-safe (each input is a prior-history aggregate)."""
    race_key = fh["track"].astype(str) + "|" + fh["date"].astype(str) + "|" + fh["raceNumber"].astype(str)
    fh["_race_key"] = race_key
    fh["sect_rank_in_race"] = fh.groupby("_race_key")["trailing_sect_i_early"].rank(pct=True, na_option="keep")
    return fh


def run():
    print("Loading and preparing form history...")
    fh = load_and_prep()
    fh = add_trailing_run_style(fh)
    verify_against_slow_method(fh)
    fh = add_trailing_sect_early(fh)
    fh = add_race_relative_sect_rank(fh)
    print(f"  trailing_sect_i_early coverage: {fh['trailing_sect_i_early'].notna().mean()*100:.1f}%")
    print(f"  sect_rank_in_race coverage: {fh['sect_rank_in_race'].notna().mean()*100:.1f}%")

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    # sect_rank_in_race: 1 = fastest early-speed rating in the field (should
    # PULL toward the front, i.e. NEGATIVE contribution to rel since 0=lead)
    # - centred the same way as draw_signal for a directly comparable
    # coefficient scale.
    fh["sect_signal"] = (fh["sect_rank_in_race"] - 0.5) * 2

    usable = fh.dropna(subset=["run_style_tendency", "actual_rel", "draw_signal"]).copy()
    usable["residual"] = usable["actual_rel"] - usable["run_style_tendency"]
    print(f"\nUsable rows: {len(usable):,} "
          f"(of which {usable['sect_signal'].notna().sum():,} also have sect_signal)")

    def evaluate(trn, te, label):
        Xa = trn[["draw_signal"]].to_numpy()
        ya = trn["residual"].to_numpy()
        (b_fit,) = fit_ols(Xa, ya)

        trn_s = trn.dropna(subset=["sect_signal"])
        Xb = trn_s[["draw_signal", "sect_signal"]].to_numpy()
        yb = trn_s["residual"].to_numpy()
        b_fit2, d_fit = fit_ols(Xb, yb)

        def predict(frame, nudge_fn):
            pred = frame["run_style_tendency"] + frame.apply(nudge_fn, axis=1)
            return pred.clip(0, 1)

        baseline_pred = predict(te, lambda r: r["draw_signal"] * se.BARRIER_MAX_NUDGE)
        a_pred = predict(te, lambda r: r["draw_signal"] * b_fit)
        b_pred = predict(te, lambda r: r["draw_signal"] * b_fit2 +
                         (r["sect_signal"] * d_fit if not pd.isna(r["sect_signal"]) else 0.0))

        mae_base = (baseline_pred - te["actual_rel"]).abs().mean()
        mae_a = (a_pred - te["actual_rel"]).abs().mean()
        mae_b = (b_pred - te["actual_rel"]).abs().mean()
        print(f"  [{label}] n_trn={len(trn):,} n_te={len(te):,} "
              f"fitted_B={b_fit:.4f}  fitted_B2={b_fit2:.4f} fitted_D(sect)={d_fit:.4f}")
        print(f"    baseline (B=0.12, no sect) MAE={mae_base:.4f}  "
              f"fitted-B-only MAE={mae_a:.4f} ({mae_a - mae_base:+.4f})  "
              f"fitted-B+sect MAE={mae_b:.4f} ({mae_b - mae_base:+.4f}, "
              f"{'better' if mae_b < mae_base else 'worse'})")
        return mae_base, mae_a, mae_b

    q70, q85 = usable["date"].quantile([0.70, 0.85])
    trn_a = usable[usable["date"] < q70]
    te_a = usable[usable["date"] >= q85]
    q30, q15 = usable["date"].quantile([0.30, 0.15])
    trn_b = usable[usable["date"] > q30]
    te_b = usable[usable["date"] <= q15]

    print("\n=== Direction A (forward: oldest 70% trn, newest 15% te) ===")
    res_a = evaluate(trn_a, te_a, "A")
    print("\n=== Direction B (reversed: newest 70% trn, oldest 15% te) ===")
    res_b = evaluate(trn_b, te_b, "B")

    print("\n=== SUMMARY (fitted-B+sect vs baseline) ===")
    da = res_a[2] - res_a[0]
    db = res_b[2] - res_b[0]
    both = da < 0 and db < 0
    print(f"  direction A {da:+.4f}, direction B {db:+.4f}  "
          f"{'BOTH IMPROVED' if both else 'not both improved'}")

    print("\nDone.")


if __name__ == "__main__":
    run()
