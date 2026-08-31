"""
wpr_alpha80_calibration_fit.py - re-derives the piecewise base calibration
for _BASE_BLEND_ALPHA=0.80, following the EXACT methodology used for the
original 0.50->0.80 shift and its later 0.80->0.50 revert (see git log
commits 5fa1966 and 8d049e9): full-data 3-segment fit (low 10% / mid 70% /
high 20% of the raw base's OWN distribution, breakpoints re-derived per
alpha since the distribution shifts), then validates the new
alpha+calibration combo against the CURRENT PRODUCTION combo (alpha=0.50 +
its own calibration) on a genuine chronological half-split, BOTH
directions, on MAE (the model's traditional bar) AND top-1 strike rate
(this session's actual ask) before recommending a ship decision.

WHY ALPHA=0.80 SPECIFICALLY: this session's own wpr_alpha_strike_eval.py
found top-1 strike rate rising monotonically with alpha in BOTH
chronological halves across the whole 0.30-0.90 grid, peaking in the
0.80-0.90 region in both - independently confirming the original
git-history MAE-based finding that landed on 0.80 (not the more
aggressive value the still-climbing trend might suggest, since only
0.70-0.85 was ever genuinely forward-validated - see _BASE_BLEND_ALPHA's
old docstring, recovered from git history).

USAGE
  python wpr_alpha80_calibration_fit.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import LinearRegression
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import add_track_barrier

FORM_CSV = "wpr_form_history.csv.gz"
NEW_ALPHA = 0.80

# The form history spans 2016-2026 but is heavily back-loaded (2025 Q2
# onward is ~68% of all rows). A naive 50/50 chronological split lands
# around Oct 2025, putting a 9-YEAR mash-up of old data into "H1" -
# including 2025 Q1, where the documented alpha-drift analysis (git
# history, commit 5fa1966) found the actual OPTIMAL alpha was only 0.25.
# Testing whether a single fixed alpha=0.80 generalizes across that known
# drift answers the wrong question (of course a single alpha doesn't fit
# both eras - that IS the drift). SINCE_CUTOFF restricts both halves to
# the recent, post-drift-settling era the 0.70-0.85 validated range
# actually concerns, matching how the original analysis avoided this trap
# (60-day rolling windows, or toprate_runners.csv's own recent-only data).
SINCE_CUTOFF = "2025-10-01"

# Current production constants (for the head-to-head comparison).
PROD_ALPHA = wpr._BASE_BLEND_ALPHA
PROD_LOW_BREAK = wpr._CALIB_LOW_BREAK
PROD_HIGH_BREAK = wpr._CALIB_HIGH_BREAK
PROD_LOW_INTERCEPT = wpr._CALIB_LOW_INTERCEPT
PROD_LOW_SLOPE = wpr._CALIB_LOW_SLOPE
PROD_INTERCEPT = wpr._CALIB_INTERCEPT
PROD_BASE_SLOPE = wpr._CALIB_BASE_SLOPE
PROD_HIGH_INTERCEPT = wpr._CALIB_HIGH_INTERCEPT
PROD_HIGH_SLOPE = wpr._CALIB_HIGH_SLOPE


def raw_base(D, alpha):
    both = D["wpr_nett"].notna() & D["ewm3"].notna()
    raw = np.where(both, alpha * D["wpr_nett"] + (1 - alpha) * D["ewm3"],
                   D["wpr_nett"].fillna(D["ewm3"]))
    return pd.Series(raw, index=D.index).fillna(D["avg_last3"]).fillna(D["career_avg"])


def fit_piecewise(fit_rows, raw_col="_raw_base", target_col="target"):
    """Full-data 3-segment fit (low 10% / mid 70% / high 20%), exactly the
    methodology in git history's alpha-shift commits."""
    d = fit_rows.dropna(subset=[raw_col, target_col])
    low_break, high_break = d[raw_col].quantile([0.10, 0.80])
    segs = {}
    for name, mask in [
        ("low", d[raw_col] <= low_break),
        ("mid", (d[raw_col] > low_break) & (d[raw_col] <= high_break)),
        ("high", d[raw_col] > high_break),
    ]:
        seg = d[mask]
        reg = LinearRegression().fit(seg[[raw_col]], seg[target_col])
        segs[name] = (float(reg.intercept_), float(reg.coef_[0]), len(seg))
    return float(low_break), float(high_break), segs


def calibrate(raw, low_break, high_break, segs):
    lo_i, lo_s, _ = segs["low"]
    mid_i, mid_s, _ = segs["mid"]
    hi_i, hi_s, _ = segs["high"]
    out = np.where(raw <= low_break, lo_i + lo_s * raw,
          np.where(raw > high_break, hi_i + hi_s * raw, mid_i + mid_s * raw))
    return out


def prod_calibrate(raw):
    return np.where(raw <= PROD_LOW_BREAK, PROD_LOW_INTERCEPT + PROD_LOW_SLOPE * raw,
           np.where(raw > PROD_HIGH_BREAK, PROD_HIGH_INTERCEPT + PROD_HIGH_SLOPE * raw,
                     PROD_INTERCEPT + PROD_BASE_SLOPE * raw))


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def run():
    print(f"Rebuilding training frame (production filters applied: void + surface)...")
    D = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1).dropna(
        subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} rows before void/surface filters")

    try:
        from wpr_void import void_from_comment_only
        cv = D["comments_video"] if "comments_video" in D.columns else [None] * len(D)
        cs = D["comments_steward"] if "comments_steward" in D.columns else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        n_void = int(sum(void_mask))
        if n_void:
            D = D[[not v for v in void_mask]].copy()
            print(f"  void filter: excluded {n_void:,} compromised runs, {len(D):,} remain")
    except ImportError:
        print("  void filter: wpr_void not found, skipping")

    if "going" in D.columns:
        g = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} blank-going runs, {len(D):,} remain")

    D["run_id"] = D["run_id"].astype(str)
    print("\nMerging race result (won/race_id) from toprate_runners.csv by run_id...")
    tr = pd.read_csv("toprate_runners.csv", dtype={"run_id": str, "race_id": str}, low_memory=False,
                      usecols=["run_id", "race_id", "won", "resulted", "scratched"])
    tr["resulted"] = pd.to_numeric(tr["resulted"], errors="coerce")
    tr["scratched"] = pd.to_numeric(tr["scratched"], errors="coerce")
    tr["won"] = pd.to_numeric(tr["won"], errors="coerce")
    tr = tr[(tr["resulted"] == 1) & (tr["scratched"] != 1)].dropna(subset=["won", "race_id"])
    tr = tr.drop_duplicates(subset="run_id", keep="last")
    # D already carries its own race_id (build_training_frame's
    # _horse_feature_rows retains it) - merging tr's race_id too would
    # collide into race_id_x/race_id_y (see the same bug already hit and
    # fixed in wpr_alpha_strike_eval.py / wpr_settle_pace_strike_eval.py).
    D_res = D.merge(tr[["run_id", "won"]], on="run_id", how="inner")

    non_tb = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    D = D.dropna(subset=["wpr_nett", "avg_last3", "career_avg"] + non_tb)
    D_res = D_res.dropna(subset=["wpr_nett", "avg_last3", "career_avg"] + non_tb +
                          ["barrier", "field_size", "track", "cur_distance"])

    if SINCE_CUTOFF:
        n_before_d, n_before_dres = len(D), len(D_res)
        D = D[D["date"] >= pd.Timestamp(SINCE_CUTOFF)].copy()
        D_res = D_res[D_res["date"] >= pd.Timestamp(SINCE_CUTOFF)].copy()
        print(f"  recency cutoff >= {SINCE_CUTOFF}: MAE rows {n_before_d:,} -> {len(D):,}, "
              f"strike-rate rows {n_before_dres:,} -> {len(D_res):,} (avoids mixing in the "
              f"pre-drift era - see SINCE_CUTOFF comment)")

    print(f"  {len(D):,} rows usable for MAE calibration fit, "
          f"{len(D_res):,} rows usable for strike-rate validation ({D_res['race_id'].nunique():,} races)")

    mid_date = D["date"].quantile(0.5)
    h1, h2 = D[D["date"] < mid_date], D[D["date"] >= mid_date]
    mid_date_r = D_res["date"].quantile(0.5)
    h1r, h2r = D_res[D_res["date"] < mid_date_r].copy(), D_res[D_res["date"] >= mid_date_r].copy()
    print(f"MAE split: H1={len(h1):,} (< {mid_date.date()}), H2={len(h2):,} (>= {mid_date.date()})")
    print(f"Strike split: H1r={len(h1r):,} (< {mid_date_r.date()}), H2r={len(h2r):,} (>= {mid_date_r.date()})\n")

    for frame in (h1, h2, h1r, h2r):
        frame["_raw_new"] = raw_base(frame, NEW_ALPHA)
        frame["_raw_prod"] = raw_base(frame, PROD_ALPHA)

    print("=== Fitting NEW alpha=0.80 piecewise calibration (H1-fit direction) ===")
    lb1, hb1, segs1 = fit_piecewise(h1, raw_col="_raw_new")
    print(f"  breakpoints: low<={lb1:.2f}, high>{hb1:.2f}")
    for name, (i, s, n) in segs1.items():
        print(f"  {name}: intercept={i:.3f} slope={s:.4f} n={n:,}")

    print("\n=== Fitting NEW alpha=0.80 piecewise calibration (H2-fit direction) ===")
    lb2, hb2, segs2 = fit_piecewise(h2, raw_col="_raw_new")
    print(f"  breakpoints: low<={lb2:.2f}, high>{hb2:.2f}")
    for name, (i, s, n) in segs2.items():
        print(f"  {name}: intercept={i:.3f} slope={s:.4f} n={n:,}")

    def new_base(frame, lb, hb, segs):
        return calibrate(frame["_raw_new"].to_numpy(), lb, hb, segs)

    def prod_base(frame):
        return prod_calibrate(frame["_raw_prod"].to_numpy())

    print("\n=== MAE: H1-fit/H2-validate direction ===")
    prod_mae_h2 = mean_absolute_error(h2["target"], prod_base(h2))
    new_mae_h2 = mean_absolute_error(h2["target"], new_base(h2, lb1, hb1, segs1))
    print(f"  production (alpha={PROD_ALPHA}): held-out MAE = {prod_mae_h2:.4f}")
    print(f"  new (alpha={NEW_ALPHA}):        held-out MAE = {new_mae_h2:.4f}")

    print("\n=== MAE: H2-fit/H1-validate direction ===")
    prod_mae_h1 = mean_absolute_error(h1["target"], prod_base(h1))
    new_mae_h1 = mean_absolute_error(h1["target"], new_base(h1, lb2, hb2, segs2))
    print(f"  production (alpha={PROD_ALPHA}): held-out MAE = {prod_mae_h1:.4f}")
    print(f"  new (alpha={NEW_ALPHA}):        held-out MAE = {new_mae_h1:.4f}")

    # Strike-rate validation: full projection (calibrated base + ADJ_TERMS,
    # track_barrier refit per direction same as every other script this
    # session) for production vs new, on the SAME held-out races.
    h1r_d1, h2r_d1 = h1r.copy(), h2r.copy()
    add_track_barrier(h1r_d1, [h1r_d1, h2r_d1])
    h1r_d2, h2r_d2 = h1r.copy(), h2r.copy()
    add_track_barrier(h2r_d2, [h1r_d2, h2r_d2])

    def full_proj(frame, base_arr):
        return base_arr + wpr._cap_adj_sum(frame[wpr.ADJ_TERMS].to_numpy()).sum(axis=1)

    h2r_d1["proj_prod"] = full_proj(h2r_d1, prod_base(h2r_d1))
    h2r_d1["proj_new"] = full_proj(h2r_d1, new_base(h2r_d1, lb1, hb1, segs1))
    h1r_d2["proj_prod"] = full_proj(h1r_d2, prod_base(h1r_d2))
    h1r_d2["proj_new"] = full_proj(h1r_d2, new_base(h1r_d2, lb2, hb2, segs2))

    print("\n=== Top-1 strike rate: H1-fit/H2-validate direction ===")
    pr, pk, pn = top1_strike_rate(h2r_d1, "proj_prod")
    nr, nk, nn = top1_strike_rate(h2r_d1, "proj_new")
    print(f"  production: {pk}/{pn} = {pr:.2f}%   new: {nk}/{nn} = {nr:.2f}%")

    print("\n=== Top-1 strike rate: H2-fit/H1-validate direction ===")
    pr2, pk2, pn2 = top1_strike_rate(h1r_d2, "proj_prod")
    nr2, nk2, nn2 = top1_strike_rate(h1r_d2, "proj_new")
    print(f"  production: {pk2}/{pn2} = {pr2:.2f}%   new: {nk2}/{nn2} = {nr2:.2f}%")

    mae_better = (new_mae_h2 < prod_mae_h2) and (new_mae_h1 < prod_mae_h1)
    strike_better = (nr > pr) and (nr2 > pr2)
    print(f"\nMAE improved in both directions: {mae_better}")
    print(f"Strike rate improved in both directions: {strike_better}")

    print("\n=== FINAL FULL-DATA FIT (what would ship) ===")
    D_full = D.assign(_raw_new=raw_base(D, NEW_ALPHA))
    lbf, hbf, segsf = fit_piecewise(D_full, raw_col="_raw_new")
    print(f"_CALIB_LOW_BREAK = {lbf:.2f}")
    print(f"_CALIB_HIGH_BREAK = {hbf:.2f}")
    print(f"_CALIB_LOW_INTERCEPT = {segsf['low'][0]:.3f}")
    print(f"_CALIB_LOW_SLOPE = {segsf['low'][1]:.4f}")
    print(f"_CALIB_INTERCEPT = {segsf['mid'][0]:.3f}")
    print(f"_CALIB_BASE_SLOPE = {segsf['mid'][1]:.4f}")
    print(f"_CALIB_HIGH_INTERCEPT = {segsf['high'][0]:.3f}")
    print(f"_CALIB_HIGH_SLOPE = {segsf['high'][1]:.4f}")

    if mae_better and strike_better:
        print("\nBOTH MAE and strike rate improve in both directions - ship-ready.")
    elif mae_better or strike_better:
        print("\nOnly one of MAE/strike rate improves in both directions - report to user, "
              "do not ship without discussion.")
    else:
        print("\nNeither improves in both directions - do NOT ship alpha=0.80.")


if __name__ == "__main__":
    run()
