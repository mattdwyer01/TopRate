"""wpr_beta_recalibration_clean.py - recalibrate beta for BRIER/calibration
quality (item 3 of the "how do we improve strike rate/AUC/Brier further"
follow-up, Sep 2026) using clean, real, live-served data directly from
toprate_runners.csv - no build_training_frame() needed (and therefore no
exposure to today's wpr_nett future-leak bug, since live-served wprp_proj
was never affected by it - see wpr_rating_quality_check.py's docstring).

NOTE: beta is rank-invariant - it cannot change AUC or top-pick strike
rate (softmax with any beta>0 preserves order). It ONLY affects how
sharply wprp_proj gaps are converted into probabilities, i.e. calibration
(Brier score). This script's job is narrow: is the currently-shipped
beta=0.3 actually the Brier-minimising choice for the CURRENT (post
demeaning-fix) architecture, or is it stale?

calibrate_price_beta.py already does a version of this, but via
build_new_proj_frame() -> build_training_frame(), which was affected by
today's leak fix (though beta itself, being derived from wprp_proj values
not from _base training, is less directly at risk - still worth a clean
cross-check against real persisted data with zero reconstruction).

Methodology: 70/30 date split (matching calibrate_price_beta.py's own
convention) on toprate_runners.csv's real resulted rows with wprp_proj
present, search a beta grid by held-out Brier score.

USAGE
  python wpr_beta_recalibration_clean.py

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

import toprate_daily as td

BETA_GRID = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.50]


def brier_for_beta(df, beta):
    rows = []
    for rid, g in df.groupby("race_id"):
        if len(g) < 4:
            continue
        pv = g["wprp_proj"].to_numpy(dtype=float)
        e = np.exp(beta * (pv - pv.max()))
        p = e / e.sum()
        rows.extend(zip(p, g["won"]))
    arr = pd.DataFrame(rows, columns=["p", "won"])
    return float(((arr["p"] - arr["won"]) ** 2).mean()) if len(arr) else float("nan")


def report(label, df):
    print(f"\n{'='*70}\n{label}\n{'='*70}")
    df = df.sort_values("date")
    cut = df["date"].quantile(0.70)
    trn, tst = df[df["date"] < cut], df[df["date"] >= cut]
    print(f"races: {df['race_id'].nunique():,}  (train < {cut.date()}: {trn['race_id'].nunique():,}, "
          f"held-out: {tst['race_id'].nunique():,})")
    print("beta | train Brier | held-out Brier")
    best_beta, best_brier = None, float("inf")
    for b in BETA_GRID:
        b_trn, b_tst = brier_for_beta(trn, b), brier_for_beta(tst, b)
        print(f"  {b:.2f}   {b_trn:.5f}    {b_tst:.5f}")
        if b_trn < best_brier:
            best_brier, best_beta = b_trn, b
    held_out_best = brier_for_beta(tst, best_beta)
    held_out_current = brier_for_beta(tst, 0.3)
    print(f"\ntrain-selected best beta: {best_beta}  (held-out Brier {held_out_best:.5f})")
    print(f"current shipped beta 0.3: held-out Brier {held_out_current:.5f}")


def run():
    r = td.load_runners()
    r["d"] = r["date"].astype(str).str[:10]
    r["date"] = pd.to_datetime(r["date"], errors="coerce")
    r["won"] = pd.to_numeric(r["won"], errors="coerce")
    r["resulted"] = pd.to_numeric(r["resulted"], errors="coerce")
    r["scratched"] = pd.to_numeric(r["scratched"], errors="coerce")
    r["wprp_proj"] = pd.to_numeric(r["wprp_proj"], errors="coerce")

    scoped = r[(r["resulted"] == 1) & (r["scratched"] != 1) &
               r["won"].notna() & r["wprp_proj"].notna() & r["date"].notna()].copy()
    field_counts = scoped.groupby("race_id")["race_id"].transform("size")
    scoped = scoped[field_counts >= 4].copy()

    report("FULL AVAILABLE HISTORY (mixed model versions)", scoped)
    report("CURRENT ARCHITECTURE ONLY (since 2026-08-09)", scoped[scoped["d"] >= "2026-08-09"])


if __name__ == "__main__":
    run()
