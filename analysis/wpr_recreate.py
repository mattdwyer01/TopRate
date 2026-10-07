"""Recreate TopRate WPR from race_results_*.csv.gz (read-only research script).

Structure (confirmed against the KB article "WFA Performance Ratings & Analysis" and 281k rows with atw):
  ATW = RS - K(distance) * margin_lengths          K = max(2750 / distance, 1.5), exact to rounding
  WPR = ATW + 0.8 * (weight_carried + 2*[filly/mare] - WFA(age, month, distance))
RS (race strength) is hand-reviewed by TopRate; here it is predicted (see rs_model) for comparison only.
Run: python analysis/wpr_recreate.py   (writes analysis/wpr_wfa_table.csv)
"""
import glob, numpy as np, pandas as pd

def k_per_length(dist):
    return np.maximum(2750.0 / np.asarray(dist, float), 1.5)

def racing_age(date, foaled):
    dt, fo = pd.to_datetime(date), pd.to_datetime(foaled, errors="coerce")
    sy = np.where(dt.dt.month >= 8, dt.dt.year, dt.dt.year - 1)
    fy = np.where(fo.dt.month >= 8, fo.dt.year, fo.dt.year - 1)
    return (sy - fy + 1) - 1          # -1: matches TopRate's own age labels (3yo = 53.5kg over 1200m in Oct)

def main():
    d = pd.concat(pd.read_csv(f, low_memory=False) for f in sorted(glob.glob("race_results_20*.csv.gz")))
    d = d[(d.isBarrierTrial != 1) & d.wpr.notna() & d.atw.notna() & d.weightCarried.notna() & d.horse_foaled.notna()].copy()
    d["age"] = racing_age(d.date, d.horse_foaled).clip(2, 4)
    d["mon"] = pd.to_datetime(d.date).dt.month
    d["db"] = (d.distance // 100).clip(8, 24)
    d["fm"] = d.horse_sex.isin(["F", "M"]) * 2.0
    d["wfa"] = d.weightCarried + d.fm - (d.wpr - d.atw) / 0.8     # implied WFA for colts/geldings
    trn, te = d[d.date < "2025-09-01"], d[d.date >= "2025-09-01"]
    tab = trn.groupby(["age", "mon", "db"]).wfa.median().rename("wfa_tab").reset_index()
    tab.to_csv("analysis/wpr_wfa_table.csv", index=False)
    te = te.merge(tab, on=["age", "mon", "db"], how="left").dropna(subset=["wfa_tab"])
    pred = te.atw + 0.8 * (te.weightCarried + te.fm - te.wfa_tab)
    print(f"WPR from ATW + WFA table, held-out {len(te)} runs: MAE {np.abs(te.wpr-pred).mean():.2f}, "
          f"within 0.5: {(np.abs(te.wpr-pred)<=0.5).mean():.1%}")
    # margin part: atw vs RS - K*margin, per race
    r = d[d.marginFinish.notna()].copy()
    r["m"] = np.where(r.positionFinish == 1, 0, r.marginFinish)
    r["rs"] = r.atw + k_per_length(r.distance) * r.m
    sd = r.groupby("race_id").rs.std()
    print(f"ATW = RS - K*margin: within-race sd of implied RS, median {sd.median():.3f} (0.1 rounding = 0.03)")

if __name__ == "__main__":
    main()
