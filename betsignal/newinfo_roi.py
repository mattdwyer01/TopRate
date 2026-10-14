"""ROI check for the one new source that carried information (sire): calibrated market + rating form + sire, clean-book races only,
walk-forward 2022-2026, flat $1 at SP. Run after `newinfo.py --build`."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, pandas as pd
from betsignal.newinfo import CACHE, BASE_COLS, GROUPS, design, fit, race_ll

A = pd.read_pickle(f"{CACHE}/newinfo.pkl")
book = (1 / A.sp).groupby(A.race_id).transform("sum")
A = A[(book >= 1.05) & (book <= 1.5)].sort_values("race_id", kind="mergesort").reset_index(drop=True)
for name, cols in (("market+form", BASE_COLS), ("market+form+sire", BASE_COLS + GROUPS["sire"])):
    rows = []
    for ty in range(2022, 2027):
        tr, te = A[A.year <= ty - 1], A[A.year == ty].copy()
        seg = lambda t: np.flatnonzero(np.r_[True, t.race_id.values[1:] != t.race_id.values[:-1]])
        Xtr, ms = design(tr, cols)
        Xte, _ = design(te, cols, ms)
        b = fit(Xtr, seg(tr), tr.win.values)
        _, p = race_ll(Xte, seg(te), te.win.values, b)
        te["ev"] = p * te.sp.values
        te["ret"] = np.where(te.win == 1, te.sp, 0.0)
        rows.append(te)
    T = pd.concat(rows)
    print("==", name)
    for lo in (0.95, 1.0, 1.05, 1.10, 1.20):
        x = T[T.ev > lo]
        if not len(x):
            print(f" ev>{lo}: n=0"); continue
        ex10 = x.drop(x[x.win == 1].nlargest(10, "sp").index)
        print(f" ev>{lo}: n={len(x):6} win {x.win.mean()*100:4.1f}% avg ${x.sp.mean():5.2f} ROI {(x.ret.mean()-1)*100:+6.1f}% ex10 {(ex10.ret.mean()-1)*100:+6.1f}%  yrs",
              " ".join(f"{(x[x.year==y].ret.mean()-1)*100:+.0f}" for y in range(2022, 2027)))
    print(" all runners flat:", f"{(T.ret.mean()-1)*100:+.1f}%", " favourites flat:", f"{(T[T.sp==T.groupby('race_id').sp.transform('min')].ret.mean()-1)*100:+.1f}%")
