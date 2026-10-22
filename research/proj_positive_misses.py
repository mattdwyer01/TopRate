"""The runs that beat Proj by more than 12 points (22 Oct 2026): what was different before the race? Held-out 2026 runs (live context Proj, fit before 2026-01), runner-page
ATW ratings only. Each pre-race fact is tabled by the share of runs with a big beat (and big under-performance for contrast) against the base rate. Run: PYTHONPATH=. python research/proj_positive_misses.py"""
import os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C
rp = C.training_frame()
pg = rp[rp.f.notna()].copy().sort_values(['horse_id', 'date']).reset_index(drop=True)
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
g = pg.groupby('horse_id')
pg['jock_chg'] = (pg.jockey != g.jockey.shift(1)).astype(float).where(g.jockey.shift(1).notna())
pg['trk_chg'] = (pg.track != g.track.shift(1)).astype(float).where(g.track.shift(1).notna())
pg['cls_prev'] = g.cls.shift(1)
pg['lprev_win'] = (g.positionFinish.shift(1) == 1).astype(float).where(g.positionFinish.shift(1).notna())
pg['prev_resid'] = g.resid.shift(1)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
m = lgb.LGBMRegressor(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
m.fit(tr[C.FEATS], tr.resid, eval_set=[(va[C.FEATS], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
te['e'] = te.resid - m.predict(te[C.FEATS])
te['up'] = (te.e > 12).astype(int); te['dn'] = (te.e < -12).astype(int)
sp = pd.to_numeric(te.priceStarting, errors='coerce'); te['sp'] = sp
te['trend'] = te.r1 - te[['r2', 'r3', 'r4']].mean(axis=1)
print(f"held-out runs {len(te):,}; big beat (more than 12 above Proj) {te.up.sum():,} = {100*te.up.mean():.1f}%; big under-performance {te.dn.sum():,} = {100*te.dn.mean():.1f}%")
def tab(name, s):
    t = te.groupby(s, observed=True).agg(n=('up', 'size'), up=('up', 'mean'), dn=('dn', 'mean'), mean=('e', 'mean'))
    print(f"\n{name}"); [print(f"   {str(k):22s} n={int(r.n):6d}  big beat {100*r.up:4.1f}%  big under {100*r.dn:4.1f}%  mean miss {r['mean']:+.2f}") for k, r in t.iterrows()]
tab('earlier runs', pd.cut(te.n, [0, 2, 5, 8, 99]))
tab('days since last run', pd.cut(te.d_last, [0, 14, 28, 60, 120, 9999]))
tab('jockey changed since last run', te.jock_chg)
tab('track changed since last run', te.trk_chg)
tab('won last start', te.lprev_win)
tab("last run's miss vs formula (resid)", pd.cut(te.prev_resid, [-99, -12, -5, 5, 12, 99]))
tab('rating trend (last vs avg of 2-4)', pd.cut(te.trend, [-99, -10, -4, 4, 10, 99]))
tab('weight change (kg)', pd.cut(te.wt_chg, [-99, -3, -1, 1, 3, 99]))
tab('starting price', pd.cut(te.sp, [0, 3, 5, 10, 20, 50, 9999]))
tab('projected level', pd.cut(te.f, [0, 60, 70, 80, 90, 200]))
tab('field size', pd.cut(te.field_size, [0, 8, 10, 12, 99]))
up = te[te.up == 1]
print(f"\nbig beats: {100*(up.positionFinish == 1).mean():.0f}% won, {100*(up.positionFinish <= 3).mean():.0f}% placed, median price ${up.sp.median():.1f} vs ${te.sp.median():.1f} all runs")
print(f"horses with 2+ big beats in 2026: {int((up.groupby('horse_id').size() >= 2).sum())} of {up.horse_id.nunique()}")
