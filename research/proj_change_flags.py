"""Do change flags (same jockey and same track as the last run, rides together before) add anything to the live context inputs? (22 Oct 2026). Runner-page ATW ratings only,
fit before 2026-01-01, scored on 35k held-out 2026 runs, paired squared-error gain per run. Run: PYTHONPATH=. python research/proj_change_flags.py"""
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
pg['pair_n'] = pg.groupby(['horse_id', 'jockey']).cumcount().astype(float)
pg['trk_n'] = pg.groupby(['horse_id', 'track']).cumcount().astype(float)
NEW = ['jock_chg', 'trk_chg', 'pair_n', 'trk_n']
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
big = te.groupby('race').resid.transform('size') >= 4
def run(feats):
    m = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return te.resid - m.predict(te[feats])
def within(e): te['_e'] = e; return np.sqrt(((e - te.groupby('race')._e.transform('mean'))[big] ** 2).mean())
b = run(C.FEATS); print(f"live context: RMSE {np.sqrt((b**2).mean()):.4f} within-race {within(b):.4f}")
for lab, f in (('+ jockey/track change flags', ['jock_chg', 'trk_chg']), ('+ rides together / runs at track', ['pair_n', 'trk_n']), ('+ all four', NEW)):
    e = run(C.FEATS + f); d = b ** 2 - e ** 2
    print(f"{lab:34s} RMSE {np.sqrt((e**2).mean()):.4f} within-race {within(e):.4f}  gain {d.mean():+.3f} pts^2/run (se {d.std()/np.sqrt(len(d)):.3f})")
