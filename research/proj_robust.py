"""Robust training and compromised runs (22 Oct 2026). Runner-page ATW ratings only; the deployed relevance model for horses with 3+ earlier runs (projection/ctx.py inputs), fit before
2026-01-01 with early stopping on 2025-10..12, scored on the 2026 held-out runs. Variants:
  deployed        : as shipped
  drop excused    : drop TRAINING runs that were bad (more than 12 below the formula) AND carry a strong trouble word (vet/lame/bled, resented/failed to)
  drop outliers   : drop TRAINING runs more than 20 points from the formula
  huber           : Huber loss (alpha 8) so outliers pull less
  prev-bad flags  : give the model the history facts: was the previous run bad and why (vet, slow away, checked, resented, no excuse), bad runs in the last 4
  flags + huber   : both
Scores on the same held-out runs: RMSE and median error on all runs and on clean runs (not bad+excused), bias, and the winner test inside each race as the runner-page store holds it
(cross-fitted scale, paired difference to deployed). Run: PYTHONPATH=. python research/proj_robust.py"""
import glob, gzip, json, os, sys, warnings
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

CACHE = os.environ.get('ROBUST_FRAME', 'robust_frame.pkl')
if os.path.exists(CACHE):
    rp = pd.read_pickle(CACHE)
else:
    rp = C.training_frame_rel()
    rows = []
    for f in sorted(glob.glob('data/tr_form/*.json.gz')):
        for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
            if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
            rows.append((r['horse_id'], r['date'], r.get('commentsSteward') or '', r.get('commentsVideo') or ''))
    cm = pd.DataFrame(rows, columns=['horse_id', 'date', 'steward', 'video']); cm['horse_id'] = pd.to_numeric(cm.horse_id, errors='coerce'); cm['date'] = pd.to_datetime(cm.date)
    rp = rp.merge(cm.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
    rp.to_pickle(CACHE)
txt = (rp.steward.fillna('') + ' | ' + rp.video.fillna('')).str.lower()
PAT = {'vet': r'\bvet|lame|bled|bleed|sore|arrhythm|cardiac|respiratory|amiss|distress|broke down|pulled up|eased down|tailed off|fell\b|lost (its )?rider|unseat|tongue|noticeably',
       'slow': r'slow(ly)? (to )?(begin|away|out)|slowly away|missed the start|began awkwardly|dwelt|jumped (late|awkward)|awkward(ly)? (start|away)|fumbled',
       'chk': r'check(ed)?\b|blocked|held up|no room|shut off|denied a run|hampered|interfer|bumped|crowded|squeezed|clipped',
       'res': r'resent|failed to|raced (very )?keen|over.?rac|pulled hard|laboured|spat|fought|did not (try|extend|respond)|ungenuine'}
for k, p in PAT.items(): rp['x_' + k] = txt.str.contains(p, regex=True)
rp['strong'] = rp.x_vet | rp.x_res
rp['bad'] = (rp.resid < -12)
rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True)
g = rp.groupby('horse_id')
for k in PAT: rp['pb_' + k] = (g['bad'].shift(1).fillna(False) & g['x_' + k].shift(1).fillna(False)).astype(float)
rp['pb_noex'] = (g['bad'].shift(1).fillna(False) & ~g[['x_vet', 'x_slow', 'x_chk', 'x_res']].shift(1).fillna(False).any(axis=1)).astype(float)
bs = pd.concat([g['bad'].shift(k).astype(float) for k in (1, 2, 3, 4)], axis=1)
rp['bad4'] = bs.sum(axis=1); rp['bad4x'] = pd.concat([(g['bad'].shift(k).fillna(False) & g['strong'].shift(k).fillna(False)).astype(float) for k in (1, 2, 3, 4)], axis=1).sum(axis=1)
FLAGF = ['pb_vet', 'pb_slow', 'pb_chk', 'pb_res', 'pb_noex', 'bad4', 'bad4x']
pg = rp[rp.f.notna() & (rp.n >= C.REL_MIN_RUNS)].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F1 = C.FEATS + C.REL_FEATS; F2 = F1 + FLAGF
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
def fit(feats, a, b, **kw):
    return lgb.LGBMRegressor(n_estimators=4000, **{**P, **kw}).fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
dropx = lambda d: d[~(d.bad & d.strong)]
dropo = lambda d: d[d.resid.abs() <= 20]
V = {'deployed': (F1, tr, va, {}), 'drop excused': (F1, dropx(tr), dropx(va), {}), 'drop outliers': (F1, dropo(tr), dropo(va), {}), 'huber': (F1, tr, va, dict(objective='huber', alpha=8.0)),
     'prev-bad flags': (F2, tr, va, {}), 'flags + huber': (F2, tr, va, dict(objective='huber', alpha=8.0))}
clean = ~(te.bad & te.strong)
print(f"held-out runs {len(te):,} ({int((~clean).sum()):,} bad AND strongly excused = {100*(~clean).mean():.1f}%); training runs {len(tr):,}\n")
te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
te['won'] = (te.positionFinish == 1).astype(int); te['nr'] = te.groupby('race').won.transform('size'); te['nw'] = te.groupby('race').won.transform('sum')
for name, (feats, a, b, kw) in V.items():
    m = fit(feats, a, b, **kw); te['mu_' + name] = te.f + m.predict(te[feats]); te['e_' + name] = te.wpr - te['mu_' + name]
    print(f"  fitted {name:16s} trees {m.best_iteration_:4d} on {len(a):,} training runs", flush=True)
r = lambda x: float(np.sqrt((x ** 2).mean()))
print(f"\n{'variant':16s} {'RMSE all':>9s} {'MAE all':>8s} {'median err':>10s} {'bias':>6s} | {'RMSE clean':>10s} {'MAE clean':>9s}")
for name in V:
    e = te['e_' + name]; print(f"{name:16s} {r(e):9.3f} {e.abs().mean():8.3f} {e.median():+10.2f} {e.mean():+6.2f} | {r(e[clean]):10.3f} {e[clean].abs().mean():9.3f}")
d = te[(te.nr >= 3) & (te.nw == 1)].copy(); d['rid'] = d.race.astype('category').cat.codes
def ll(df, col, b):
    s = b * df[col].values; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]
fitb = lambda df, c: minimize(lambda b: -ll(df, c, b[0]).mean(), [0.15], method='L-BFGS-B').x[0]
dates = sorted(d.date.unique()); half = dates[len(dates) // 2]; A, B = d[d.date < half], d[d.date >= half]
out = {n: np.concatenate([ll(B, 'mu_' + n, fitb(A, 'mu_' + n)), ll(A, 'mu_' + n, fitb(B, 'mu_' + n))]) for n in V}
print(f"\nwinner test ({d.rid.nunique():,} store races, {len(d):,} runners): winner log-lik, gain vs deployed")
for n in V:
    dd = out[n] - out['deployed']; print(f"  {n:16s} {out[n].mean():8.4f}  {dd.mean():+.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})")
te.to_pickle(os.environ.get('ROBUST_OUT', 'robust_te.pkl'))
