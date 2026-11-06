"""6 Nov 2026 (owner: pull every first Australian start and compare). First Australian start = a run in Australia whose previous run was overseas or in Hong Kong (overseas = an un-numbered going word at a track
that is not an Australian venue, or Sha Tin / Happy Valley), 2024-2026. For each, the actual page rating against (a) the plain formula and (b) the context-model Proj trained only on earlier data
(three forward folds: test 2024 fit before 2024, test 2025 fit before 2025, test 2026 fit before 2026; page store only, as train_ctx.py without converted history). Reports mean and median miss, RMSE and
within-6 for each, split by whether the run was excused (trouble comment), by rating level and by 1-2 / 3+ earlier runs. Same measures for all other Australian runs as the baseline.
Run: PYTHONPATH=.:projection PROJECTION_RATINGS=toprate python research/first_aus_start_compare.py"""
import glob, gzip, json, re, sys, warnings
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, 'projection')
import ctx as C

P = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
PAT = [r'\bvet|lame|bled|bleed|sore|broke down|pulled up|eased down|tailed off|fell\b|lost (its )?rider|unseat|tongue',
       r'slow(ly)? (to )?(begin|away|out)|slowly away|missed the start|began awkwardly|dwelt|jumped (late|awkward)|awkward(ly)? (start|away)|fumbled',
       r'check(ed)?\b|blocked|held up|no room|shut off|denied a run|hampered|interfer|bumped|crowded|squeezed|clipped',
       r'resent|failed to|raced (very )?keen|over.?rac|pulled hard|laboured|spat|fought|did not (try|extend|respond)|ungenuine']
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        rows.append((r['horse_id'], r['date'], r.get('commentsSteward') or '', r.get('commentsVideo') or '', str(r.get('track')), str(r.get('going'))))
cm = pd.DataFrame(rows, columns=['horse_id', 'date', 'steward', 'video', 'trk', 'gostr']); cm['horse_id'] = pd.to_numeric(cm.horse_id, errors='coerce'); cm['date'] = pd.to_datetime(cm.date)
txt = (cm.steward + ' | ' + cm.video).str.lower(); cm['exc'] = False
for p in PAT: cm['exc'] |= txt.str.contains(p, regex=True)
aus = set(pd.read_csv('runners.csv', usecols=['venue', 'state'], low_memory=False).query("state != 'HK'").venue.str.lower().unique())
for _f in sorted(glob.glob('race_results_20*.csv.gz')) + ['runners_archive.csv.gz']:
    try:
        _x = pd.read_csv(_f, usecols=lambda c: c in ('track', 'venue'), compression='gzip', low_memory=False)
        for _c in _x.columns: aus |= set(_x[_c].dropna().astype(str).str.lower().unique())
    except Exception: pass
aus = {a for a in aus if not re.search(r'sha tin|happy valley', a)}
tl, gl = cm.trk.str.lower(), cm.gostr.str.lower()
cm['os'] = (gl.str.match(r'^(firm|fast|good|sand|dead|slow|soft|heavy|yielding)\b') & ~gl.str.contains(r'\d') & ~tl.isin(aus)) | tl.str.contains(r'sha tin|happy valley')
rp = C.training_frame_rel(True)
rp = rp.merge(cm[['horse_id', 'date', 'exc', 'os']].drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
rp['exc'] = rp.exc.fillna(False).astype(bool); rp['os'] = rp.os.fillna(False).astype(bool)
rp = rp.sort_values(['horse_id', 'date']); rp['os_last'] = rp.groupby('horse_id').os.shift(1).fillna(False).astype(bool)
pg = rp[rp.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
F0 = list(C.FEATS2); F1 = F0 + list(C.REL_FEATS2); rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
out = []
for year in (2024, 2025, 2026):
    cut = pd.Timestamp(f'{year}-01-01'); es = cut - pd.Timedelta(days=92); end = pd.Timestamp(f'{year + 1}-01-01')
    tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[(pg.date >= cut) & (pg.date < end)].copy()
    if len(tr) < 5000 or len(va) < 500: print('skip', year, len(tr), len(va)); continue
    m0 = lgb.LGBMRegressor(**P).fit(tr[F0], tr.resid, eval_set=[(va[F0], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[F1], rel(tr).resid, eval_set=[(rel(va)[F1], rel(va).resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    use = (te.n >= C.REL_MIN_RUNS).values
    c = m0.predict(te[F0]); c1 = np.full(len(te), np.nan); c1[use] = m1.predict(te.loc[use, F1])
    te['corr'] = np.where(use, c1, c); te['e'] = te.resid - te['corr']; te['year'] = year
    out.append(te); print(year, 'train', len(tr), 'test', len(te), 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
t = pd.concat(out)
t['first'] = t.os_last & ~t.os
t = t[~t.os]
def line(name, a):
    if len(a) < 15: print(f'{name:46s} n={len(a):5d} (too few)'); return
    f = lambda x: f'mean {x.mean():+5.2f} median {x.median():+5.2f} RMSE {np.sqrt((x**2).mean()):5.2f} w6 {100*(x.abs()<=6).mean():4.1f}%'
    print(f'{name:46s} n={len(a):6d} | formula {f(a.resid)} | Proj {f(a.e)}')
print('\nformula vs context-model Proj (actual minus each):')
line('first Australian start (all years)', t[t['first']]); line('every other Australian run', t[~t['first']])
for y in (2024, 2025, 2026): line(f'  first start, {y}', t[t['first'] & (t.year == y)])
fs = t[t['first']]
line('first start, not excused', fs[~fs.exc]); line('first start, excused', fs[fs.exc])
line('first start, 1-2 earlier runs', fs[fs.n < 3]); line('first start, 3+ earlier runs', fs[fs.n >= 3])
m3 = fs[['r1', 'r2', 'r3']].mean(axis=1)
for lo, hi in ((0, 80), (80, 90), (90, 95), (95, 100), (100, 130)): line(f'first start, last-3 avg {lo}-{hi}', fs[m3.between(lo, hi, inclusive='left')])
line('first start, Proj 90+', fs[(fs.f + fs['corr']) >= 90]); line('first start, Proj 85-95', fs[((fs.f + fs['corr']) >= 85) & ((fs.f + fs['corr']) < 95)])
d = fs.resid ** 2 - fs.e ** 2; print(f'\npaired squared-error gain, Proj over formula, first starts: {d.mean():+.2f} se {d.std()/np.sqrt(len(d)):.2f}  (n={len(fs)})')
b = t[~t['first']]; d = b.resid ** 2 - b.e ** 2; print(f'same, all other Australian runs: {d.mean():+.2f} se {d.std()/np.sqrt(len(d)):.2f}')
