"""6 Nov 2026 (owner: show a 'clean-run' figure). Calibrate how far above the Proj a horse typically runs when the run has no trouble comment (steward or video: slow away, checked, blocked, hampered, vet,
lame, resented, failed to; same words as excused_runs_test.py). Deployed-style context model (page store, fit before 2026-01, early stop 2025-10..12), held-out 2026. The offset is fitted on 2026-01..06
and checked on 2026-07 on, by earlier-run count. Comments are written after the race, so this describes a trouble-free run, not what to expect on average.
Run: PYTHONPATH=.:projection PROJECTION_RATINGS=toprate python research/clean_run_offset.py"""
import glob, gzip, json, sys, warnings
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
        rows.append((r['horse_id'], r['date'], r.get('commentsSteward') or '', r.get('commentsVideo') or ''))
cm = pd.DataFrame(rows, columns=['horse_id', 'date', 'steward', 'video']); cm['horse_id'] = pd.to_numeric(cm.horse_id, errors='coerce'); cm['date'] = pd.to_datetime(cm.date)
txt = (cm.steward + ' | ' + cm.video).str.lower(); cm['exc'] = False
for p in PAT: cm['exc'] |= txt.str.contains(p, regex=True)
rp = C.training_frame_rel(True)
pg = rp[rp.f.notna()].copy()
pg = pg.merge(cm[['horse_id', 'date', 'exc']].drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left'); pg['exc'] = pg.exc.fillna(False).astype(bool)
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
F0 = list(C.FEATS2); F1 = F0 + list(C.REL_FEATS2); rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
m0 = lgb.LGBMRegressor(**P).fit(tr[F0], tr.resid, eval_set=[(va[F0], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[F1], rel(tr).resid, eval_set=[(rel(va)[F1], rel(va).resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
use = (te.n >= C.REL_MIN_RUNS).values
c = m0.predict(te[F0]); c1 = np.full(len(te), np.nan); c1[use] = m1.predict(te.loc[use, F1])
te['e'] = te.resid - np.where(use, c1, c)          # actual minus the deployed-style Proj
h1, h2 = te[te.date < '2026-07-01'], te[te.date >= '2026-07-01']
q = lambda x: f'mean {x.e.mean():+5.2f} median {x.e.median():+5.2f} p25 {x.e.quantile(.25):+5.2f} p75 {x.e.quantile(.75):+5.2f}'
print(f'held-out 2026: n={len(te)}  excused share {100*te.exc.mean():.1f}%')
for nm, a in (('first half (fit window)', h1), ('second half (check)', h2)):
    print(f'\n{nm}')
    for lab, s in (('all runs', a), ('not excused', a[~a.exc]), ('excused', a[a.exc])): print(f'  {lab:14s} n={len(s):6d} {q(s)}')
    for lab, m in (('under 3 earlier runs', a.n < 3), ('3-7 earlier runs', a.n.between(3, 7)), ('8+ earlier runs', a.n >= 8)):
        s = a[m & ~a.exc]; print(f'  not excused, {lab:22s} n={len(s):6d} {q(s)}')
off = float(h1[~h1.exc].e.median()); off_mean = float(h1[~h1.exc].e.mean())
print(f'\noffset (median of not-excused misses, first half): {off:+.2f}   (mean {off_mean:+.2f})')
s = h2[~h2.exc]
for nm, k in (('Proj', 0.0), (f'Proj + {off:.1f}', off)):
    e = s.e - k; print(f'  second half, not excused, vs {nm:14s}: within 3 {100*(e.abs()<=3).mean():.1f}%  within 6 {100*(e.abs()<=6).mean():.1f}%  median miss {e.median():+.2f}  share above {100*(e>0).mean():.1f}%')
s = h2
for nm, k in (('Proj', 0.0), (f'Proj + {off:.1f}', off)):
    e = s.e - k; print(f'  second half, ALL runs,    vs {nm:14s}: within 3 {100*(e.abs()<=3).mean():.1f}%  within 6 {100*(e.abs()<=6).mean():.1f}%  median miss {e.median():+.2f}  share above {100*(e>0).mean():.1f}%')
