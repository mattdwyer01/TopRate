"""Flagged runs (22 Oct 2026): which past runs were materially affected by something other than the horse's ability, and what do they do to the NEXT run's projection?
Runner-page ATW ratings only. A run is 'excused' when the steward or video comment records trouble (slow away, checked, blocked, hampered, vet, lame, resented, failed to ...)
and 'bad' when its rating came in more than 12 below the formula. Table: the formula's miss on the NEXT run (actual minus formula, positive = the horse did better than the history
said) after an excused bad run, an unexcused bad run, an excused run that was not bad, and an ordinary run. If the next run bounces back after an excused bad run, that run
should not drag the history. Run: PYTHONPATH=. python research/proj_flagged_runs.py"""
import glob, gzip, json, os, re, sys, warnings
warnings.filterwarnings('ignore')
import numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

rp = C.page_frame()
co = C.coefs(); rp['f'] = C.formula_pred(rp, co); rp['resid'] = rp.wpr - rp.f
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        rows.append((r['horse_id'], r['date'], r.get('commentsSteward') or '', r.get('commentsVideo') or ''))
cm = pd.DataFrame(rows, columns=['horse_id', 'date', 'steward', 'video']); cm['horse_id'] = pd.to_numeric(cm.horse_id, errors='coerce'); cm['date'] = pd.to_datetime(cm.date)
rp = rp.merge(cm.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
txt = (rp.steward.fillna('') + ' | ' + rp.video.fillna('')).str.lower()
PAT = {'vet/lame/bled/sore': r'\bvet|lame|bled|bleed|sore|broke down|pulled up|eased down|tailed off|fell\b|lost (its )?rider|unseat|tongue',
       'slow away/dwelt': r'slow(ly)? (to )?(begin|away|out)|slowly away|missed the start|began awkwardly|dwelt|jumped (late|awkward)|awkward(ly)? (start|away)|fumbled',
       'checked/blocked/held up': r'check(ed)?\b|blocked|held up|no room|shut off|denied a run|hampered|interfer|bumped|crowded|squeezed|clipped',
       'resented/failed to/keen': r'resent|failed to|raced (very )?keen|over.?rac|pulled hard|laboured|spat|fought|did not (try|extend|respond)|ungenuine'}
for k, p in PAT.items(): rp['x_' + k] = txt.str.contains(p, regex=True)
rp['excused'] = rp[['x_' + k for k in PAT]].any(axis=1)
print(f"{len(rp):,} rated runs with a formula figure: {rp.f.notna().sum():,}. Excused (a trouble word in the steward or video comment): {100*rp.excused.mean():.1f}% of runs")
print('share by family:', {k: round(100 * rp['x_' + k].mean(), 1) for k in PAT})
rp = rp.sort_values(['horse_id', 'date'])
g = rp.groupby('horse_id')
rp['bad'] = rp.resid < -12
rp['next_resid'] = g.resid.shift(-1); rp['next_f'] = g.f.shift(-1); rp['next_gap'] = (g.date.shift(-1) - rp.date).dt.days
z = rp[rp.next_resid.notna() & rp.resid.notna()].copy()
z['kind'] = np.select([z.bad & z.excused, z.bad & ~z.excused, ~z.bad & z.excused], ['bad AND excused', 'bad, no excuse', 'excused, not bad'], 'ordinary')
t = z.groupby('kind').agg(n=('next_resid', 'size'), next_miss=('next_resid', 'mean'), median=('next_resid', 'median'), sd=('next_resid', 'std'))
t['share'] = 100 * t.n / t.n.sum(); print('\nformula miss on the NEXT run (positive = better than the history said):'); print(t.round(2).to_string())
print('\nby family, bad runs only (next-run miss):')
for k in PAT:
    s = z[z.bad & z['x_' + k]]; print(f"   {k:28s} n={len(s):5d} next miss {s.next_resid.mean():+.2f} (median {s.next_resid.median():+.2f}); bad runs without it {z[z.bad & ~z['x_' + k]].next_resid.mean():+.2f}")
print('\nnext-run miss after a bad excused run by days to the next run:')
s = z[z.bad & z.excused]
print(s.groupby(pd.cut(s.next_gap, [0, 14, 28, 70, 9999])).next_resid.agg(['size', 'mean']).round(2).to_string())
# top phrases among bad runs
w = txt[rp.bad & rp.resid.notna()].str.findall(r'[a-z][a-z\-]{3,}').explode().value_counts()
base = txt[~rp.bad & rp.resid.notna()].str.findall(r'[a-z][a-z\-]{3,}').explode().value_counts()
nb, no = (rp.bad & rp.resid.notna()).sum(), (~rp.bad & rp.resid.notna()).sum()
lift = pd.DataFrame({'bad': w, 'ok': base}).fillna(0); lift = lift[lift.bad >= 40]; lift['lift'] = (lift.bad / nb) / ((lift.ok + 1) / no)
print('\nwords most over-represented in bad runs (count in bad runs, lift):'); print(lift.sort_values('lift', ascending=False).head(25).round(1).to_string())
rp[['horse_id', 'date', 'excused', 'bad']].to_pickle(os.environ.get('FL_OUT', 'flags.pkl'))
