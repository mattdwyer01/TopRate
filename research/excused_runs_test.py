"""6 Nov 2026 (owner: are the mean and median tests dragged down by runs with excuses? exclude those when testing). Redoes the main residual tests with the TARGET run split into excused (a trouble word in the steward
or video comment, same definition as proj_flagged_runs.py) and not excused: overall formula residual, rising lightly raced horses, first Australian start after overseas form (and at 95+), and TopRate Base
minus our Proj gap groups (8-12 and 5-8). Comments are written after the race, so excluding excused runs measures the horse's ability, not what a pre-race figure should expect.
Run: PYTHONPATH=. python research/excused_runs_test.py"""
import glob, gzip, json, os, re, sys, warnings
warnings.filterwarnings('ignore')
import numpy as np, pandas as pd
sys.path.insert(0, 'projection')
import ctx as C
rp = C.page_frame(); co = C.coefs(); rp['f'] = C.formula_pred(rp, co); rp['resid'] = rp.wpr - rp.f
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        rows.append((r['horse_id'], r['date'], r.get('commentsSteward') or '', r.get('commentsVideo') or '', str(r.get('track')), str(r.get('going'))))
cm = pd.DataFrame(rows, columns=['horse_id', 'date', 'steward', 'video', 'trk', 'gostr']); cm['horse_id'] = pd.to_numeric(cm.horse_id, errors='coerce'); cm['date'] = pd.to_datetime(cm.date)
rp = rp.merge(cm.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
txt = (rp.steward.fillna('') + ' | ' + rp.video.fillna('')).str.lower()
PAT = [r'\bvet|lame|bled|bleed|sore|broke down|pulled up|eased down|tailed off|fell\b|lost (its )?rider|unseat|tongue',
       r'slow(ly)? (to )?(begin|away|out)|slowly away|missed the start|began awkwardly|dwelt|jumped (late|awkward)|awkward(ly)? (start|away)|fumbled',
       r'check(ed)?\b|blocked|held up|no room|shut off|denied a run|hampered|interfer|bumped|crowded|squeezed|clipped',
       r'resent|failed to|raced (very )?keen|over.?rac|pulled hard|laboured|spat|fought|did not (try|extend|respond)|ungenuine']
rp['exc'] = False
for p in PAT: rp['exc'] |= txt.str.contains(p, regex=True)
rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True)
pg = rp[rp.f.notna() & (rp.date >= '2025-01-01')].copy()
def show(name, a):
    ne, ex = a[~a.exc], a[a.exc]
    f = lambda x: f'n={len(x):6d} mean {x.resid.mean():+5.2f} median {x.resid.median():+5.2f} RMSE {np.sqrt((x.resid**2).mean()):5.2f}'
    print(f'{name:40s} ALL {f(a)} | NOT excused {f(ne)} | excused {len(ex)} ({100*len(ex)/len(a):.0f}%) mean {ex.resid.mean():+.2f}')
print(f'excused share of all rated runs since 2025: {100*pg.exc.mean():.1f}%\n-- formula residual (actual - formula) --')
show('all runs', pg)
r1, r2, r3 = pg.r1, pg.r2, pg.r3
up = (r1 > r2) & (r2 > r3) & ((r1 - r3) >= 5)
show('rising 3 straight (rise>=5)', pg[up]); show('rising, light (n<=11)', pg[up & (pg.n <= 11)])
# overseas: first Australian start
aus = set(pd.read_csv('runners.csv', usecols=['venue', 'state'], low_memory=False).query("state != 'HK'").venue.str.lower().unique())
for _f in sorted(glob.glob('race_results_20*.csv.gz')) + ['runners_archive.csv.gz']:
    try:
        _x = pd.read_csv(_f, usecols=lambda c: c in ('track', 'venue'), compression='gzip', low_memory=False)
        for _c in _x.columns: aus |= set(_x[_c].dropna().astype(str).str.lower().unique())
    except Exception: pass
aus = {a for a in aus if not re.search(r'sha tin|happy valley', a)}
tl = rp.trk.fillna('').str.lower(); gl = rp.gostr.fillna('').str.lower()
rp['os'] = (gl.str.match(r'^(firm|fast|good|sand|dead|slow|soft|heavy|yielding)\b') & ~gl.str.contains(r'\d') & ~tl.isin(aus)) | tl.str.contains(r'sha tin|happy valley')
rp['os_last'] = rp.groupby('horse_id').os.shift(1)
fa = rp[rp.f.notna() & (rp.date >= '2018-01-01') & ~rp.os & (rp.os_last == True)]
print('\n-- first Australian start after an overseas run (2018 on) --'); show('first Aus start', fa)
show('first Aus start, last-3 avg 95+', fa[fa[['r1', 'r2', 'r3']].mean(axis=1) >= 95])
# Base (Nett) minus Proj
r = pd.read_csv('runners.csv', low_memory=False)
r = r[(r.date >= '2026-10-16') & r.wpr_nett.notna() & r.wprp_proj.notna() & (r.scratched.fillna(0) != 1)].copy(); r['h'] = r.horse.astype(str).str.lower()
act = {}
for f in sorted(glob.glob('data/tr_results/*.json.gz')):
    d = json.load(gzip.open(f)); dt = f.split('/')[-1][:10]
    def walk(o):
        if isinstance(o, dict):
            if 'atw' in o and ('horse' in o or 'name' in o): yield o
            for v in o.values(): yield from walk(v)
        elif isinstance(o, list):
            for v in o: yield from walk(v)
    for o in walk(d):
        if o.get('atw') is not None: act[(str(o.get('horse') or o.get('name')).lower(), dt)] = o['atw']
r['act'] = [act.get((h, str(dd)[:10])) for h, dd in zip(r.h, r.date)]
r = r[r.act.notna()].copy(); r['act'] = r.act.astype(float); r['horse_id'] = pd.to_numeric(r.horse_id, errors='coerce'); r['date'] = pd.to_datetime(r.date)
r = r.merge(rp[['horse_id', 'date', 'exc']].drop_duplicates(['horse_id', 'date']), on=['horse_id', 'date'], how='left')
r['gap'] = r.wpr_nett - r.wprp_proj
print(f"\n-- Base (Nett) minus our Proj, actual TopRate rating (comment flag found for {100*r.exc.notna().mean():.0f}% of these) --")
for lo, hi in ((0, 5), (5, 8), (8, 12)):
    a = r[r.gap.between(lo, hi, inclusive='left') & r.exc.notna()]
    for nm, s in (('all', a), ('not excused', a[~a.exc.astype(bool)])):
        print(f'  gap [{lo},{hi}) {nm:12s} n={len(s):5d} actual-Nett mean {(s.act-s.wpr_nett).mean():+5.2f} median {(s.act-s.wpr_nett).median():+5.2f} | actual-Proj mean {(s.act-s.wprp_proj).mean():+5.2f} median {(s.act-s.wprp_proj).median():+5.2f} | ran at/above Nett {100*(s.act>=s.wpr_nett).mean():.1f}%')
