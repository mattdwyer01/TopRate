"""Report on data/forward_log (forward_log.py): the 'lower-rated but forward on the map' rules judged on races logged BEFORE the jump.
Price = the last fixed price read before the jump (`price`), normalised in each race to a win chance (races with a book outside 1.05 to 2.0 dropped).
Run: python research/forward_log_report.py [--since YYYY-MM-DD]"""
import argparse, glob, gzip, json
import numpy as np, pandas as pd

ap = argparse.ArgumentParser(); ap.add_argument('--since', default='2000-01-01'); a = ap.parse_args()
rows = []
for f in sorted(glob.glob('data/forward_log/*.json.gz')):
    if f[-18:-8] < a.since: continue
    for k, r in json.load(gzip.open(f, 'rt')).get('rows', {}).items():
        if r.get('gone'): continue
        rows.append({'run_id': k, **r})
d = pd.DataFrame(rows)
if d.empty: raise SystemExit('log is empty')
print('logged runners', len(d), 'races', d.race_id.nunique(), d.date.min(), '..', d.date.max())
if 'won' not in d.columns: raise SystemExit('no labelled races yet (labels are added the day after racing)')
d = d[d.won.notna() & d.price.notna() & d.proj.notna() & d.fgap.notna()].copy()
late = d.proj_made.fillna('') > d.start_time.astype(str).str[:19].str.replace('T', ' ').str.replace(' ', 'T') + 'Z'
print('rows with a Proj made after the start (dropped):', int(late.sum())); d = d[~late]
g = d.groupby('race_id'); d = d[(g.proj.transform('size') >= 6)]
d['p'] = 1 / d.price; bk = d.groupby('race_id').p.transform('sum'); d = d[(bk >= 1.05) & (bk <= 2.0)]
d['imp'] = d.p / d.groupby('race_id').p.transform('sum')
d = d[d.groupby('race_id').won.transform('sum') == 1]
d['top'] = d.proj == d.groupby('race_id').proj.transform('max'); d = d[d.groupby('race_id').top.transform('sum') == 1].copy()
d['gap'] = d.groupby('race_id').proj.transform('max') - d.proj
d['topgap'] = d.race_id.map(d[d.top].set_index('race_id').fgap); d['fwd'] = d.topgap - d.fgap
print('usable races', d.race_id.nunique(), 'runners', len(d), d.date.min(), '..', d.date.max(), d.groupby('map_kind').race_id.nunique().to_dict())

def stat(s):
    if len(s) == 0: return 'n=0'
    ex = s.won.sum() - s.imp.sum(); se = np.sqrt((s.imp * (1 - s.imp)).sum()); roi = (s.won * s.price).mean() * 100 - 100
    w = s[s.won == 1].sort_values('price', ascending=False); s2 = s.drop(w.index[:3]); roi3 = (s2.won * s2.price).mean() * 100 - 100
    return f"n={len(s):5d} win={s.won.mean()*100:5.1f}% imp={s.imp.mean()*100:5.1f}% z={ex/se:5.1f} ROI={roi:6.1f}% ex3={roi3:6.1f}%"
print('top rated:', stat(d[d.top]))
for lo, hi in [(0, 1), (1, 3), (3, 6), (6, 99)]: print(f'  top rated, forecast {lo}-{hi}L:', stat(d[d.top & (d.fgap >= lo) & (d.fgap < hi)]))
for hi in (2, 4, 6):
    b = (d.gap > 0) & (d.gap <= hi) & ~d.top
    print(f'-- 0-{hi} pts below (top excluded)')
    for L in (None, 0, 2, 3, 4, 5):
        mk = b if L is None else b & (d.fwd >= L)
        print(f"   {'any' if L is None else '>=%dL closer' % L:12s}", stat(d[mk]))
d['wk'] = pd.to_datetime(d.date).dt.to_period('W').astype(str)
mk = (d.gap > 0) & (d.gap <= 6) & ~d.top & (d.fwd >= 3)
print('\nweekly, 0-6 pts below and >=3L closer:')
for k, s in d[mk].groupby('wk'): print('  ', k, stat(s))
