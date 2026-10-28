"""Does the meeting's own lean (earlier races on the day: did leaders or closers win?) change how the 'lower-rated but forward' runners do? 7 years of results files.
Lean of a race = Spearman(position at 800m, finishing position), + = leaders did better (fields 6+). Meeting lean = mean over the 3+ EARLIER races at the same track and date
(races ordered by race_id: the results files have no race number). Run: python research/fwd_map_meeting_lean.py <y10.pkl from fwd_map_10yr.py>"""
import glob, sys
import numpy as np, pandas as pd

d = pd.read_pickle(sys.argv[1]); d = d[d.fwd.notna()].copy()
cols = ['race_id', 'date', 'track', 'position800m', 'positionFinish', 'barrier', 'field_size', 'isBarrierTrial', 'is_jumpout']
fs = [f for f in sorted(glob.glob('race_results_20*.csv.gz')) if 'rc' not in f]
r = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(cols), low_memory=False) for f in fs])
r = r[(~r.isBarrierTrial.astype(bool)) & (~r.is_jumpout.fillna(False).astype(bool))]
r['race_id'] = r.race_id.astype(str); r['date'] = pd.to_datetime(r.date)
r = r[r.position800m.notna() & r.positionFinish.notna() & (r.groupby('race_id').race_id.transform('size') >= 6)]
def lean(g):
    return pd.Series(dict(lead=g.position800m.rank().corr(g.positionFinish.rank()), draw=g.barrier.rank().corr(g.positionFinish.rank()) if g.barrier.notna().all() else np.nan))
rl = r.groupby(['date', 'track', 'race_id']).apply(lean).reset_index()
rl['race_i'] = rl.race_id.astype(np.int64)
rl = rl.sort_values(['date', 'track', 'race_i'])
rl['n_prev'] = rl.groupby(['date', 'track']).cumcount()
for c in ('lead', 'draw'):
    cs = rl.groupby(['date', 'track'])[c].cumsum() - rl[c]
    rl['prev_' + c] = np.where(rl.n_prev >= 3, cs / rl.n_prev.replace(0, np.nan), np.nan)
d = d.merge(rl[['race_id', 'prev_lead', 'prev_draw', 'n_prev']], on='race_id', how='left')
h = d[d.prev_lead.notna()].copy()
print('races with a meeting lean', h.race_id.nunique(), 'of', d.race_id.nunique(), flush=True)
cuts = h.prev_lead.quantile([.2, .4, .6, .8]).round(3).tolist(); print('quintile cuts (earlier-races leader lean):', cuts)
h['lb'] = pd.qcut(h.prev_lead, 5, labels=['1 leaders hurt', '2', '3', '4', '5 leaders favoured'])
h['half'] = np.where(h.date < '2023-01-01', '2019-22', '2023-26')
def st(s):
    if len(s) == 0: return 'n=0'
    ex = s.won.sum() - s.imp.sum(); se = np.sqrt((s.imp * (1 - s.imp)).sum()); roi = (s.won * s.price).mean() * 100 - 100
    return f"n={len(s):6d} win={s.won.mean()*100:5.1f}% imp={s.imp.mean()*100:5.1f}% exc={(s.won.mean()-s.imp.mean())*100:5.2f} z={ex/se:5.1f} ROI={roi:6.1f}%"
rules = {'forward lower-rated (0-6 below, >=3L forward)': (h.gap > 0) & (h.gap <= 6) & ~h.top & (h.fwd >= 3),
         'forward lower-rated (0-2 below, not behind)': (h.gap > 0) & (h.gap <= 2) & ~h.top & (h.fwd >= 0),
         'back lower-rated (0-6 below, >=3L BEHIND)': (h.gap > 0) & (h.gap <= 6) & ~h.top & (h.fwd <= -3),
         'top rated, history gap <=3L': h.top & (h.gh3 <= 3), 'top rated, history gap >3L': h.top & (h.gh3 > 3)}
for lab, mk in rules.items():
    print('\n', lab)
    for k, g in h[mk].groupby('lb', observed=True): print('   ', f'{k:20s}', st(g))
print('\nEXTREME meeting leans (forward lower-rated, 0-6 below, >=3L):')
mk = rules['forward lower-rated (0-6 below, >=3L forward)']
for lab, m2 in [('leaders strongly favoured (lean >= +0.35)', h.prev_lead >= .35), ('leaders favoured (+0.20 to +0.35)', h.prev_lead.between(.2, .35, inclusive='left')),
                ('neutral (-0.05 to +0.20)', h.prev_lead.between(-.05, .2, inclusive='left')), ('leaders hurt (< -0.05)', h.prev_lead < -.05)]:
    s = h[mk & m2]; print('   ', f'{lab:44s}', st(s), '| halves:', ' / '.join(f"{k} z{(g.won.sum()-g.imp.sum())/np.sqrt((g.imp*(1-g.imp)).sum()):.1f}" for k, g in s.groupby('half')))
print('\nSTRONG lean AND rule, by rail/going:')
sl = h[mk & (h.prev_lead >= .25)]
sl['rb'] = pd.cut(sl.rail_m, [-1, 0, 4, 9, 100], labels=['true rail', '+1-4m', '+5-9m', '+10m+'])
for v, g in sl.groupby('rb', observed=True):
    if len(g) > 150: print('   rail', f'{v!s:10s}', st(g))
sl['gg'] = sl.going.fillna('?').astype(str).str.extract(r'^([A-Za-z]+)')[0]
for v, g in sl.groupby('gg'):
    if len(g) > 150: print('   going', f'{v!s:10s}', st(g))
h['lp'] = np.log(h.imp); h['gz'] = (h.gh3 - h.groupby('race_id').gh3.transform('mean')); h['x'] = h.gz * h.prev_lead; h['rz'] = h.rat - h.groupby('race_id').rat.transform('mean')
sub = h[h.race_id.isin(h.race_id.drop_duplicates().sample(12000, random_state=1))]
cols2 = ['lp', 'rz', 'gz', 'x']
G = [(g[cols2].values.astype(float), int(np.argmax(g.won.values))) for _, g in sub.groupby('race_id')]
b = np.zeros(4)
for _ in range(20):
    gr = np.zeros(4); H = np.zeros((4, 4))
    for x, i in G:
        s = x @ b; p = np.exp(s - s.max()); p /= p.sum(); m = p @ x; gr += x[i] - m; H -= (x.T * p) @ x - np.outer(m, m)
    b = b - np.linalg.solve(H, gr)
print('\nconditional logit (12,000 races): coef [price, rating, history gap(L), gap x earlier-races leader lean] =', b.round(4), 'se', np.sqrt(np.diag(np.linalg.inv(-H))).round(4))
