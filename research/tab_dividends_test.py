"""Place and exotic bets on the Proj, judged at real TAB dividends (10 Nov 2026).

tab_dividends.csv holds VIC TAB tote dividends per $1 (Win, Place, Quinella,
Exacta, Duet, Trifecta, FirstFour) captured by the TAB poller from 2 Oct 2026.
Races are joined to runners.csv on date, venue and race number; a race is used
when every runner still in it has a logged Proj (wprp_proj, the pre-race figure)
and a tab number. Rankings compared: Proj, the direct finishing-position model
(data/direct_scores, from 14 Oct), and the market (last fixed price, a reference).
Every structure is a flat $1 a combination. ROI is return / cost - 1; 'ex3'
removes the three biggest returning races; 'H1/H2' are the two date halves.

Run: PYTHONPATH=. python research/tab_dividends_test.py
"""
import glob, json, itertools
import numpy as np, pandas as pd
from rc_field_rows import norm_venue

D = pd.read_csv('tab_dividends.csv')
D = D[D.status == 'Paying']
D['v'] = D.venue.str.split('@').str[-1].str.strip().map(norm_venue)
D['sel'] = D['raw'].map(lambda s: tuple(json.loads(s)['selections']))
D['race_no'] = D.race_no.astype(int)

R = pd.read_csv('runners.csv', low_memory=False,
                usecols=['date', 'venue', 'race', 'race_id', 'tab_number', 'scratched', 'fixed_win_price',
                         'finish_position', 'wprp_proj'])
R = R[R.date.between(D.date.min(), D.date.max())]
R['scr'] = pd.to_numeric(R.scratched, errors='coerce').fillna(0) > 0
R = R[~R.scr & R.tab_number.notna() & (R.tab_number > 0)]
R['v'] = R.venue.map(norm_venue)
R['tab'] = R.tab_number.astype(int)

dm = {}
for f in glob.glob('data/direct_scores/*.json'):
    for rid, m in json.load(open(f))['races'].items():
        for t, p in m.items():
            dm[(int(rid), int(t))] = p
R['dm'] = [dm.get((int(a), b)) for a, b in zip(R.race_id, R.tab)]

races = []
for (dt, v, rn), g in R.groupby(['date', 'v', 'race']):
    if len(g) < 5 or g.wprp_proj.isna().any():
        continue
    dd = D[(D.date == dt) & (D.v == v) & (D.race_no == int(rn))]
    if dd.empty or not (dd['product'] == 'Win').any():
        continue
    g = g.copy()
    rec = dict(date=dt, key=(dt, v, rn), n=len(g), div={p: dict(zip(x.sel, x.amount)) for p, x in dd.groupby('product')})
    rec['proj'] = list(g.sort_values('wprp_proj', ascending=False).tab)
    rec['mkt'] = list(g.sort_values('fixed_win_price').tab) if g.fixed_win_price.notna().all() else None
    rec['dir'] = list(g.sort_values('dm', ascending=False).tab) if g.dm.notna().all() else None
    races.append(rec)
print('races with dividends and a full Proj:', len(races),
      ' with market ranks:', sum(r['mkt'] is not None for r in races),
      ' with direct scores:', sum(r['dir'] is not None for r in races))

def pay(div, prod, sel):
    return div.get(prod, {}).get(tuple(sel), 0.0)

def place_tabs(div):
    return {s[0]: a for s, a in div.get('Place', {}).items()}

def strat(rank, div):
    """Return {name: (cost, return)} for one race."""
    o = {}
    r = rank
    win = {s[0]: a for s, a in div.get('Win', {}).items()}
    pl = place_tabs(div)
    o['Win #1'] = (1, win.get(r[0], 0))
    o['Place #1'] = (1, pl.get(r[0], 0))
    o['Place #2'] = (1, pl.get(r[1], 0))
    o['Place #3'] = (1, pl.get(r[2], 0))
    o['Place #1+#2'] = (2, pl.get(r[0], 0) + pl.get(r[1], 0))
    q = lambda a, b: div.get('Quinella', {}).get((a, b), 0) + div.get('Quinella', {}).get((b, a), 0)
    o['Quinella 1-2'] = (1, q(r[0], r[1]))
    o['Quinella box 3'] = (3, sum(q(a, b) for a, b in itertools.combinations(r[:3], 2)))
    o['Quinella box 4'] = (6, sum(q(a, b) for a, b in itertools.combinations(r[:4], 2)))
    o['Quinella #1 with 2-4'] = (3, sum(q(r[0], b) for b in r[1:4]))
    o['Exacta 1-2'] = (1, pay(div, 'Exacta', r[:2]))
    o['Exacta #1 over 2-4'] = (3, sum(pay(div, 'Exacta', (r[0], b)) for b in r[1:4]))
    o['Exacta box 3'] = (6, sum(pay(div, 'Exacta', p) for p in itertools.permutations(r[:3], 2)))
    du = lambda a, b: div.get('Duet', {}).get((a, b), 0) + div.get('Duet', {}).get((b, a), 0)
    o['Duet 1-2'] = (1, du(r[0], r[1]))
    o['Duet box 3'] = (3, sum(du(a, b) for a, b in itertools.combinations(r[:3], 2)))
    o['Duet #1 with 2-4'] = (3, sum(du(r[0], b) for b in r[1:4]))
    tri = lambda p: pay(div, 'Trifecta', p)
    o['Trifecta box 3'] = (6, sum(tri(p) for p in itertools.permutations(r[:3], 3)))
    o['Trifecta box 4'] = (24, sum(tri(p) for p in itertools.permutations(r[:4], 3)))
    o['Trifecta #1 / 2-4 / 2-4'] = (6, sum(tri((r[0],) + p) for p in itertools.permutations(r[1:4], 2)))
    o['Trifecta #1 / 2-5 / 2-5'] = (12, sum(tri((r[0],) + p) for p in itertools.permutations(r[1:5], 2)))
    o['Trifecta 1-2 / 1-2 / 3-6'] = (8, sum(tri(p + (c,)) for p in itertools.permutations(r[:2], 2) for c in r[2:6]))
    ff = lambda p: pay(div, 'FirstFour', p)
    o['First four box 4'] = (24, sum(ff(p) for p in itertools.permutations(r[:4], 4)))
    o['First four box 5'] = (120, sum(ff(p) for p in itertools.permutations(r[:5], 4)))
    o['First four #1 / 2-5 x3'] = (24, sum(ff((r[0],) + p) for p in itertools.permutations(r[1:5], 3)))
    o['First four #1 / 2-6 x3'] = (60, sum(ff((r[0],) + p) for p in itertools.permutations(r[1:6], 3)))
    return o

def summarise(rows, label):
    df = pd.DataFrame(rows)
    out = []
    dates = sorted(df.date.unique()); mid = dates[len(dates) // 2]
    for s, g in df.groupby('s', sort=False):
        c, ret = g.cost.sum(), g.ret.sum()
        ex3 = (ret - g.ret.nlargest(3).sum()) / c - 1
        h1 = g[g.date < mid]; h2 = g[g.date >= mid]
        out.append((s, len(g), (g.ret > 0).mean(), c, ret / c - 1, ex3,
                    h1.ret.sum() / h1.cost.sum() - 1, h2.ret.sum() / h2.cost.sum() - 1))
    t = pd.DataFrame(out, columns=['bet', 'races', 'hit', 'cost', 'roi', 'ex3', 'H1', 'H2'])
    print('\n== ranking: %s ==' % label)
    print(t.to_string(index=False, formatters={'hit': '{:.1%}'.format, 'cost': '{:.0f}'.format,
                                               'roi': '{:+.1%}'.format, 'ex3': '{:+.1%}'.format,
                                               'H1': '{:+.1%}'.format, 'H2': '{:+.1%}'.format}))
    return t

res = {}
for rk in ('proj', 'mkt', 'dir'):
    rows = []
    sub = [r for r in races if r[rk] is not None and r['proj'] is not None and r['mkt'] is not None]
    for r in sub:
        for s, (c, ret) in strat(r[rk], r['div']).items():
            rows.append(dict(s=s, date=r['date'], cost=c, ret=ret))
    res[rk] = summarise(rows, rk + ' (%d races, all with Proj and market ranks)' % len(sub))

# same races for Proj vs direct
common = [r for r in races if r['dir'] is not None and r['mkt'] is not None]
for rk in ('proj', 'dir', 'mkt'):
    rows = []
    for r in common:
        for s, (c, ret) in strat(r[rk], r['div']).items():
            rows.append(dict(s=s, date=r['date'], cost=c, ret=ret))
    summarise(rows, rk + ' on the %d races that also have direct scores' % len(common))

