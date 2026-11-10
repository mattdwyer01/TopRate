import pandas as pd, numpy as np
d = pd.read_pickle('std_runs.pkl'); d = d[d.atw.notna()].sort_values(['horse_id','date'])
d['off'] = d.atw - d.wpr; g = d.groupby('horse_id').wpr
d['l3'] = (g.shift(1) + g.shift(2) + g.shift(3)) / 3 + d.off
d['n'] = d.groupby('race_id').wpr.transform('size')
d = d[d.l3.notna() & (d.date >= '2019-01-01')]
d['e'] = d.atw - d.l3
d['fsb'] = pd.cut(d.n, [0, 7, 10, 13, 16, 19, 30], labels=['<=7','8-10','11-13','14-16','17-19','20+'])
d['top'] = d.l3 >= 95
f = lambda x: pd.Series({'runs': len(x), 'races': x.race_id.nunique(), 'actual-L3 med': x.e.median(), 'actual-L3 mean': x.e.mean()})
pd.set_option('display.width', 200)
print('results files 2019 to Oct 2026, ratings on each race\'s weights'); print(d.groupby('fsb', observed=True).apply(f).round(2).to_string())
print('\nL3 95+ only'); print(d[d.top].groupby('fsb', observed=True).apply(f).round(2).to_string())
big = d[d.n >= 20]
print('\nfields of 20+:'); print(big.groupby(['date','venue','distance']).apply(lambda x: pd.Series({'n': len(x), 'med actual-L3': x.e.median(), 'L3 med': x.l3.median()})).round(1).to_string())
# within field-size, same-class comparison: Group 1 / open 2400+ races, 14-16 vs 20+
o = d[(d.distance >= 2400) & (d.l3 >= 90)]
print('\n2400m+, L3 90+'); print(o.groupby('fsb', observed=True).apply(f).round(2).to_string())
