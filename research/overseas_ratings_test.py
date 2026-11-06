"""6 Nov 2026 (owner: are overseas ratings proven inaccurate? Defiantly's ratings are all Irish/UK/French). Formula residual (actual page rating minus the live formula figure, outlier trim as live) for runs in Australia,
split by where the horse's recent ratings were earned (region of the last run, share of the last 3 runs overseas), by which Australian start it is, and by rating level. Page store, Jan 2024 on.
Overseas = a run on an un-numbered going word (Good/Soft/Firm/...) at a track that is not an Australian venue; Hong Kong is a separate region (its venues are in runners.csv, state HK).
Run: PYTHONPATH=. python research/overseas_ratings_test.py"""
import gzip, json, glob, re, numpy as np, pandas as pd
co = json.load(open('projection/models_tr/formula.json'))['coef']
def form(l):
    l = np.array(l, float); n = min(len(l), 8); l = l[:n]
    if n >= 2:
        med = np.median(l[:6]); l = np.maximum(l, med - 10)
    c = co[str(n)]; return c[0] + np.dot(c[1:], l)
rn = pd.read_csv('runners.csv', usecols=['venue', 'state'], low_memory=False)
hk_pat = r'sha tin|happy valley'
aus = set(rn[rn.state != 'HK'].venue.str.lower().unique())
for _f in sorted(glob.glob('race_results_20*.csv.gz')) + ['runners_archive.csv.gz']:
    try:
        _x = pd.read_csv(_f, usecols=lambda c: c in ('track', 'venue'), compression='gzip', low_memory=False)
        for _c in _x.columns: aus |= set(_x[_c].dropna().astype(str).str.lower().unique())
    except Exception as e: print('skip', _f, e)
aus = {a for a in aus if not re.search(hk_pat, a)}
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for k, v in json.load(gzip.open(f))['runs'].items():
        if v.get('wpr') is None or v.get('isBarrierTrial') or v.get('isJumpout'): continue
        rows.append((v['horse_id'], v['date'], v['wpr'], str(v.get('track')), str(v.get('going'))))
d = pd.DataFrame(rows, columns=['h', 'date', 'r', 'track', 'going']).drop_duplicates(['h', 'date']).sort_values(['h', 'date'])
t = d.track.str.lower(); g = d.going.str.lower()
word = g.str.match(r'^(firm|fast|good|sand|dead|slow|soft|heavy|yielding)\b') & ~g.str.contains(r'\d')
IRE = r'leopardstown|killarney|cork|curragh|galway|naas|listowel|fairyhouse|punchestown|navan|gowran|dundalk|limerick|tipperary|down royal|ballinrobe|roscommon|bellewstown|tramore|clonmel|wexford|sligo|thurles|kilbeggan|laytown|downpatrick|tralee|ballybrit|the curragh|kenmare|dromore'
FRA = r'deauville|longchamp|chantilly|saint.cloud|maisons|compiegne|lyon|toulouse|marseille|vichy|clairefontaine|cagnes|bordeaux|la teste|craon|nantes|strasbourg|pau|le lion|fontainebleau|angers|cholet|mont.de.marsan|dieppe|auteuil|enghien|reims'
d['region'] = 'aus'
d.loc[t.str.contains(hk_pat), 'region'] = 'hk'
d.loc[word & ~t.isin(aus) & ~t.str.contains(hk_pat), 'region'] = 'other_os'
d.loc[(d.region == 'other_os') & t.str.contains(IRE), 'region'] = 'ireland'
d.loc[(d.region == 'other_os') & t.str.contains(FRA), 'region'] = 'france'
# remaining un-numbered going at a non-Australian track is treated as UK/Europe/other
d.loc[d.region == 'other_os', 'region'] = 'uk_other'
print(d.region.value_counts().to_string())
print('top uk_other tracks:', d[d.region == 'uk_other'].track.value_counts().head(12).to_dict())
out = []
for h, g_ in d.groupby('h'):
    r = g_.r.values; rg = g_.region.values; dt = g_.date.values
    for i in range(1, len(r)):
        if dt[i] < '2024-01-01' or rg[i] != 'aus': continue
        l = r[max(0, i - 8):i][::-1]; reg = rg[max(0, i - 8):i][::-1]
        ausn = 0
        while ausn < i and rg[i - 1 - ausn] == 'aus': ausn += 1   # earlier Australian starts in a row just before this run
        out.append((r[i], form(l), reg[0], np.mean(reg[:3] != 'aus'), l[:3].mean(), len(l), ausn, 'aus' if (reg == 'aus').all() else 'mixed'))
o = pd.DataFrame(out, columns=['act', 'f', 'last_reg', 'os_share3', 'm3', 'n', 'aus_streak', 'hist'])
o['res'] = o.act - o.f
def s(name, m):
    a = o[m]
    if len(a) < 20: print(f'{name:58s} n={len(a):6d}  (too few)'); return
    print(f'{name:58s} n={len(a):6d} mean {a.res.mean():+5.2f} (se {a.res.std()/np.sqrt(len(a)):.2f}) median {a.res.median():+5.2f} RMSE {np.sqrt((a.res**2).mean()):5.2f} | within 6: {100*(a.res.abs()<=6).mean():4.1f}%')
print('\n-- by where the last run was (this run in Australia) --')
s('last run in Australia', o.last_reg == 'aus')
for rg in ('ireland', 'france', 'uk_other', 'hk'): s(f'last run in {rg}', o.last_reg == rg)
print('\n-- first, second, third Australian start after overseas form (last run overseas, then streak) --')
mix = (o['hist'] == 'mixed')
s('first Aus start (last run overseas)', o.last_reg != 'aus')
s('second Aus start (last run Aus, run before overseas)', mix & (o.aus_streak == 1))
s('third Aus start', mix & (o.aus_streak == 2))
s('4th-8th Aus start', mix & o.aus_streak.between(3, 7))
print('\n-- first Australian start by rating level (last-3 average) --')
for lo, hi in ((0, 80), (80, 90), (90, 95), (95, 100), (100, 130)):
    for rg in ('ireland', 'france', 'uk_other', 'hk'):
        pass
    m = (o.last_reg != 'aus') & o.m3.between(lo, hi, inclusive='left')
    s(f'  first Aus start, last-3 avg {lo}-{hi}', m)
    s(f'  Australian-form horses, last-3 avg {lo}-{hi}', (o['hist'] == 'aus') & (o.n >= 3) & o.m3.between(lo, hi, inclusive='left'))
print('\n-- first Aus start, last-3 avg 95+, by region of the last run --')
for rg in ('ireland', 'france', 'uk_other', 'hk'): s(f'  {rg}', (o.last_reg == rg) & (o.m3 >= 95))
print('\n-- how many of the last 3 runs overseas (any region), 3+ earlier runs --')
for sh in (0, 1/3, 2/3, 1): s(f'  share overseas {sh:.2f}', (np.isclose(o.os_share3, sh)) & (o.n >= 3))
