"""Test 5: sanity checks. (a) locked-rule ROI by price band / where should the $3 floor sit; (b) Dutch the top 4 benchmark."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from model import *
from rules import *

RES = os.path.join(os.path.dirname(__file__), 'results')
BANDS = [(1.5, 2), (2, 3), (3, 5), (5, 7), (7, 1000)]


def band_rows(df, price, tag):
    rows = [roi_stats(df[(df[price] >= lo) & (df[price] < hi)], price, f'{tag} ${lo}-{hi if hi < 1000 else "+"}') for lo, hi in BANDS]
    return rows


def floor_rows(df, price, tag):
    return [roi_stats(df[df[price] >= f], price, f'{tag} floor ${f}') for f in (1.5, 2.0, 2.5, 3.0, 4.0, 5.0)]


def dutch(df, rank_col, k=4, max_ratio=0.8, price='price_top', label=''):
    """Dutch the k best-ranked runners to a 1-unit return each. outlay = sum(1/price). Bet only when outlay < max_ratio.
    Profit = 1 - outlay if the winner is among them else -outlay. ROI is on total outlay."""
    s = df[df[rank_col] <= k]
    g = s.groupby('race_id')
    cnt = g.size(); ok = cnt[cnt == k].index
    s = s[s['race_id'].isin(ok) & s[price].notna() & (s[price] > 1)]
    g = s.groupby('race_id')
    cnt = g.size(); s = s[s['race_id'].isin(cnt[cnt == k].index)]
    g = s.groupby('race_id')
    r = pd.DataFrame({'outlay': g[price].apply(lambda p: (1 / p).sum()), 'hit': g['win'].max(), 'date': g['date'].first()})
    r = r[r['outlay'] < max_ratio]
    n = len(r)
    if n == 0:
        return dict(variant=label, threshold=max_ratio, races_bet=0)
    profit = np.where(r['hit'] == 1, 1 - r['outlay'], -r['outlay'])
    roi = profit.sum() / r['outlay'].sum() * 100
    rng = np.random.default_rng(1)
    bs = [profit[i].sum() / r['outlay'].values[i].sum() * 100 for i in (rng.integers(0, n, n) for _ in range(300))]
    d = r['date'].values; mid = np.sort(d)[n // 2]
    h = lambda m: profit[m].sum() / r['outlay'].values[m].sum() * 100 if m.sum() else np.nan
    return dict(variant=label, threshold=max_ratio, races_bet=n, strike_pct=r['hit'].mean() * 100, avg_outlay=r['outlay'].mean(), roi_on_outlay_pct=roi, roi_se=float(np.std(bs)), half1=h(d < mid), half2=h(d >= mid))


def run():
    D = prep(pd.read_pickle(os.path.join(CACHE, 'features.pkl')))
    a = load_archive()
    out = ['## Test 5: sanity checks\n']
    # ---- 5a: price bands, with the $3 floor removed from the rule
    r_nofloor = locked_rule_real(a, min_top=0)
    out.append('### 5a. Locked rule (real, Apr-Oct 2026) by Top price band, rule applied WITHOUT the $3 floor\n')
    out.append(fmt_table(band_rows(r_nofloor, 'price_top', 'Top')) + '\n')
    out.append('Cumulative floors (a bet is placed at or above the floor):\n')
    out.append(fmt_table(floor_rows(r_nofloor, 'price_top', 'Top')) + '\n')
    rs = r_nofloor.rename(columns={'starting_price_sp': 'sp'})
    out.append('Same rule settled at the starting price instead (Top is never below SP, so it behaves like the best price seen rather than a price you can take at will; SP is the sensitivity):\n')
    out.append(fmt_table(floor_rows(rs[rs['sp'] > 1], 'sp', 'SP')) + '\n')
    E = D[(D['n_prior'] >= 3) & (D.groupby('race_id')['race_id'].transform('size') >= 4)].copy()
    from rules import proxy_ranks, proxy_rule
    E = proxy_ranks(E)
    Pn = proxy_rule(E, min_top=0)
    out.append('Reference rule P without the floor (2019-2026, as-of proxy, NOT the locked rule):\n')
    out.append(fmt_table(band_rows(Pn, 'price_top', 'Top')) + '\n')
    out.append(fmt_table(floor_rows(Pn, 'price_top', 'Top')) + '\n')
    rows = []
    for y, g in Pn.groupby(Pn['dt'].dt.year):
        for lo, hi in ((1.5, 3), (3, 1000)):
            rows.append(roi_stats(g[(g['price_top'] >= lo) & (g['price_top'] < hi)], 'price_top', f'{y} ${lo}-{hi if hi < 1000 else "+"}'))
    out.append('Rule P, below vs above the $3 floor by year:\n')
    out.append(fmt_table(rows) + '\n')
    # ---- 5b: Dutch top 4
    preds = walk_forward(D, BASE + CLASS_PAR, name='m')
    m = D[['run_id', 'race_id', 'date', 'win', 'price_top', 'priceStarting']].merge(preds[['run_id', 'rk_m']], on='run_id')
    m['mkt_rank'] = m.groupby('race_id')['price_top'].rank(method='first')
    rows = []
    for th in (0.8, 0.9, 1.0):
        rows.append(dutch(m, 'rk_m', 4, th, label='model top 4 (base + class_par), 2023-2026'))
    for th in (0.8, 1.0):
        rows.append(dutch(m, 'mkt_rank', 4, th, label='market top 4 (shortest Top prices), 2023-2026'))
    rt = a.copy(); rt['rk'] = rt['tr_rank']
    for th in (0.8, 0.9, 1.0):
        rows.append(dutch(rt, 'tr_rank', 4, th, label='TR rank top 4 (real toprate_rating), Apr-Oct 2026'))
    # locked-rule races: Dutch the top 4 TR in races where the rule has a pick, to compare like with like
    pick_races = set(locked_rule_real(a)['race_id'])
    rows.append(dutch(rt[rt['race_id'].isin(pick_races)], 'tr_rank', 4, 0.8, label='TR top 4 in races with a locked-rule pick, Apr-Oct 2026'))
    rows.append(dutch(rt[rt['race_id'].isin(pick_races)], 'tr_rank', 4, 1.0, label='TR top 4 in races with a locked-rule pick, no outlay cap'))
    rows.append(dutch(m, 'rk_m', 4, 0.8, price='priceStarting', label='model top 4 settled at SP (outlay cap on SP), 2023-2026'))
    rows.append(dutch(m, 'rk_m', 4, 1.0, price='priceStarting', label='model top 4 settled at SP, no cap'))
    rows.append(dutch(rt, 'tr_rank', 4, 0.8, price='starting_price_sp', label='TR top 4 settled at SP, Apr-Oct 2026'))
    rows.append(dutch(rt, 'tr_rank', 4, 1.0, price='starting_price_sp', label='TR top 4 settled at SP, no cap'))
    t = pd.DataFrame(rows)
    out.append('### 5b. Dutch the top 4 to an equal fixed return, bet only when total outlay < threshold x return\n')
    out.append('Stake on each runner = 1 / Top price, so a winner among the four returns 1 unit; outlay = sum of the four implied probabilities. '
               'Threshold 0.8 is the requested rule (edge of at least 20% before any miss). ROI is profit / total outlay; "strike" is the share of bet races where the winner was in the four.\n')
    out.append(md(t, {'threshold': '{:.1f}', 'strike_pct': '{:.1f}', 'avg_outlay': '{:.3f}', 'roi_on_outlay_pct': '{:+.1f}', 'roi_se': '{:.1f}', 'half1': '{:+.1f}', 'half2': '{:+.1f}'}) + '\n')
    open(os.path.join(RES, 't5.md'), 'w').write('\n'.join(out))
    print('\n'.join(out))


if __name__ == '__main__':
    run()
