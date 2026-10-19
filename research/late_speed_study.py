"""Late speed as a pre-race ranking, analysis only (19 Oct 2026). Follows research/speed_rating_variants.py (same par v2 figures, same complete-case test).

Per-run late measures (from earlier runs only, EWM halflife 4 runs, at least 2 runs, as the Spd rating):
  close  = closing gain on the winner over the last 600m, lengths: (margin600m - winner's margin600m) - max(marginFinish, 0). Relative to the winner, so it says how a
           horse finished against the field, not how fast the race was.
  late   = race speed level + closing gain, i.e. the run's overall speed figure re-weighted to the finish: fast_par2 + close (lengths vs par).
  abs600 = absolute last-600m figure where the winner's last-600m time is known (time_last600m, a minority of runs): par600 + variant + close.
  spd    = the shipped Spd rating (EWM of the overall figure) for comparison.
Scores on results-file races 2025-07+ (to 8 Oct 2026) where every runner has every signal: winner log-lik alone (best softmax beta), top pick win %, top 3, rank
correlation with Spd and L3, the paired gain when added to L3 + Spd (weight fitted on 2025-07..12, scored on 2026), the same split by distance, and the top pick's
win rate and flat ROI at the starting price against the market-implied rate.
usage: python research/late_speed_study.py
"""
import os
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_rating_variants as v  # noqa: E402
import speed_figure_study2 as s2  # noqa: E402

SEC = v.SEC


def build():
    d = v.figures()
    r = s2.races_table(d)
    tr = r[(r.date < '2025-01-01') & r.t600.notna()]
    par6 = pd.Series(np.nan, index=r.index)
    for k in (['track', 'distance', 'gname'], ['track', 'distance'], ['distance']):
        g = tr.groupby(k).t600.agg(['median', 'size']).reset_index()
        g = g[g['size'] >= 8].rename(columns={'median': '_p'})
        par6 = par6.fillna(pd.Series(r[k].merge(g[k + ['_p']], on=k, how='left')['_p'].values, index=r.index))
    dev6 = r.t600 - par6
    r['fast600'] = -(dev6 - pd.Series(s2.variant(r, dev6, 'c'), index=r.index)) / SEC
    d = d.merge(r[['race_id', 'fast600']], on='race_id', how='left')
    w6 = d[d.positionFinish == 1].groupby('race_id').margin600m.first().rename('w6')
    d = d.merge(w6, on='race_id', how='left')
    d['marg'] = d.marginFinish.clip(lower=0, upper=25)
    d['close'] = (d.margin600m - d.w6).clip(-25, 25) - d.marg
    d.loc[d.w6.isna() | d.margin600m.isna(), 'close'] = np.nan
    d['late'] = d.fast_par2 + d.close
    d['abs600'] = d.fast600 + d.close
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = d.groupby('horse_id', sort=False)
    for src, out in (('sp2', 'spd'), ('close', 'close_r'), ('late', 'late_r'), ('abs600', 'abs600_r')):
        d[out] = g[src].transform(lambda s: s.shift(1).ewm(halflife=4.0, min_periods=2, ignore_na=True).mean())
    d['l3'] = g['wpr'].transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    return d


def main():
    d = build()
    t = d[(d.date >= '2025-07-01')].copy()
    t['won'] = (t.positionFinish == 1).astype(int)
    print('coverage of runs 2025-07+: ' + ', '.join(f'{c} {t[c].notna().mean():.0%}' for c in ('spd', 'close_r', 'late_r', 'abs600_r', 'l3')))
    sig = ['spd', 'close_r', 'late_r', 'l3']

    def races(cols):
        ok = t.groupby('race_id').apply(lambda x: x[cols].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
        x = t[t.race_id.isin(ok[ok].index)].sort_values(['race_id', 'horse_id']).reset_index(drop=True)
        st = np.flatnonzero(np.r_[True, x.race_id.values[1:] != x.race_id.values[:-1]])
        return x, st, np.flatnonzero(x.won.values)

    def z(x, c):
        g = x.groupby('race_id')[c]
        return ((x[c] - g.transform('mean')) / g.transform('std').replace(0, np.nan)).fillna(0).values

    betas = [0.01, 0.02, 0.03, 0.05, 0.075, 0.1, 0.15, 0.2, 0.3, 0.5]

    def table(cols, label):
        x, st, wi = races(cols)
        half_r = x.groupby('race_id').date.first().values < np.datetime64('2026-01-01')
        print(f'\n== {label}: {len(st)} races, {len(x)} runners')
        rows = []
        zl3, zsp = z(x, 'l3'), z(x, 'spd')
        base = zl3 + zsp
        for c in cols:
            sc = x[c].values.astype(float)
            res = v.ll_by_beta(sc, st, wi, betas)
            bb = max(betas, key=lambda b: res[b].mean())
            rk = x.groupby('race_id')[c].rank(ascending=False, method='first').values
            wr = rk[wi]
            top = x[rk == 1]
            p = top.priceStarting
            roi = (top.won * p).sum() / p.notna().sum() - 1 if p.notna().any() else np.nan
            zc = z(x, c)
            bw, bv = 0.0, -9
            for w in (0.0, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0):
                r2 = v.ll_by_beta(base + w * zc, st, wi, [0.5, 1.0, 1.5])
                val = max(r2[k][half_r].mean() for k in r2)
                if val > bv:
                    bv, bw = val, w
            r3 = v.ll_by_beta(base + bw * zc, st, wi, [0.5, 1.0, 1.5])
            r0 = v.ll_by_beta(base, st, wi, [0.5, 1.0, 1.5])
            kb = max(r3, key=lambda k: r3[k][half_r].mean())
            diff = (r3[kb] - r0[kb])[~half_r]
            cor = x.assign(a=zc, b=zsp).groupby('race_id').apply(lambda g: g.a.corr(g.b)).mean()
            rows.append({'signal': c, 'LL alone': res[bb].mean(), 'top1 win%': 100 * (wr == 1).mean(), 'top3%': 100 * (wr <= 3).mean(),
                         'top1 ROI@SP': 100 * roi, 'corr w Spd': cor, 'w on L3+Spd': bw, 'gain over L3+Spd (2026)': diff.mean(), 'se': diff.std() / np.sqrt(len(diff))})
        print(pd.DataFrame(rows).set_index('signal').round(4).to_string())
        return x, st, wi, half_r

    x, st, wi, half_r = table(sig, 'core signals')
    table(['spd', 'abs600_r', 'l3'], 'absolute last-600m (needs the winner last-600m time on an earlier run)')
    # by distance: each signal's own top pick, and late_r added to L3 + Spd at weight 0.15 (best of three softmax scales, same scale for both arms)
    x['dist'] = pd.cut(x.distance, [0, 1300, 1700, 5000], labels=['sprint <1300', 'middle 1300-1700', 'staying 1700+']).astype(str)
    zl3, zsp, zlt = z(x, 'l3'), z(x, 'spd'), z(x, 'late_r')
    dist_r = x.groupby('race_id').dist.first().values
    print('\nby distance (2025-07+ complete races)')
    for k in ('sprint <1300', 'middle 1300-1700', 'staying 1700+'):
        m = dist_r == k
        out = [f'{k}: races {m.sum()}']
        for c in ('spd', 'close_r', 'late_r', 'l3'):
            rk = x.groupby('race_id')[c].rank(ascending=False, method='first').values[wi]
            out.append(f'{c} top1 {100 * (rk[m] == 1).mean():.1f}%')
        r0 = v.ll_by_beta(zl3 + zsp, st, wi, [0.5, 1.0, 1.5])
        r1 = v.ll_by_beta(zl3 + zsp + 0.15 * zlt, st, wi, [0.5, 1.0, 1.5])
        kb = max(r0, key=lambda b: r0[b][m].mean())
        df = (r1[kb] - r0[kb])[m]
        out.append(f'gain adding late_r {df.mean():+.4f} (se {df.std() / np.sqrt(m.sum()):.4f})')
        print('  ' + ' | '.join(out))


if __name__ == '__main__':
    main()
