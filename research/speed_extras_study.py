"""Remaining speed rating ideas (19 Oct 2026). Shipped rating = EWM halflife 4 of par v2 figures (lengths vs par, min 2 runs), as of before the race.
Part A (position bias, redone): same-day early-position bias from position600m (front / middle / back third of the field), other races only, plus the draw bias, versus shipped.
  Scored on 2025-07+ complete-case races: winner log-lik, top pick, gain over L3 (weight fitted 2025-07..12, scored 2026).
Part B (what the rating misses): target = the run's own wpr minus the race mean (the rating the horse earns), runners in races of 5+. OLS fitted before 2025, scored on 2025-07+:
  base = L3 + rating; then adds (i) last figure minus the rating before it ('jump', improver flag), (ii) distance change, (iii) days since last run, (iv) weight change,
  (v) all together. Reports test RMSE gain and, by subgroup (runs so far, age, first-up after 90+ days), the correlation of the target with the rating at three memories and
  the partial gain of adding the rating to L3.
usage: PYTHONPATH=. python research/speed_extras_study.py"""
import os, sys
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_figure_study as sf
import speed_figure_study2 as s2
import speed_rating_variants as v

SEC = sf.SEC
sf.USE = list(dict.fromkeys(sf.USE + ['barrier', 'position600m', 'horse_age']))


def variant(r, dev, k=2.0, clip=6.0):
    x = dev.clip(-clip, clip)
    key = [r.track, r.date]
    n = x.groupby(key).transform('count')
    s = x.groupby(key).transform('sum')
    m = n - x.notna().astype(int)
    return np.where(m >= 2, (s - x.fillna(0)) / m.clip(lower=1) * (m / (m + k)), 0.0)


def bias(d, base, g, k):
    n = d.groupby('race_id').race_id.transform('size')
    fd = (d[base] - d.groupby('race_id')[base].transform('mean')).where(n >= 6)
    ok = fd.notna() & d[g].notna()
    tmp = d[['track', 'date', 'race_id', g]].copy()
    tmp['fd'] = fd
    tot = tmp[ok].groupby(['track', 'date', g]).fd.agg(['sum', 'count'])
    own = tmp[ok].groupby(['race_id', g]).fd.agg(['sum', 'count'])
    ts = tot.reindex(pd.MultiIndex.from_frame(d[['track', 'date', g]])).fillna(0).values
    os_ = own.reindex(pd.MultiIndex.from_frame(d[['race_id', g]])).fillna(0).values
    return np.where(d[g].notna(), (ts[:, 0] - os_[:, 0]) / (ts[:, 1] - os_[:, 1] + k), 0.0)


def evaluate(t, rcols, label_first):
    t = t.sort_values(['race_id', 'horse_id']).reset_index(drop=True)
    starts = np.flatnonzero(np.r_[True, t.race_id.values[1:] != t.race_id.values[:-1]])
    win_idx = np.flatnonzero(t.won.values)
    betas = [0.01, 0.02, 0.03, 0.05, 0.075, 0.1, 0.15, 0.2, 0.3, 0.5]
    z = lambda c: ((t[c] - t.groupby('race_id')[c].transform('mean')) / t.groupby('race_id')[c].transform('std').replace(0, np.nan)).fillna(0).values
    zl3 = z('L3')
    half_r = t.groupby('race_id').date.first().values < np.datetime64('2026-01-01')
    base_ll, rows = None, []
    for c in rcols:
        res = v.ll_by_beta(t[c].values.astype(float), starts, win_idx, betas)
        bb = max(betas, key=lambda b: res[b].mean())
        ll = res[bb]
        base_ll = ll if base_ll is None else base_ll
        rk = t.groupby('race_id')[c].rank(ascending=False, method='first').values[win_idx]
        zc = z(c)
        best_w, best_v = 0.0, -9
        for w in (0.0, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0):
            r2 = v.ll_by_beta(zl3 + w * zc, starts, win_idx, [0.5, 1.0, 1.5])
            val = max(r2[k][half_r].mean() for k in r2)
            if val > best_v:
                best_v, best_w = val, w
        r3 = v.ll_by_beta(zl3 + best_w * zc, starts, win_idx, [0.5, 1.0, 1.5])
        r0 = v.ll_by_beta(zl3, starts, win_idx, [0.5, 1.0, 1.5])
        kb = max(r3, key=lambda k: r3[k][half_r].mean())
        diff = (r3[kb] - r0[kb])[~half_r]
        pv = ll - base_ll
        rows.append({'rating': c[2:], 'winner LL': ll.mean(), 'top1 %': 100 * (rk == 1).mean(), 'vs shipped': pv.mean(), 'vs se': pv.std() / np.sqrt(len(pv)),
                     'gain over L3': diff.mean(), 'se': diff.std() / np.sqrt(len(diff))})
    print(pd.DataFrame(rows).set_index('rating').round(4).to_string())


def ols(X, y):
    X1 = np.column_stack([np.ones(len(X)), X])
    b, *_ = np.linalg.lstsq(X1, y, rcond=None)
    return b


def pred(b, X):
    return np.column_stack([np.ones(len(X)), X]) @ b


def main():
    d = sf.load()
    r = s2.races_table(d)
    r['par'] = s2.fit_par(r)
    dev = r.winners_time - r.par
    r['fast'] = -(dev - variant(r, dev)) / SEC
    d = d.merge(r[['race_id', 'fast']], on='race_id', how='left')
    d['sp'] = d.fast - d.marginFinish.clip(lower=0, upper=25)
    d = d.dropna(subset=['sp']).copy()
    d['dgrp'] = pd.cut(d.barrier / d.field_size, [-1, 1 / 3, 2 / 3, 9], labels=False)
    d['sgrp'] = pd.cut(d.position600m / d.field_size, [-1, 1 / 3, 2 / 3, 9], labels=False)
    print('position600m present', round(d.position600m.notna().mean(), 3), flush=True)
    for nm, g in (('draw', 'dgrp'), ('pos', 'sgrp')):
        for k in (5.0, 15.0):
            d[f'sp_{nm}{k:g}'] = d.sp - bias(d, 'sp', g, k)
    d['sp_both5'] = d.sp - bias(d, 'sp', 'dgrp', 5.0) - bias(d, 'sp', 'sgrp', 5.0)
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    gg = d.groupby('horse_id', sort=False)
    cols = {'A shipped': 'sp', 'B draw bias k5': 'sp_draw5', 'C draw bias k15': 'sp_draw15', 'D position bias k5': 'sp_pos5', 'E position bias k15': 'sp_pos15', 'F draw+position k5': 'sp_both5'}
    for nm, c in cols.items():
        d['R ' + nm] = gg[c].transform(lambda s: s.shift(1).ewm(halflife=4.0, min_periods=2).mean())
    d['L3'] = gg['wpr'].transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    rcols = ['R ' + nm for nm in cols]
    t = d[d.date >= '2025-07-01'].copy()
    t['won'] = (t.positionFinish == 1).astype(int)
    ok = t.groupby('race_id').apply(lambda x: x[rcols + ['L3']].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
    t = t[t.race_id.isin(ok[ok].index)]
    print('\nPART A: position and draw bias, complete-case races', t.race_id.nunique(), flush=True)
    evaluate(t, rcols, 'R A shipped')

    # ---- Part B
    d['R4'] = d['R A shipped']
    for h in (2.0, 8.0):
        d[f'R{h:g}'] = gg['sp'].transform(lambda s, h=h: s.shift(1).ewm(halflife=h, min_periods=2).mean())
    d['jump'] = gg['sp'].shift(1) - gg['R4'].shift(1)
    d['dchg'] = d.distance - gg['distance'].shift(1)
    d['days'] = (d.date - gg['date'].shift(1)).dt.days
    d['ldays'] = np.log1p(d.days.clip(upper=400))
    d['wchg'] = d.weightCarried - gg['weightCarried'].shift(1)
    d['nprior'] = gg['sp'].transform(lambda s: s.shift(1).expanding().count())
    d['age'] = d.horse_age
    d['T'] = d.wpr - d.groupby('race_id').wpr.transform('mean')
    n = d.groupby('race_id').race_id.transform('size')
    use = d[(n >= 5) & d['T'].notna() & d.R4.notna() & d.L3.notna() & d.jump.notna() & d.dchg.notna() & d.days.notna() & d.wchg.notna()].copy()
    for c in ['R4', 'R2', 'R8', 'L3', 'jump', 'dchg', 'ldays', 'wchg']:
        use[c + '_d'] = use[c] - use.groupby('race_id')[c].transform('mean')
    use = use.dropna(subset=['R2_d', 'R8_d'])
    tr, te = use[use.date < '2025-01-01'], use[use.date >= '2025-07-01']
    print(f'\nPART B: runners train {len(tr)} test {len(te)}')
    sets = {'L3 + rating': ['L3_d', 'R4_d'], '+ jump (last figure minus prior rating)': ['L3_d', 'R4_d', 'jump_d'], '+ distance change': ['L3_d', 'R4_d', 'dchg_d'],
            '+ days since run': ['L3_d', 'R4_d', 'ldays_d'], '+ weight change': ['L3_d', 'R4_d', 'wchg_d'], '+ all': ['L3_d', 'R4_d', 'jump_d', 'dchg_d', 'ldays_d', 'wchg_d']}
    base = None
    for nm, f in sets.items():
        b = ols(tr[f].values, tr['T'].values)
        e = te['T'].values - pred(b, te[f].values)
        rm = np.sqrt((e ** 2).mean())
        base = rm if base is None else base
        print(f'  {nm:42s} RMSE {rm:.4f}  vs L3+rating {rm - base:+.4f}  coefs {np.round(b[1:], 3)}')
    only = ols(tr[['L3_d']].values, tr['T'].values)
    print(f'  L3 only RMSE {np.sqrt(((te["T"].values - pred(only, te[["L3_d"]].values)) ** 2).mean()):.4f}')
    print('\nby subgroup: corr of target with rating at halflife 2 / 4 / 8 and L3; gain in RMSE from adding rating to L3 (OLS by subgroup fitted on train rows of the same subgroup)')
    groups = {'runs so far 2-3': lambda x: x.nprior.between(2, 3), 'runs 4-7': lambda x: x.nprior.between(4, 7), 'runs 8+': lambda x: x.nprior >= 8,
              'age 2-3': lambda x: x.age <= 3, 'age 4-5': lambda x: x.age.between(4, 5), 'age 6+': lambda x: x.age >= 6,
              'first-up (90+ days)': lambda x: x.days >= 90, 'back in under 90 days': lambda x: x.days < 90}
    for nm, fn in groups.items():
        a, bte = tr[fn(tr)], te[fn(te)]
        if len(a) < 2000 or len(bte) < 2000:
            continue
        cs = [bte['T'].corr(bte[c]) for c in ('R2_d', 'R4_d', 'R8_d', 'L3_d')]
        b0 = ols(a[['L3_d']].values, a['T'].values)
        b1 = ols(a[['L3_d', 'R4_d']].values, a['T'].values)
        e0 = bte['T'].values - pred(b0, bte[['L3_d']].values)
        e1 = bte['T'].values - pred(b1, bte[['L3_d', 'R4_d']].values)
        gain = np.sqrt((e0 ** 2).mean()) - np.sqrt((e1 ** 2).mean())
        print(f'  {nm:24s} n={len(bte):6d} corr hl2 {cs[0]:.3f} hl4 {cs[1]:.3f} hl8 {cs[2]:.3f} L3 {cs[3]:.3f}   RMSE gain from adding rating {gain:+.4f}  (coef on rating {b1[2]:.3f})')


if __name__ == '__main__':
    main()
