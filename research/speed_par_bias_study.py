"""Better par times and a track-bias adjustment for the speed figure (19 Oct 2026). Results files 2019+, flat, no trials.
Part 1, race level: how well par + same-day venue variant explain winners' times out of sample (2025-07+), residual sd in lengths:
  par v2 (shipped), par v3 (adds rail position, track x distance, month), variants: shipped, by distance group, other shrink/clip.
Part 2, rating level: figure = lengths faster than par+variant minus beaten margin; rating = EWM halflife 4 of earlier figures (min 2 runs). Scored on 2025-07+ races where
every version has a rating: winner log-lik (best beta), top pick %, top 3 %, paired gain vs the shipped rating, gain when added to L3 (weight fitted on 2025-07..12, scored 2026).
Track bias adjustment: a figure is moved by the shrunk mean demeaned figure of other races on the same track and day for the same draw group (inside / middle / wide third
of the field) and for the same early-position group (front / middle / back third of the field by settled position), other races only, shrink k runners.
usage: PYTHONPATH=. python research/speed_par_bias_study.py"""
import os, sys
import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import speed_figure_study as sf
import speed_figure_study2 as s2
import speed_rating_variants as v

SEC = sf.SEC
sf.USE = list(dict.fromkeys(sf.USE + ['barrier', 'rail_position', 'positionSettled']))


def rail_num(x):
    s = pd.Series(x.astype(str)).str.extract(r'([+-]?\d+\.?\d*)')[0].astype(float)
    return s


def races(d):
    r = s2.races_table(d)
    f = d.drop_duplicates('race_id').set_index('race_id')
    r['rail_s'] = f.rail_position.reindex(r.race_id).astype(str).values
    r['rail'] = rail_num(r.rail_s)
    r['mon'] = r.date.dt.month
    r['td'] = r.track.astype(str) + '|' + r.distance.astype(int).astype(str)
    return r


def fit_par3(r):
    feats = ['distance', 'gnum', 'field_size', 'doy', 'mw', 'rail']
    cats = ['track', 'gname', 'cls', 'grading', 'rail_s', 'td']
    X = r[feats + cats].copy()
    for c in cats:
        X[c] = X[c].astype(str).astype('category')
    tr = (r.date < '2025-01-01') & (r.date >= '2020-01-01')
    P = dict(objective='l2', learning_rate=0.05, num_leaves=63, min_data_in_leaf=20, feature_fraction=0.9, lambda_l2=5, cat_smooth=10, cat_l2=10, verbose=-1, num_threads=4)
    m = lgb.train(P, lgb.Dataset(X[tr], r.perkm[tr]), 700)
    return m.predict(X) * r.distance / 1000


def variant(r, dev, by=('track', 'date'), k=2.0, clip=6.0, minm=2):
    x = dev.clip(-clip, clip)
    key = [r[c] for c in by]
    n = x.groupby(key).transform('count')
    s = x.groupby(key).transform('sum')
    m = n - x.notna().astype(int)
    others = (s - x.fillna(0)) / m.clip(lower=1)
    return np.where(m >= minm, others * (m / (m + k)), 0.0)


def main():
    d = sf.load()
    r = races(d)
    r['dg'] = pd.cut(r.distance, [0, 1300, 1800, 9999], labels=False)
    r['par2'] = s2.fit_par(r)
    r['par3'] = fit_par3(r)
    test = r.date >= '2025-07-01'
    out = {}
    for pn in ('par2', 'par3'):
        dev = r.winners_time - r[pn]
        out[(pn, 'raw, no variant')] = dev
        out[(pn, 'variant shipped')] = dev - variant(r, dev)
        out[(pn, 'variant by distance group')] = dev - variant(r, dev, by=('track', 'date', 'dg'))
        out[(pn, 'variant k=1 clip 4')] = dev - variant(r, dev, k=1.0, clip=4.0)
        out[(pn, 'variant k=4 clip 8')] = dev - variant(r, dev, k=4.0, clip=8.0)
    print('race level: residual sd of winners time in lengths, 2025-07+ (%d races)' % test.sum())
    for k, x in out.items():
        print(f'  {k[0]} {k[1]:28s} sd {(x[test] / SEC).std():6.2f}  mad {((x[test] - x[test].median()).abs().median() / SEC):6.2f}')
    # figures
    devs = {'par2': r.winners_time - r.par2, 'par3': r.winners_time - r.par3}
    for pn in devs:
        r['fast_' + pn] = -(devs[pn] - variant(r, devs[pn])) / SEC
        r['fastd_' + pn] = -(devs[pn] - variant(r, devs[pn], by=('track', 'date', 'dg'))) / SEC
    d = d.merge(r[['race_id', 'fast_par2', 'fast_par3', 'fastd_par2', 'fastd_par3']], on='race_id', how='left')
    d['marg'] = d.marginFinish.clip(lower=0, upper=25)
    for c in ('par2', 'par3'):
        d['sp_' + c] = d['fast_' + c] - d.marg
        d['spd_' + c] = d['fastd_' + c] - d.marg
    d = d.dropna(subset=['sp_par2', 'sp_par3']).copy()
    # track bias groups
    n = d.groupby('race_id').race_id.transform('size')
    d['dfrac'] = d.barrier / d.field_size
    d['dgrp'] = pd.cut(d.dfrac, [-1, 1 / 3, 2 / 3, 9], labels=False)
    d['sfrac'] = d.positionSettled / d.field_size
    d['sgrp'] = pd.cut(d.sfrac, [-1, 1 / 3, 2 / 3, 9], labels=False)
    for base in ('sp_par3',):
        fd = d[base] - d.groupby('race_id')[base].transform('mean')
        d['fd'] = fd.where(n >= 6)
        for g, nm in (('dgrp', 'draw'), ('sgrp', 'pos')):
            for k in (5.0, 15.0):
                ok = d.fd.notna() & d[g].notna()
                tot = d[ok].groupby(['track', 'date', g]).fd.agg(['sum', 'count'])
                own = d[ok].groupby(['race_id', g]).fd.agg(['sum', 'count'])
                key = pd.MultiIndex.from_frame(d[['track', 'date', g]])
                ts = tot.reindex(key).fillna(0).values
                key2 = pd.MultiIndex.from_frame(d[['race_id', g]])
                os_ = own.reindex(key2).fillna(0).values
                ss, nn = ts[:, 0] - os_[:, 0], ts[:, 1] - os_[:, 1]
                b = np.where(d[g].notna(), ss / (nn + k), 0.0)
                d[f'bias_{nm}_{k:g}'] = b
                d[f'sp_par3_{nm}{k:g}'] = d[base] - b
        d['sp_par3_both5'] = d[base] - d['bias_draw_5'] - d['bias_pos_5']
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    gg = d.groupby('horse_id', sort=False)
    cols = {'A shipped (par v2, variant)': 'sp_par2', 'B par v3': 'sp_par3', 'C par v2, variant by distance group': 'spd_par2', 'D par v3, variant by distance group': 'spd_par3',
            'E par v3 + draw bias k5': 'sp_par3_draw5', 'F par v3 + draw bias k15': 'sp_par3_draw15', 'G par v3 + position bias k5': 'sp_par3_pos5',
            'H par v3 + position bias k15': 'sp_par3_pos15', 'I par v3 + draw and position bias k5': 'sp_par3_both5'}
    for nm, c in cols.items():
        d['R ' + nm] = gg[c].transform(lambda s: s.shift(1).ewm(halflife=4.0, min_periods=2).mean())
    d['L3'] = gg['wpr'].transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
    rcols = ['R ' + nm for nm in cols]
    t = d[d.date >= '2025-07-01'].copy()
    t['won'] = (t.positionFinish == 1).astype(int)
    ok = t.groupby('race_id').apply(lambda x: x[rcols + ['L3']].notna().all().all() and len(x) >= 5 and x.won.sum() == 1)
    t = t[t.race_id.isin(ok[ok].index)].sort_values(['race_id', 'horse_id']).reset_index(drop=True)
    starts = np.flatnonzero(np.r_[True, t.race_id.values[1:] != t.race_id.values[:-1]])
    win_idx = np.flatnonzero(t.won.values)
    nr = len(starts)
    print('\nrating level: complete-case races', nr, 'runners', len(t), flush=True)
    betas = [0.01, 0.02, 0.03, 0.05, 0.075, 0.1, 0.15, 0.2, 0.3, 0.5]
    z = lambda c: ((t[c] - t.groupby('race_id')[c].transform('mean')) / t.groupby('race_id')[c].transform('std').replace(0, np.nan)).fillna(0).values
    zl3 = z('L3')
    half_r = t.groupby('race_id').date.first().values < np.datetime64('2026-01-01')
    base_ll = None
    rows = []
    for c in rcols:
        sc = t[c].values.astype(float)
        res = v.ll_by_beta(sc, starts, win_idx, betas)
        bb = max(betas, key=lambda b: res[b].mean())
        ll = res[bb]
        if base_ll is None:
            base_ll = ll
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
        rows.append({'rating': c[2:], 'winner LL': ll.mean(), 'top1 %': 100 * (rk == 1).mean(), 'top3 %': 100 * (rk <= 3).mean(), 'vs A': pv.mean(), 'vs A se': pv.std() / np.sqrt(len(pv)),
                     'w': best_w, 'gain over L3 (2026)': diff.mean(), 'se': diff.std() / np.sqrt(len(diff))})
    pd.set_option('display.width', 250)
    pd.set_option('display.max_colwidth', 48)
    print(pd.DataFrame(rows).set_index('rating').round(4).to_string())


if __name__ == '__main__':
    main()
