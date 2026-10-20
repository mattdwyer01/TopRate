"""Horsetorque ideas re-run with the Spd rating as the ONLY signal (20 Oct 2026). No WPR, TR, Nett, locked rule or fitted model.

Spd = the shipped rating: EWM (halflife 4 runs, >= 2 runs) of the par v2 speed figures as of before the race, plus the days-since-run and weight-change
terms from speed_models/adjust.json. Population: results-file races 2025-07 to 8 Oct 2026 (where Spd exists for most runners), >= 5 Spd-rated runners,
one winner, clean SP book (1.05 to 2.0). The Horsetorque ideas are used only as filters on Spd picks. Base selection: Spd #1 or #2 with Top >= $3
(this is NOT the locked rule, which needs TR / Mid / Late / Total).
usage: PYTHONPATH=.:research python analysis/horsetorque_edge/spd_only.py
"""
import os, sys, json
import numpy as np, pandas as pd
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..', 'research'))
from common import roi_stats, fmt_table, CACHE, ROOT
import speed_rating_variants as v

PTS = 2.15  # displayed-scale points per length


def build():
    d = v.figures()
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = d.groupby('horse_id', sort=False)
    d['spd'] = g['sp2'].transform(lambda s: s.shift(1).ewm(halflife=4.0, min_periods=2, ignore_na=True).mean())
    f = pd.read_pickle(os.path.join(CACHE, 'features.pkl'))
    keep = ['race_id', 'horse_id', 'price_top', 'priceStarting', 'days_since', 'w_up', 'cp_class_move', 'class_par', 'tof_prev', 'rear_last', 'd_up',
            'settle_m3_pos', 'field_size', 'win']
    d = d.merge(f[keep], on=['race_id', 'horse_id'], how='inner', suffixes=('', '_f'))
    c = json.load(open(os.path.join(ROOT, 'speed_models', 'adjust.json')))
    a = c['adj_lengths']
    adj = a['ldays'] * (np.log1p(d['days_since'].clip(0, 400)) - c['ldays_center'])
    adj = adj.fillna(0.0) + (a['wchg'] * d['w_up'].clip(-c['wchg_clip'], c['wchg_clip'])).fillna(0.0)
    d['spd'] = d['spd'] + adj
    d = d[(d['date'] >= '2025-07-01') & d['spd'].notna()].copy()
    d['impb'] = 1 / d['priceStarting'].where(d['priceStarting'] > 1)
    book = d.groupby('race_id')['impb'].transform('sum')
    cnt = d.groupby('race_id')['spd'].transform('size')
    allp = d.groupby('race_id')['impb'].transform(lambda s: s.notna().all())
    d = d[(cnt >= 5) & (book >= 1.05) & (book <= 2.0) & allp.astype(bool)].copy()
    d['rk'] = d.groupby('race_id')['spd'].rank(ascending=False, method='first')
    top = d.groupby('race_id')['spd'].transform('max')
    d['gap'] = (top - d['spd']) * PTS
    return d


def comp(d, thr, n):
    w = d[d['gap'] <= thr].groupby('race_id').size()
    return w


def main():
    d = build()
    out = [f'# Spd-only Horsetorque tests\n\n{d.race_id.nunique():,} races, {len(d):,} runners, 2025-07 to 8 Oct 2026. Only the Spd rating ranks or selects; every other idea is a filter on Spd picks. '
           'ROI is shown at the Top price and at SP (Top is never below SP, so Top is an upper bound).\n']
    base = d[(d.rk <= 2) & (d.price_top >= 3)]
    out += ['## Base: Spd rank and price floor\n', fmt_table([roi_stats(d[d.rk == 1], 'price_top', 'Spd #1, any price'), roi_stats(d[d.rk == 2], 'price_top', 'Spd #2, any price'),
            roi_stats(d[(d.rk == 1) & (d.price_top >= 3)], 'price_top', 'Spd #1, Top >= $3'), roi_stats(base, 'price_top', 'Spd #1 or #2, Top >= $3 (base for the filters)'),
            roi_stats(d[d.price_top >= 3], 'price_top', 'all runners, Top >= $3 (baseline)')]) + '\n']
    # 1 price bands / floor
    rows = [roi_stats(d[(d.rk <= 2) & (d.price_top >= lo) & (d.price_top < hi)], 'price_top', f'Spd #1-2, Top ${lo}-{hi if hi < 1000 else "+"}') for lo, hi in [(1.5, 2), (2, 3), (3, 5), (5, 7), (7, 1000)]]
    rows += [roi_stats(d[(d.rk <= 2) & (d.price_top >= f)], 'price_top', f'Spd #1-2, floor ${f}') for f in (2, 2.5, 3, 4, 5)]
    out += ['## Test 5a: price bands and the floor, Spd #1-2\n', fmt_table(rows) + '\n']
    # 1 class par
    b = d[(d.rk <= 2) & (d.price_top >= 3) & d.cp_class_move.notna()].copy()
    b['cm'] = pd.cut(b.cp_class_move, [-99, -1.5, 1.5, 99], labels=['class drop (> 1.5 par below recent)', 'same class (+-1.5)', 'class rise (> 1.5 above recent)'])
    rows = [roi_stats(g, 'price_top', str(k)) for k, g in b.groupby('cm', observed=True)]
    b['pb'] = pd.cut(b.class_par, [0, 86.5, 92, 96.5, 120], labels=['Maiden', 'BM/CLS up to 92', 'BM/CLS 92-96.5', 'Open / Black type'])
    rows += [roi_stats(g, 'price_top', f'class_par {k}') for k, g in b.groupby('pb', observed=True)]
    out += ['## Test 1: class par as a filter on Spd #1-2 (Top >= $3)\n', fmt_table(rows) + '\n']
    # 2 TOF avoid flag
    b = d[(d.rk <= 2) & (d.price_top >= 3)].copy()
    ok = b.tof_prev.notna() & b.rear_last.notna() & b.w_up.notna() & b.d_up.notna()
    flag = (b.tof_prev < 0) & (b.rear_last == 1) & ((b.w_up > 0) | (b.d_up > 0))
    rows = [roi_stats(b[ok & flag], 'price_top', 'avoid flag set (TOF<0, rear third, weight or distance up)'), roi_stats(b[ok & ~flag], 'price_top', 'flag not set'),
            roi_stats(b[b.tof_prev < 0], 'price_top', 'last-start TOF < 0 (any settle)'), roi_stats(b[b.tof_prev >= 0], 'price_top', 'last-start TOF >= 0')]
    out += ['## Test 2: TOF avoid flag on Spd #1-2 (Top >= $3)\n', fmt_table(rows) + '\n']
    # 3 compression, gaps in displayed-scale points (2.15 per length)
    rows = [roi_stats(base, 'price_top', 'no gate')]
    for thr in (3, 4, 5, 6):
        w = d[d.gap <= thr].groupby('race_id').size()
        for N in (4, 5, 6):
            keep = base[base.race_id.map(w).fillna(0) < N]
            rows.append(roi_stats(keep, 'price_top', f'skip compressed: >= {N} within {thr} pts (kept {len(keep)/len(base)*100:.0f}%)'))
    out += ['## Test 3: compression gate on Spd #1-2 (points on the displayed Spd scale, 2.15 per length)\n', fmt_table(rows) + '\n']
    g15 = d[d.rk == 5].set_index('race_id')['gap']
    b = base.copy(); b['g15'] = b.race_id.map(g15)
    q = b.g15.quantile([0, .25, .5, .75, 1]).values
    rows = [roi_stats(b[(b.g15 >= lo) & (b.g15 <= hi)], 'price_top', f'gap_1_5 {lo:.1f} to {hi:.1f}') for lo, hi in zip(q[:-1], q[1:])]
    out += ['gap_1_5 quartiles (larger = less compressed):\n', fmt_table(rows) + '\n']
    # 4 golden 8
    b = d[(d.rk <= 2) & (d.price_top >= 3) & d.settle_m3_pos.notna() & (d.field_size >= 9)].copy()
    d9 = d[d.settle_m3_pos.notna()].copy()
    d9['mr'] = d9.groupby('race_id')['settle_m3_pos'].rank(method='first')
    b['mr'] = b.set_index(['race_id', 'horse_id']).index.map(d9.set_index(['race_id', 'horse_id'])['mr'])
    rows = [roi_stats(b[b.mr <= 8], 'price_top', 'projected map position in first 8'), roi_stats(b[b.mr > 8], 'price_top', 'projected map position 9th or worse'),
            roi_stats(b[b.mr <= 4], 'price_top', 'projected in first 4')]
    out += ['## Test 4: projected map position (last-3 average 800m call) on Spd #1-2, fields of 9+\n', fmt_table(rows) + '\n']
    # 5b dutch
    rows = []
    for col, nm in (('price_top', 'Top'), ('priceStarting', 'SP')):
        for th in (0.8, 1.0):
            s = d[(d.rk <= 4)]; s = s[s.groupby('race_id')['race_id'].transform('size') == 4]
            g = s.groupby('race_id'); r = pd.DataFrame({'o': g[col].apply(lambda p: (1 / p).sum()), 'h': g['win'].max()})
            r = r[r.o < th]
            pr = np.where(r.h == 1, 1 - r.o, -r.o)
            rows.append(dict(variant=f'Dutch Spd top 4 at {nm}, outlay < {th}', races=len(r), strike=r.h.mean() * 100 if len(r) else np.nan, roi_on_outlay=pr.sum() / r.o.sum() * 100 if len(r) else np.nan))
    out += ['## Test 5b: Dutch the Spd top 4 to equal return\n', '| variant | races | strike % | ROI on outlay % |\n|---|---|---|---|\n' + '\n'.join(f"| {r['variant']} | {r['races']} | {r['strike']:.1f} | {r['roi_on_outlay']:+.1f} |" for r in rows) + '\n']
    txt = '\n'.join(out)
    open(os.path.join(HERE, '..', 'horsetorque_edge_spd_only.md'), 'w').write(txt)
    print(txt)


if __name__ == '__main__':
    main()
