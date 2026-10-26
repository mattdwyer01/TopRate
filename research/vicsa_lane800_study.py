"""VIC/SA width at 800m from home: measured readings (Racing Victoria PDFs, rc_pdf_gps.py) against the model the trip map used.

The trip map's VIC/SA width model was trained on racing.com's whole-run AVERAGE distance from the rail (one number a runner), while
Queensland has width at 800m. The PDFs carry the rail distance by section, so for runs since 28 Apr 2026 the real 800m value is known.

  PYTHONPATH=. python research/vicsa_lane800_study.py

Compares, on later races not used for fitting (fields of 8+, within-race correlation and error against the measured 800m width):
  A  the old approach: model of whole-run average width, scored against the 800m width
  B  a model trained on the measured 800m width
  C  B plus A's forecast as an input
"""
import glob
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'analysis', 'trip_map'))
import build_trip_map as B  # noqa: E402

ROOT = B.ROOT
SPLIT = pd.Timestamp(os.environ.get('LANE_SPLIT', '2026-09-01'))


def lane800_table():
    fs = sorted(glob.glob(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_rail_*.parquet')))
    d = pd.concat([pd.read_parquet(f) for f in fs], ignore_index=True)
    d['meet_code'] = d.meet_code.astype(str)
    key = ['meet_code', 'race_no', 'tab_no']
    p = d.pivot_table(index=key, columns='from_m', values='rail_m', aggfunc='first')
    direct = p[800] if 800 in p.columns else pd.Series(np.nan, index=p.index)
    near = pd.concat([p[c] for c in (1000, 600) if c in p.columns], axis=1).mean(axis=1, skipna=False)
    out = direct.fillna(near).rename('lane800').reset_index()
    out['lane800_src'] = np.where(direct.reset_index(drop=True).notna(), 'direct', 'interp')
    return out


def wcorr(df, pred, y):
    z = pd.DataFrame({'r': df.race_id.values, 'p': np.asarray(pred), 'y': df[y].values}).dropna()
    for c in 'py':
        z[c] -= z.groupby('r')[c].transform('mean')
    return round(float(np.corrcoef(z.p, z.y)[0, 1]), 3), round(float(np.sqrt(((z.p - z.y) ** 2).mean())), 2), len(z)


def main():
    res = B.load_results()
    a = B.vicsa_runs(res)
    a = a[a.fs >= 5].copy()
    a['trk'] = a.track.astype('category')
    cats = list(a.trk.cat.categories)
    a = B.add_history(a)
    a['trk'] = pd.Categorical(a.track, categories=cats)
    a['meet_code'] = a.meet_code.astype(str)
    a = a.merge(lane800_table(), on=['meet_code', 'race_no', 'tab_no'], how='left')
    S = a[a.lane800.notna()]
    print('VIC/SA runs', len(a), '| with a measured 800m width', len(S), 'in', S.race_id.nunique(), 'races', S.date.min().date(), 'to', S.date.max().date(),
          '| direct', int((S.lane800_src == 'direct').sum()), 'interpolated', int((S.lane800_src == 'interp').sum()))
    print('800m width: mean %.2f sd %.2f | whole-run average width on the same runs: mean %.2f' % (S.lane800.mean(), S.lane800.std(), S.lane.mean()))
    print('within-race corr of measured 800m width with whole-run average width: %s' % (wcorr(S, S.lane, 'lane800'),))
    tr_s, te_s = S[S.date < SPLIT], S[(S.date >= SPLIT) & (S.fs >= 8)]
    print('fit runs', len(tr_s), 'test runs', len(te_s), 'test races', te_s.race_id.nunique())
    # A: whole-run average width model, trained on everything before the first measured run (no overlap with the 800m rows)
    first = S.date.min()
    old = a[(a.date < first) & a.lane.notna()]
    mA = lgb.train(B.PARAMS, lgb.Dataset(old[B.FEATS], old.lane), B.ROUNDS)
    for df in (tr_s, te_s):
        df['predA'] = mA.predict(df[B.FEATS])
    # B: trained on the measured 800m width
    pb = dict(B.PARAMS, min_data_in_leaf=40, num_leaves=15)
    mB = lgb.train(pb, lgb.Dataset(tr_s[B.FEATS], tr_s.lane800), 250)
    mC = lgb.train(pb, lgb.Dataset(tr_s[B.FEATS + ['predA']], tr_s.lane800), 250)
    te = te_s.copy()
    te['predB'] = mB.predict(te[B.FEATS])
    te['predC'] = mC.predict(te[B.FEATS + ['predA']])
    te['barfrac_only'] = te.barfrac
    print('\n=== within-race corr / RMSE / n against measured 800m width (test, fields of 8+) ===')
    for nm, col in (('barrier fraction alone', 'barfrac_only'), ('A  old model (whole-run avg width)', 'predA'), ('B  trained on measured 800m', 'predB'), ('C  B + A as input', 'predC')):
        print(f'{nm:38s}', wcorr(te, te[col], 'lane800'))
    # for the absolute level: RMSE of the race-mean-corrected prediction is not comparable, report calibration of B
    print('\nB: mean predicted %.2f vs measured %.2f; sd within race %.2f vs %.2f' % (
        te.predB.mean(), te.lane800.mean(), (te.predB - te.groupby('race_id').predB.transform('mean')).std(), (te.lane800 - te.groupby('race_id').lane800.transform('mean')).std()))
    imp = pd.Series(mB.feature_importance('gain'), index=B.FEATS).sort_values(ascending=False)
    print('top inputs for B:', (imp / imp.sum()).round(3).head(8).to_dict())
    te[['race_id', 'horse_id', 'track', 'distance', 'barrier', 'fs', 'lane800', 'predA', 'predB', 'predC']].to_pickle(os.environ.get('LANE_OUT', '/tmp/vicsa_lane800_test.pkl'))


if __name__ == '__main__':
    main()
