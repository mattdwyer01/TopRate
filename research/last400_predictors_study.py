"""What known-before-the-race data predicts how a horse runs the last 400m (and the whole race)? (26 Oct 2026)

Targets are the racing.com GPS phase deficits from closing_stage_study.load() (seconds vs the race mean, VIC and SA 2021 on): L = last 400m,
T = total. Base model = distance, barrier, field size, venue plus the horse's own earlier GPS E/M/L/T deficits. Each family of extra inputs is
then added alone (R2 gain on 2025 on, LightGBM fit before 2025), and all together. Families:
  F1 fitness (days since run, spell, run number in prep, letup)   F2 weight (carried, change, vs field) and jockey as-of effect on L
  F3 trainer as-of effect on L                                      F4 pedigree (sire as-of L by distance band, age, sex)
  F5 TopRate sectional history (last 4 sect_i_l400/l200/early)      F6 race shape history (raceShapeLate/Early/Mid)
  F7 comment flags of the last run                                  F8 closing gain history from positions/margins at 400m
  F9 rating, class and trend                                        F10 market (log opening/mid price)
  F11 going/track history (own L on this going group, this venue)   F12 field closing profile (mean history of the field's L)
  PYTHONPATH=. python research/last400_predictors_study.py
"""
import glob
import os
import re
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'research'))
import closing_stage_study as CS  # noqa: E402
from bad_run_risk import asof_rate  # noqa: E402

ROOT = CS.ROOT
COLS = ['race_id', 'horse', 'date', 'distance', 'going', 'wpr', 'weightCarried', 'barrier', 'priceStarting', 'position400m', 'margin400m', 'marginFinish',
        'raceShapeEarly', 'raceShapeMid', 'raceShapeLate', 'sect_i_early', 'sect_i_l200', 'sect_i_l400', 'sect_i_to800', 'race_class', 'is_letup', 'is_spell',
        'blinkers_on', 'gear_changes', 'comments_steward', 'comments_video', 'jockey', 'trainer', 'horse_age', 'horse_sex', 'sire', 'sire_of_dam',
        'price_opening', 'price_mid', 'field_size', 'isBarrierTrial', 'is_jumpout', 'trackGrading', 'weight_allowance', 'track']
P = dict(learning_rate=0.05, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_estimators=350)
FLAGS = {'weak': r'weaken|tired|faded|dropped out', 'ranon': r'ran on|finished (strongly|well)|stayed on', 'trouble': r'checked|blocked|held up|crowded|interfer',
         'wide': r'wide|three wide|3 wide|outside', 'slowaway': r'slow(ly)? (away|to begin)|missed the start|lost ground at the start', 'pulled': r'pulled|over-raced|raced keenly|resented'}


def results(names):
    fs = sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz')))
    r = pd.concat([pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False) for f in fs], ignore_index=True)
    r['hk'] = CS.clean(r.horse)
    r = r[r.hk.isin(names)]
    r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
    r['date'] = pd.to_datetime(r.date)
    return r.drop_duplicates(['hk', 'date', 'race_id']).sort_values(['hk', 'date', 'race_id']).reset_index(drop=True)


def main():
    d = CS.load()
    print(f'GPS runs {len(d):,} in {d.key.nunique():,} races')
    r = results(set(d.hk))
    g = r.groupby('hk')
    # ---- history on the full timeline, then merged on (hk, date, distance)
    r['gs'] = pd.to_numeric(r.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    r['days'] = g.date.diff().dt.days
    r['prep_n'] = (r.days.fillna(999) > 60).groupby(r.hk).cumsum()
    r['run_in_prep'] = r.groupby(['hk', 'prep_n']).cumcount()
    r['closegain'] = (r.position400m - r.positionFinish) if 'positionFinish' in r else np.nan
    r['cg'] = r.margin400m.clip(0, 30) - r.marginFinish.clip(0, 30)
    com = (r.comments_steward.fillna('') + ' ' + r.comments_video.fillna('')).str.lower()
    for k, rx in FLAGS.items():
        r['fl_' + k] = com.str.contains(rx, regex=True).astype(float)
    r['lpo'] = np.log(r.price_opening.where(r.price_opening > 1))
    r['lpm'] = np.log(r.price_mid.where(r.price_mid > 1))
    g = r.groupby('hk')
    H = {}
    for c in ('sect_i_l400', 'sect_i_l200', 'sect_i_early', 'raceShapeLate', 'raceShapeEarly', 'raceShapeMid', 'cg', 'wpr', 'weightCarried'):
        lg = pd.concat([g[c].shift(k) for k in range(1, 5)], axis=1)
        H['p1_' + c] = lg.iloc[:, 0]
        H['m4_' + c] = lg.mean(axis=1)
        H['s4_' + c] = lg.std(axis=1)
    for k in FLAGS:
        H['pf_' + k] = g['fl_' + k].shift(1)
        H['rf_' + k] = pd.concat([g['fl_' + k].shift(j) for j in range(1, 5)], axis=1).mean(axis=1)
    H['wchg'] = r.weightCarried - g.weightCarried.shift(1)
    H['wpr_trend'] = g.wpr.shift(1) - g.wpr.shift(4)
    H['lastdist'] = g.distance.shift(1)
    H['dchg'] = r.distance - H['lastdist']
    H['gs_chg'] = r.gs - g.gs.shift(1)
    H['n_runs'] = g.cumcount().astype(float)
    Hd = pd.DataFrame(H)
    cur = r[['hk', 'date', 'distance', 'days', 'run_in_prep', 'is_letup', 'is_spell', 'weightCarried', 'blinkers_on', 'gear_changes', 'jockey', 'trainer', 'horse_age',
             'horse_sex', 'sire', 'sire_of_dam', 'lpo', 'lpm', 'race_class', 'gs', 'trackGrading', 'weight_allowance', 'priceStarting']].join(Hd)
    cur['gear_changes'] = cur.gear_changes.notna().astype(float)
    cur['blinkers_on'] = pd.to_numeric(cur.blinkers_on, errors='coerce')
    cur['sex'] = cur.horse_sex.astype('category').cat.codes.astype(float)
    cur['cls'] = cur.race_class.astype('category').cat.codes.astype(float)
    cur['grd'] = cur.trackGrading.astype('category').cat.codes.astype(float)
    cur = cur.drop_duplicates(['hk', 'date'])
    d = d.merge(cur, left_on=['hk', 'date'], right_on=['hk', 'date'], how='left')
    d = d.sort_values(['hk', 'date', 'key']).reset_index(drop=True)
    print(f'matched to the results timeline: {d.jockey.notna().mean():.0%}')

    # ---- GPS own history
    g2 = d.groupby('hk')
    for c in ('E', 'M', 'L', 'T'):
        lags = pd.concat([g2[f'd_{c}'].shift(k) for k in range(1, 5)], axis=1)
        d[f'h_{c}'] = lags.mean(axis=1)
        d[f'hs_{c}'] = lags.std(axis=1)
    d['h_n'] = g2.cumcount().astype(float)
    d['barfrac'] = (d.barrier - 1) / (d.nr - 1)
    d['trk'] = d.venue.astype('category')
    d['wt_vs_field'] = d.weightCarried - d.groupby('key').weightCarried.transform('mean')
    d['band'] = pd.cut(d.dist, [0, 1150, 1450, 1850, 2300, 9999], labels=False).astype(float)
    d['wet'] = (d.gs >= 5).astype(float)
    # as-of effects on L (shrunk, strictly before the day, over GPS rows)
    for nm, key in (('jock', 'jockey'), ('trn', 'trainer'), ('sire', 'sire'), ('sdam', 'sire_of_dam')):
        d[f'k_{nm}'] = d[key].astype(str).where(d[key].notna())
    d['k_sireband'] = d.k_sire + '|' + d.band.astype(str)
    d['k_sirewet'] = d.k_sire + '|' + d.wet.astype(str)
    d['k_hvenue'] = d.hk + '|' + d.venue.astype(str)
    d['k_hgoing'] = d.hk + '|' + d.wet.astype(str)
    d['k_hband'] = d.hk + '|' + d.band.astype(str)
    for nm in ('jock', 'trn', 'sire', 'sdam', 'sireband', 'sirewet', 'hvenue', 'hgoing', 'hband'):
        v, n = asof_rate(d, f'k_{nm}', None, prior=0.0, k=30, value='d_L')
        d[f'x_{nm}'] = v
        d[f'xn_{nm}'] = n
    # field closing profile
    d['f_L_hist'] = d.groupby('key').h_L.transform('mean')
    d['f_L_rel'] = d.h_L - d.f_L_hist
    d['f_sect_rel'] = d.m4_sect_i_l400 - d.groupby('key').m4_sect_i_l400.transform('mean')

    base = ['h_E', 'h_M', 'h_L', 'h_T', 'hs_E', 'hs_M', 'hs_L', 'h_n', 'dist', 'barfrac', 'nr', 'trk']
    fam = {
        'F1 fitness': ['days', 'run_in_prep', 'is_letup', 'is_spell', 'n_runs'],
        'F2 weight and jockey': ['weightCarried', 'wchg', 'wt_vs_field', 'weight_allowance', 'x_jock', 'xn_jock', 'blinkers_on', 'gear_changes'],
        'F3 trainer': ['x_trn', 'xn_trn'],
        'F4 pedigree': ['x_sire', 'xn_sire', 'x_sireband', 'x_sirewet', 'x_sdam', 'horse_age', 'sex'],
        'F5 TopRate sectionals': [f'{a}_{c}' for c in ('sect_i_l400', 'sect_i_l200', 'sect_i_early') for a in ('p1', 'm4', 's4')] + ['f_sect_rel'],
        'F6 race shape history': [f'{a}_{c}' for c in ('raceShapeLate', 'raceShapeEarly', 'raceShapeMid') for a in ('p1', 'm4')],
        'F7 comment flags': [f'{a}_{k}' for k in FLAGS for a in ('pf', 'rf')],
        'F8 closing gain history': ['p1_cg', 'm4_cg', 's4_cg'],
        'F9 rating, class, trend': ['m4_wpr', 'p1_wpr', 's4_wpr', 'wpr_trend', 'cls', 'dchg', 'lastdist'],
        'F10 market': ['lpo', 'lpm'],
        'F11 going and track history': ['gs', 'gs_chg', 'grd', 'wet', 'x_hvenue', 'x_hgoing', 'x_hband', 'xn_hband'],
        'F12 field closing profile': ['f_L_hist', 'f_L_rel'],
    }
    for c in {x for v in fam.values() for x in v}:
        if c in d.columns and d[c].dtype == object:
            d[c] = pd.to_numeric(d[c].replace({True: 1, False: 0, 'True': 1, 'False': 0}), errors='coerce')
    tr = d[(d.date < '2025-01-01') & d.h_E.notna()]
    te = d[(d.date >= '2025-01-01') & d.h_E.notna()]
    print(f'fit before 2025: {len(tr):,} runs; scored 2025 on: {len(te):,} runs in {te.key.nunique():,} races\n')

    def r2(cols, c):
        m = lgb.LGBMRegressor(**P).fit(tr[cols], tr[f'd_{c}'])
        pr = m.predict(te[cols])
        y = te[f'd_{c}']
        return 1 - ((y - pr) ** 2).sum() / ((y - y.mean()) ** 2).sum(), m
    res = {}
    for c in ('L', 'T'):
        b, _ = r2(base, c)
        res[c] = {'base': b}
        for nm, cols in fam.items():
            v, _ = r2(base + cols, c)
            res[c][nm] = v
        allc = base + [x for v in fam.values() for x in v]
        res[c]['ALL'], m = r2(allc, c)
        imp = pd.Series(m.booster_.feature_importance('gain'), index=allc).sort_values(ascending=False)
        res[c]['top'] = imp.head(15)
    print(f'{"family":30s} {"R2 last 400m":>13s} {"gain":>8s}   {"R2 total":>9s} {"gain":>8s}')
    print(f'{"base (own GPS history + basics)":30s} {res["L"]["base"]:13.4f} {"":8s}   {res["T"]["base"]:9.4f}')
    for nm in list(fam) + ['ALL']:
        print(f'{nm:30s} {res["L"][nm]:13.4f} {res["L"][nm] - res["L"]["base"]:+8.4f}   {res["T"][nm]:9.4f} {res["T"][nm] - res["T"]["base"]:+8.4f}')
    print('\ntop inputs by gain, all together, last 400m:')
    print((100 * res['L']['top'] / res['L']['top'].sum()).round(1).to_string())
    print(f'\nsd of L deficit in 2025 on: {te.d_L.std():.3f}s; sd of T: {te.d_T.std():.3f}s')


if __name__ == '__main__':
    sys.exit(main())
