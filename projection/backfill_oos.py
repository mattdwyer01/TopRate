"""Out-of-sample back-fill of the projection log for races that ran before the log existed on the current models (13 Oct 2026).

The shipped models are trained through the latest results, so re-scoring a past race with them would be in-sample. This script trains the
same models on data BEFORE `--from` only (main model fitted through 2026-06, early-stopped on 2026-07..09; light models likewise; the
suitability model fitted on the main model's out-of-sample residuals from before 2026-07) and scores every rated run from `--from`
to the end of the results files with them. Rows are written to wpr_projection_log.csv.gz with src = 'oos', run_id and race_id taken from
runners.csv (matched on date and horse name), made = after the race, and no grp split. One seed per model, so a little noisier than live.

usage: python projection/backfill_oos.py --from 2026-10-01 [--dry-run]
"""
import argparse
import json
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import features as F  # noqa: E402
import projlog as plog  # noqa: E402
import train_light as TL  # noqa: E402
import train_main as T  # noqa: E402
import train_suit as TS  # noqa: E402
from own_ratings.rc_join import norm_horse  # noqa: E402

M = F.MODELS
WT_K = 0.4
FIT_END = '2026-07-01'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--from', dest='start', default='2026-10-01')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    sfeats = json.load(open(os.path.join(M, 'suitability_features.json')))
    feats = T.ORIGINAL + F.LADDER_FEATURES
    # ---------------- main model
    L = T.assemble()
    ph = F.build_pos_hist(L)
    L = L[(L.nruns >= 3) & L[T.BASE].notna().all(axis=1) & L.wpr.notna() & (L.date >= '2018-01-01')].copy()
    # A: trained before 2025 -> out-of-sample residuals 2025-01 .. end, for the suitability fit
    trA, vaA = L[L.date < '2025-01-01'], L[(L.date >= '2025-01-01') & (L.date < '2025-07-01')]
    mA, cA = T.fit(trA, feats, None, 1, valid=vaA)
    oos = L[L.date >= '2025-01-01'].copy()
    oos['base'] = np.c_[np.ones(len(oos)), oos[T.BASE].values] @ cA + mA.predict(oos[feats], num_iteration=mA.best_iteration)
    oos['res'] = oos.wpr - oos.base
    S = F.build_suit(F.load_results_all(), ph).drop_duplicates(['race_id', 'horse_id'])
    Z = oos[['race_id', 'horse_id', 'date', 'res', 'bf', 'field_size', 'dist', 'going_num']].merge(S.drop(columns=['date']), on=['race_id', 'horse_id'], how='left', suffixes=('', '_s'))
    Z = Z.merge(ph[['race_id', 'horse_id', 'm800_hist3', 'own_rel']], on=['race_id', 'horse_id'], how='left')
    Z['sty'] = Z.pos_hist3 - 0.5
    Z['i_front'], Z['i_front2'] = Z.fa_cum * Z.sty, Z.fa_last * Z.sty
    Z['i_out'], Z['i_out2'] = Z.oa_cum * (Z.bf - 0.5), Z.oa_last * (Z.bf - 0.5)
    Z['j_style'], Z['j_p8_x'] = Z.j_dev * Z.sty, Z.j_p8 - Z.pos_hist3
    for c in sfeats:
        if c not in Z.columns:
            Z[c] = np.nan
    fitZ = Z[Z.date < FIT_END]
    suit = lgb.train(TS.PARAMS, lgb.Dataset(fitZ[sfeats], fitZ.res.values), TS.ROUNDS)
    print('suitability fitted on', len(fitZ), 'residuals before', FIT_END, flush=True)
    # B: main model trained before FIT_END, stopped on Jul..Sep, scores the back-fill window
    trB, vaB = L[L.date < FIT_END], L[(L.date >= FIT_END) & (L.date < a.start)]
    mB, cB = T.fit(trB, feats, None, 1, valid=vaB)
    tgt = L[L.date >= a.start].copy()
    tgt['base'] = np.c_[np.ones(len(tgt)), tgt[T.BASE].values] @ cB + mB.predict(tgt[feats], num_iteration=mB.best_iteration)
    Zt = tgt[['race_id', 'horse_id', 'bf', 'field_size', 'dist', 'going_num']].merge(
        S.drop(columns=['date']), on=['race_id', 'horse_id'], how='left', suffixes=('', '_s')).merge(ph[['race_id', 'horse_id', 'm800_hist3', 'own_rel']], on=['race_id', 'horse_id'], how='left')
    Zt['sty'] = Zt.pos_hist3 - 0.5
    Zt['i_front'], Zt['i_front2'] = Zt.fa_cum * Zt.sty, Zt.fa_last * Zt.sty
    Zt['i_out'], Zt['i_out2'] = Zt.oa_cum * (Zt.bf - 0.5), Zt.oa_last * (Zt.bf - 0.5)
    Zt['j_style'], Zt['j_p8_x'] = Zt.j_dev * Zt.sty, Zt.j_p8 - Zt.pos_hist3
    for c in sfeats:
        if c not in Zt.columns:
            Zt[c] = np.nan
    Zt['adj'] = suit.predict(Zt[sfeats])
    tgt = tgt.merge(Zt[['race_id', 'horse_id', 'adj']], on=['race_id', 'horse_id'], how='left')
    tgt['wtadj'] = -WT_K * tgt.wt_rel.fillna(0.0)
    tgt['proj'] = tgt.base + tgt.adj.fillna(0) + tgt.wtadj
    tgt['model'] = 'main'
    tgt['sd'] = [6.75 if p >= 70 else 7.31 if p >= 60 else 7.55 for p in tgt.proj]
    main_rows = tgt[['race_id', 'horse_id', 'date', 'proj', 'base', 'adj', 'wtadj', 'sd', 'model', 'nruns']].copy()
    print('main rows', len(main_rows), flush=True)
    del L, S, Z, oos
    # ---------------- light models
    H = F.load_history()
    levels = json.load(open(os.path.join(M, 'levels.json')))
    LL, t3 = TL.assemble(H, levels)
    LL['lp'] = np.log(LL.priceStarting.where(LL.priceStarting > 1))
    LL = LL[(LL.nruns <= 2) & (LL.date >= '2019-01-01')].copy()
    LL['sex'] = pd.Categorical(LL.horse_sex, categories=levels['sex'])
    trL, vaL, tgL = LL[LL.date < FIT_END], LL[(LL.date >= FIT_END) & (LL.date < a.start)], LL[LL.date >= a.start].copy()
    tgL['proj0'] = np.nan
    for price in (True, False):
        fl = TL.light_features(t3, price)
        mm = lgb.train(dict(TL.PARAMS, seed=1), lgb.Dataset(trL[fl], trL.wpr), 3000, valid_sets=[lgb.Dataset(vaL[fl], vaL.wpr)], callbacks=[lgb.early_stopping(60, verbose=False)])
        p = mm.predict(tgL[fl], num_iteration=mm.best_iteration)
        use = tgL.lp.notna() if price else tgL.lp.isna()
        tgL.loc[use, 'proj0'] = p[use.values]
    tgL['base'] = tgL.proj0
    tgL['adj'] = 0.0
    tgL['wtadj'] = -WT_K * tgL.wt_rel.fillna(0.0)
    tgL['proj'] = tgL.base + tgL.wtadj
    tgL['model'] = 'light'
    li = json.load(open(os.path.join(M, 'light_info.json')))
    tgL['sd'] = [li['stage_sd'].get(str(int(n)), 11.0) for n in tgL.nruns]
    light_rows = tgL[['race_id', 'horse_id', 'date', 'proj', 'base', 'adj', 'wtadj', 'sd', 'model', 'nruns']].copy()
    rows = pd.concat([main_rows, light_rows], ignore_index=True)
    rows = rows.loc[:, ~rows.columns.duplicated()]
    rows['date'] = pd.to_datetime(rows.date)
    print('rows scored', len(rows), rows.groupby('model').proj.agg(['count', 'mean', 'std']).round(1).to_dict(), flush=True)
    # ---------------- map to the runner rows (their run_id and race_id are what the log and the dashboard use)
    names = pd.concat([pd.read_csv(f, usecols=['race_id', 'horse_id', 'horse', 'date'], low_memory=False) for f in sorted(__import__('glob').glob(os.path.join(F.ROOT, 'race_results_20*.csv.gz')))])
    names = names.drop_duplicates(['race_id', 'horse_id'])
    rows = rows.merge(names[['race_id', 'horse_id', 'horse']], on=['race_id', 'horse_id'], how='left')
    rows['h'] = rows.horse.map(norm_horse)
    rows['d'] = rows.date.dt.strftime('%Y-%m-%d')
    import runners_io
    R = runners_io.read_runners()
    R = R[(R.date.astype(str).str[:10] >= a.start)].copy()
    R['h'] = R.horse.map(norm_horse)
    R['d'] = R.date.astype(str).str[:10]
    R = R.drop_duplicates(['d', 'h'])
    m = rows.merge(R[['d', 'h', 'run_id', 'race_id']].rename(columns={'race_id': 'rrace'}), on=['d', 'h'], how='inner')
    out = pd.DataFrame({'run_id': pd.to_numeric(m.run_id, errors='coerce'), 'race_id': pd.to_numeric(m.rrace, errors='coerce'), 'date': m.date, 'proj': m.proj.round(2),
                        'base': m.base.round(2), 'adj': m.adj.round(2), 'wtadj': m.wtadj.round(2), 'sd': m.sd, 'model': m.model, 'nruns': m.nruns, 'grp': None, 'src': 'oos',
                        'made': '2026-10-13T00:00:00Z', 'atwo': np.nan, 'sadj': np.nan, 'badj': np.nan}).dropna(subset=['run_id', 'race_id'])
    out['run_id'], out['race_id'] = out.run_id.astype('int64'), out.race_id.astype('int64')
    print('matched to runner rows', len(out), 'of', len(rows), 'dates', out.date.dt.strftime('%m-%d').value_counts().sort_index().to_dict(), flush=True)
    if a.dry_run:
        out.to_pickle(os.path.join(os.environ.get('TMPDIR', '/tmp'), 'backfill_oos_rows.pkl'))
        return
    old = plog.load()
    keep = old[~old.run_id.isin(out.run_id)]
    new = pd.concat([keep, out[plog.COLS]], ignore_index=True)
    new = new.sort_values(['date', 'race_id', 'run_id'])
    new.to_csv(plog.PATH, index=False, compression='gzip', float_format='%.2f')
    print('log now', len(new), 'rows')


if __name__ == '__main__':
    main()
