"""Four Proj improvement tests in one (9 Nov 2026, owner: "try all 4"). Same live structure as research/proj_trials_test.py (projection/train_ctx.py --v2 --conv-frac 1.0
--fit-feats --trials: runner-page ATW ratings plus converted results-file history for TRAINING rows, option 2 inputs, fit and trial inputs, Huber 4), fit before 2026-01-01
(early stop 2025-10..12). Variants (name:seed):
  base  the live inputs.
  ped   + pedigree and young-horse inputs: sire / dam-sire offspring (shrunk mean of their formula residuals, and of their ratings), sire at the distance band and on wet
        tracks, the dam's other offspring, the trainer's record with horses on their 1st to 3rd run. As of the day before, from converted history plus later page runs.
  dirf  + the finishing-position model's inputs the Proj lacks: age, sex, win and place share over the last 8, mean finish position and margin over the last 4,
        8-run mean and best rating, and those against the field.
  fld   the base inputs, but the field inputs (field mean, rank and gap in the field) are blanked on the runner-page TRAINING rows, which hold only part of each past field,
        so the model learns field effects from complete (converted) fields only, as live fields are complete.
  all   ped + dirf.
Each job writes predictions for two test sets to <out>_<test>.pkl: 'pg' = 2026 runner-page runs (as the earlier tests), 'cv' = 2026 complete fields from the results files on the
page scale (converted history to CONV_TO), the faithful test for complete fields. research/proj_improve4_combine.py scores them (and the 3-seed bags).
Run: PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/proj_improve4.py --jobs base:1,fld:1 --out research/pi4/j1"""
import argparse, glob, json, os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C

ap = argparse.ArgumentParser(); ap.add_argument('--jobs', required=True); ap.add_argument('--out', required=True); ap.add_argument('--conv-to', default='2026-10-08'); ap.add_argument('--frac', type=float, default=1.0); ap.add_argument('--trees', type=int, default=4000)
a = ap.parse_args()
JOBS = [(j.split(':')[0], int(j.split(':')[1])) for j in a.jobs.split(',')]
CUT, ES = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')

import conv_history as CH, features as FT
real = FT.runner_page_runs().copy()
FT._TR_CACHE['rows'] = CH.build(2020, a.conv_to, a.frac)
cv = C.training_frame_rel(True); cv = cv[cv.f.notna()].copy()
FT._TR_CACHE['rows'] = real
pg = C.training_frame_rel(True); pg = pg[pg.f.notna()].copy()
cv['src'], pg['src'] = 'cv', 'pg'
print('frames: converted', len(cv), 'page', len(pg), flush=True)

# ---- static horse facts from the results files: foaling season (age), sex, sire, dam, dam-sire ----
parts = []
for f in sorted(glob.glob('race_results_20[12]*.csv.gz')):
    if '_rc' in f:
        continue
    parts.append(pd.read_csv(f, usecols=lambda c: c in ('horse_id', 'date', 'horse_age', 'horse_sex', 'sire_id', 'dam_id', 'sire_of_dam'), low_memory=False))
S = pd.concat(parts, ignore_index=True)
S['horse_id'] = pd.to_numeric(S.horse_id, errors='coerce'); S = S.dropna(subset=['horse_id'])
S['date'] = pd.to_datetime(S.date)
season = lambda d: d.dt.year - (d.dt.month < 8).astype(int)
S['foal'] = season(S.date) - pd.to_numeric(S.horse_age, errors='coerce')
sx = S.horse_sex.astype(str).str.upper().str[:1].map({'G': 0, 'R': 0, 'M': 1, 'F': 1, 'C': 2, 'H': 2})
S['sex'] = sx
H = S.sort_values('date').groupby('horse_id').agg(foal=('foal', 'median'), sex=('sex', 'last'), sire=('sire_id', 'last'), dam=('dam_id', 'last'), dsire=('sire_of_dam', 'last'))
H['dsire'] = H.dsire.astype(str).str.upper().str.strip().where(H.dsire.notna())
H['dsire'] = H.dsire.astype('category').cat.codes.astype(float).where(H.dsire.notna())
print('horses with static facts', len(H), flush=True)


def add_static(df):
    df = df.copy()
    h = H.reindex(df.horse_id.values)
    df['age'] = (season(pd.to_datetime(df.date)) - h.foal.values).astype(float)
    df['age'] = df.age.where(df.age.between(1, 15))
    df['sex_c'] = h.sex.values; df['sire'] = h.sire.values; df['dam'] = h.dam.values; df['dsire'] = h.dsire.values
    df['dband'] = pd.cut(df.distance, [0, 1200, 1600, 2000, 9999], labels=False).astype(float)
    df['wet'] = (df.going_n >= 5).astype(float)
    return df


cv, pg = add_static(cv), add_static(pg)

# ---- pedigree / young-horse inputs, as of the day before, from converted history plus page runs after it ----
SRC = pd.concat([cv[['horse_id', 'date', 'resid', 'wpr', 'dband', 'wet', 'n', 'trainer', 'sire', 'dam', 'dsire']],
                 pg.loc[pg.date > pd.Timestamp(a.conv_to), ['horse_id', 'date', 'resid', 'wpr', 'dband', 'wet', 'n', 'trainer', 'sire', 'dam', 'dsire']]], ignore_index=True)
SRC = SRC[SRC.resid.notna()].copy()
MU = float(SRC.wpr.mean())
SRC['wdev'] = SRC.wpr - MU


def asof(keys, tgt, val, mask=None):
    s = SRC if mask is None else SRC[mask]
    s = s.dropna(subset=keys + [val])
    g = s.groupby(keys + ['date'])[val].agg(['sum', 'count']).reset_index().sort_values('date')
    g['S'] = g.groupby(keys)['sum'].cumsum(); g['C'] = g.groupby(keys)['count'].cumsum()
    t = tgt[keys + ['date']].copy(); t['_i'] = np.arange(len(t)); t = t.dropna(subset=keys)
    for k in keys:
        t[k] = t[k].astype(float); g[k] = g[k].astype(float)
    t = t.sort_values('date')
    m = pd.merge_asof(t, g[keys + ['date', 'S', 'C']], on='date', by=keys, allow_exact_matches=False)
    Sv, Cv = np.zeros(len(tgt)), np.zeros(len(tgt))
    Sv[m._i.values] = m.S.fillna(0).values; Cv[m._i.values] = m.C.fillna(0).values
    return Sv, Cv


def others(key, tgt, val, K, mask=None, extra=()):
    """shrunk mean of val over the key group's runs before the date, the horse's own runs taken out."""
    s1, c1 = asof([key, *extra], tgt, val, mask)
    s2, c2 = asof([key, *extra, 'horse_id'], tgt, val, mask)
    s, c = s1 - s2, c1 - c2
    return s / (c + K), c


PED = ['sire_eff', 'sire_lvl', 'sire_n', 'sire_dist_eff', 'sire_wet_eff', 'dsire_eff', 'dsire_lvl', 'dam_eff', 'dam_lvl', 'dam_n', 'trn_yng_eff', 'trn_yng_n']


def add_ped(df):
    df = df.copy()
    df['sire_eff'], df['sire_n'] = others('sire', df, 'resid', 30)
    df['sire_lvl'], _ = others('sire', df, 'wdev', 30)
    df['sire_dist_eff'], _ = others('sire', df, 'resid', 30, extra=('dband',))
    wet = SRC.wet == 1
    df['sire_wet_eff'], _ = others('sire', df, 'resid', 30, mask=wet)
    df['dsire_eff'], _ = others('dsire', df, 'resid', 30)
    df['dsire_lvl'], _ = others('dsire', df, 'wdev', 30)
    df['dam_eff'], df['dam_n'] = others('dam', df, 'resid', 5)
    df['dam_lvl'], _ = others('dam', df, 'wdev', 5)
    yng = SRC.n <= 2
    tr_codes = {t: i for i, t in enumerate(pd.concat([SRC.trainer, df.trainer]).dropna().astype(str).unique())}
    SRC['trn'] = SRC.trainer.astype(str).map(tr_codes).where(SRC.trainer.notna())
    df['trn'] = df.trainer.astype(str).map(tr_codes).where(df.trainer.notna())
    s, c = asof(['trn'], df, 'resid', yng)
    df['trn_yng_eff'], df['trn_yng_n'] = s / (c + 20), c
    for k in ('sire', 'dsire', 'dam'):
        miss = df[k].isna()
        for col in [x for x in PED if x.startswith(k + '_')]:
            df.loc[miss, col] = np.nan
    return df


DIRF_BASE = ['age', 'win8', 'plc8', 'm4_finpct', 'm4_mfin', 'm8', 'max8']
DIRF = ['age', 'sex_c', 'win8', 'plc8', 'm4_finpct', 'm4_mfin', 'm8', 'max8'] + [p + c for c in DIRF_BASE + ['weightCarried', 'barr_f'] for p in ('r_', 'k_')]


def add_dirf(df):
    df = df.copy()
    o = df.sort_values(['horse_id', 'date'])
    pos, fs = o.positionFinish, o.field_size
    vals = {'won': (pos == 1).astype(float).where(pos.notna()), 'plc': (pos <= 3).astype(float).where(pos.notna()),
            'fp': ((pos - 1) / (fs - 1)).clip(0, 1).where(pos.notna() & (fs > 1)), 'mg': o.marginFinish.clip(0, 30)}
    hid = o.horse_id
    out = {}
    for nm, v, k in (('win8', 'won', 8), ('plc8', 'plc', 8), ('m4_finpct', 'fp', 4), ('m4_mfin', 'mg', 4)):
        x = vals[v]; cs = x.fillna(0).groupby(hid).cumsum(); cc = x.notna().astype(float).groupby(hid).cumsum()
        s = cs.groupby(hid).shift(1).fillna(0) - cs.groupby(hid).shift(k + 1).fillna(0)
        c = cc.groupby(hid).shift(1).fillna(0) - cc.groupby(hid).shift(k + 1).fillna(0)
        out[nm] = (s / c.where(c > 0)).reindex(df.index)
    for nm, s in out.items():
        df[nm] = s
    R = df[[f'r{k}' for k in range(1, 9)]]
    df['m8'], df['max8'] = R.mean(axis=1), R.max(axis=1)
    return C.add_field_rel(df, DIRF_BASE + ['weightCarried', 'barr_f'])


cv, pg = add_ped(cv), add_ped(pg)
cv, pg = add_dirf(cv), add_dirf(pg)
for nm, d in (('converted', cv), ('page', pg)):
    print(nm, 'coverage:', {c: round(float(d[c].notna().mean()), 3) for c in ('age', 'sex_c', 'sire_eff', 'dam_eff', 'dsire_eff', 'win8', 'm8')}, flush=True)

classes = sorted(pg.cls.dropna().unique().tolist())
for d in (cv, pg):
    d['cls_c'] = C._cls(d.cls, classes)
pa = pd.concat([cv[cv.date < CUT], pg[pg.date < CUT]], ignore_index=True)
tr, va = pa[pa.date < ES], pa[(pa.date >= ES) & (pa.date < CUT)]
tests = {'pg': pg[pg.date >= CUT].copy(), 'cv': cv[cv.date >= CUT].copy()}
FIELD_COLS = ['fld_other', 'f_vs_fld'] + C.FLD_FEATS + C.FLD_REL_FEATS

F0 = C.FEATS2 + C.TRIAL_FEATS
F1 = C.FEATS2 + C.REL_FEATS2 + C.FIT_FEATS + C.TRIAL_FEATS
SETS = {'base': (F0, F1), 'fld': (F0, F1), 'ped': (F0 + PED, F1 + PED), 'dirf': (F0 + DIRF, F1 + DIRF), 'all': (F0 + PED + DIRF, F1 + PED + DIRF)}
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]

out = {k: t[['horse_id', 'date', 'wpr', 'positionFinish', 'n', 'd_last', 'field_size', 'vn', 'distance', 'cls']].copy() for k, t in tests.items()}
for k, t in out.items():
    t['f'] = tests[k].f.values
info = {}
for name, seed in JOBS:
    A, B = SETS[name]
    P = dict(n_estimators=a.trees, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1,
             objective='huber', alpha=4.0, random_state=seed)
    t0, v0 = tr, va
    if name == 'fld':
        t0, v0 = tr.copy(), va.copy()
        for d in (t0, v0):
            d.loc[d.src == 'pg', FIELD_COLS] = np.nan
    fit = lambda F, t, v: lgb.LGBMRegressor(**P).fit(t[F], t.resid, eval_set=[(v[F], v.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    m0 = fit(A, t0, v0); m1 = fit(B, rel(t0), rel(v0))
    col = f'{name}_s{seed}'
    for k, te in tests.items():
        use = (te.n >= C.REL_MIN_RUNS).values
        c = m0.predict(te[A]); c[use] = m1.predict(te.loc[use, B])
        c = np.where(use, c, np.clip(c, -2, 2))           # run.py CTX_CAP_FEW for under 3 runs
        out[k][col] = te.f.values + c
    imp = pd.Series(m1.booster_.feature_importance('gain'), index=B)
    newf = [x for x in B if x not in F1]
    info[col] = dict(trees=int(m1.best_iteration_), trees_plain=int(m0.best_iteration_),
                     new_share=round(float(imp[newf].sum() / imp.sum()), 4) if newf else 0.0,
                     top_new={x: round(float(v), 4) for x, v in (imp[newf] / imp.sum()).sort_values(ascending=False).head(8).items()} if newf else {})
    print(col, info[col], flush=True)
os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
for k, t in out.items():
    t.to_pickle(f'{a.out}_{k}.pkl')
json.dump(info, open(f'{a.out}_info.json', 'w'), indent=1)
