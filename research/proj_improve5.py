"""Proj improvement tests, batch 5 (10 Nov 2026, owner: "try everything, even if it has been tried"). Same live structure and split as research/proj_improve4.py
(runner-page ATW ratings plus converted results-file history for TRAINING rows, option 2 inputs, fit and trial inputs, Huber 4, fit before 2026-01-01, early stop 2025-10..12;
tests 'pg' = 2026 runner-page runs and 'cv' = 2026 complete converted fields). Starting point: nearly every earlier fit stopped at the 4,000 tree cap, so the model was
still improving when training ended. Variants (name:seed):
 training only (live inputs)
  base   the live settings (lr 0.03, 4,000 tree cap)                 long   lr 0.03, 16,000 cap
  lr06   lr 0.06, 10,000 cap (reference for everything below)        big    127 leaves        deep  255 leaves, 60% columns
  cs5    50% columns per tree     small  15 leaves     reg  heavier regularisation     hub25 / hub8  Huber alpha 2.5 / 8
  wrec   recency weights (3 year decay)       wpg   runner-page rows weighted x3
  rdm    target = residual minus its race mean (races of 4+ rows); the combine step keeps lr06's race level and takes the within-race order from this one
         (RESULT: its apparent +0.007 was the missing cap for under-3-run horses on these columns; against the uncapped usual model it adds nothing, see lr06.N in batch 8)
  cat    CatBoost on the same inputs (a different learner, also averaged with lr06)
  h16    converted history from 2016 instead of 2020 (run with --conv-from 2016)
 new inputs (lr06 settings)
  frank  collateral form: for each of the horse's last 3 races, how the OTHER runners ran against their own figures in that race (race level surprise) and in their next
         run since (form franked or not), as of the day before
  jsw    jockey switch: today's jockey against the jockey of the last run (win rates and rating effect, as of today)
  tfu    trainer patterns as of the day before: overall, first up, at this venue, at this distance band, on wet, with this jockey; jockey at this venue
  lfld   strength of the horse's last three fields (its figure against the other runners' then)
  l2 / xt / lin  squared error / extra-random trees / linear leaves;  one  a single model for every run count;  cshort  no converted rows after 2025-03 (value of the newest ones);
  nopg   converted rows only
  frm    more inputs as runner minus field mean and rank in field;  allz  ped + dirf + tfu + frank + lfld + frm
  a name may end in .R (within-race target, as rdm), .C (CatBoost), .RC, or .N (no cap on the step for horses with under 3 runs), e.g. allx.R, dirf.RC, ped.N
  ped    pedigree block of batch 4      dirf  finishing-position inputs of batch 4       allx  all of the above
Run: PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/proj_improve5.py --jobs base:1,lr06:1 --out pi5/j1"""
import argparse, glob, json, os, sys, time
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
import ctx as C

ap = argparse.ArgumentParser(); ap.add_argument('--jobs', required=True); ap.add_argument('--out', required=True); ap.add_argument('--conv-to', default='2026-10-08')
ap.add_argument('--conv-from', type=int, default=2020); ap.add_argument('--frac', type=float, default=1.0); ap.add_argument('--tree-scale', type=float, default=1.0)
a = ap.parse_args()
JOBS = [(j.split(':')[0], int(j.split(':')[1])) for j in a.jobs.split(',')]
CUT, ES, CONV_TO = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01'), pd.Timestamp(a.conv_to)
T0 = time.time()
log = lambda *x: print(f'[{(time.time() - T0) / 60:5.1f}m]', *x, flush=True)

import conv_history as CH, features as FT, rates as RT
real = FT.runner_page_runs().copy()
FT._TR_CACHE['rows'] = CH.build(a.conv_from, a.conv_to, a.frac)
cv = C.training_frame_rel(True); cv = cv[cv.f.notna()].copy()
FT._TR_CACHE['rows'] = real
pg = C.training_frame_rel(True); pg = pg[pg.f.notna()].copy()
cv['src'], pg['src'] = 'cv', 'pg'
cv, pg = cv.reset_index(drop=True), pg.reset_index(drop=True)
log('frames: converted', len(cv), 'page', len(pg))
NEED = {n.split('.')[0] for n, _ in JOBS}
want = lambda *names: bool(NEED & set(names))

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
S['sex'] = S.horse_sex.astype(str).str.upper().str[:1].map({'G': 0, 'R': 0, 'M': 1, 'F': 1, 'C': 2, 'H': 2})
H = S.sort_values('date').groupby('horse_id').agg(foal=('foal', 'median'), sex=('sex', 'last'), sire=('sire_id', 'last'), dam=('dam_id', 'last'), dsire=('sire_of_dam', 'last'))
H['dsire'] = H.dsire.astype(str).str.upper().str.strip().where(H.dsire.notna())
H['dsire'] = H.dsire.astype('category').cat.codes.astype(float).where(H.dsire.notna())
del S, parts


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
# key codes shared by both frames
jk_all = pd.concat([cv.jockey, pg.jockey]).map(RT.nk)
codes = {k: i for i, k in enumerate(jk_all.dropna().unique())}
tr_codes = {t: i for i, t in enumerate(pd.concat([cv.trainer, pg.trainer]).dropna().astype(str).unique())}
vn_codes = {t: i for i, t in enumerate(pd.concat([cv.vn, pg.vn]).dropna().astype(str).unique())}
for d in (cv, pg):
    d['jkc'] = d.jockey.map(RT.nk).map(codes)
    d['trn'] = d.trainer.astype(str).map(tr_codes).where(d.trainer.notna())
    d['vnc'] = d.vn.astype(str).map(vn_codes).where(d.vn.notna() & (d.vn != ''))

SCOLS = ['horse_id', 'date', 'resid', 'wpr', 'dband', 'wet', 'n', 'd_last', 'trn', 'jkc', 'vnc', 'sire', 'dam', 'dsire']
SRC = pd.concat([cv[SCOLS], pg.loc[pg.date > CONV_TO, SCOLS]], ignore_index=True)
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
    df['sire_wet_eff'], _ = others('sire', df, 'resid', 30, mask=SRC.wet == 1)
    df['dsire_eff'], _ = others('dsire', df, 'resid', 30)
    df['dsire_lvl'], _ = others('dsire', df, 'wdev', 30)
    df['dam_eff'], df['dam_n'] = others('dam', df, 'resid', 5)
    df['dam_lvl'], _ = others('dam', df, 'wdev', 5)
    s, c = asof(['trn'], df, 'resid', SRC.n <= 2)
    df['trn_yng_eff'], df['trn_yng_n'] = s / (c + 20), c
    for k in ('sire', 'dsire', 'dam'):
        miss = df[k].isna()
        for col in [x for x in PED if x.startswith(k + '_')]:
            df.loc[miss, col] = np.nan
    return df


TFU = ['trn_eff', 'trn_n', 'trn_fu_eff', 'trn_fu_n', 'trn_ven_eff', 'trn_ven_n', 'jk_ven_eff', 'tj_eff', 'tj_n', 'trn_db_eff', 'trn_wet_eff']


def add_tfu(df):
    df = df.copy()
    sh = lambda sc, K: (sc[0] / (sc[1] + K), sc[1])
    df['trn_eff'], df['trn_n'] = sh(asof(['trn'], df, 'resid'), 50)
    df['trn_fu_eff'], df['trn_fu_n'] = sh(asof(['trn'], df, 'resid', SRC.d_last > 60), 30)
    df['trn_ven_eff'], df['trn_ven_n'] = sh(asof(['trn', 'vnc'], df, 'resid'), 20)
    df['jk_ven_eff'], _ = sh(asof(['jkc', 'vnc'], df, 'resid'), 20)
    df['tj_eff'], df['tj_n'] = sh(asof(['trn', 'jkc'], df, 'resid'), 20)
    df['trn_db_eff'], _ = sh(asof(['trn', 'dband'], df, 'resid'), 30)
    df['trn_wet_eff'], _ = sh(asof(['trn'], df, 'resid', SRC.wet == 1), 30)
    df.loc[df.trn.isna(), [c for c in TFU if c.startswith('trn') or c.startswith('tj')]] = np.nan
    return df


JSW = ['jk_same', 'jw_l', 'jw_d', 'jw90_d', 'jeff_l', 'jeff_d']


def add_jsw(df):
    df = df.copy()
    o = df.sort_values(['horse_id', 'date'])
    lj = o.groupby('horse_id').jockey.shift(1).reindex(df.index)
    tmp = pd.DataFrame({'date': df.date.values, 'jockey': lj.values, 'trainer': None}, index=df.index)
    r = RT.add_rates(tmp)
    je = C.add_jockey(tmp[['date', 'jockey']].copy(), C.jockey_table(df), targets=True).jock_eff
    df['jk_same'] = (lj.map(RT.nk) == df.jockey.map(RT.nk)).astype(float).where(lj.notna())
    df['jw_l'] = r.jw.values
    df['jw_d'] = df.jw - r.jw.values
    df['jw90_d'] = df.jw90 - r.jw90.values
    df['jeff_l'] = np.where(lj.notna(), je.values, np.nan)
    df['jeff_d'] = df.jock_eff - df.jeff_l
    return df


FRK = [f'{p}{k}' for k in (1, 2, 3) for p in ('rl', 'rln', 'fk', 'fkd', 'fkn')] + ['rl_w', 'fk_w']


def build_frank():
    """RUN: one row per (horse, date) with a race key; per race the others' mean residual; and the sorted next-run table for 'franked since' sums."""
    cols = ['horse_id', 'date', 'resid', 'rk', 'w', 'src']
    A = cv.assign(rk=C._race_key(cv), w=cv.wpr_plain if 'wpr_plain' in cv.columns else cv.wpr)[cols]
    B = pg[pg.date > CONV_TO].assign(rk=C._race_key(pg), w=pg.wpr)[cols]
    R = pd.concat([A, B], ignore_index=True).drop_duplicates(['horse_id', 'date']).sort_values(['horse_id', 'date']).reset_index(drop=True)
    R['rc'] = pd.factorize(R.rk)[0]
    R['di'] = R.date.values.astype('datetime64[D]').astype('int64')
    g = R.groupby('horse_id')
    R['dn'] = g.di.shift(-1); R['rn'] = g.resid.shift(-1)
    R['dw'] = (g.w.shift(-1) - R.w).where(g.src.shift(-1) == R.src)
    nrc = int(R.rc.max()) + 1
    ok = R.resid.notna().values
    Ssum = np.bincount(R.rc.values[ok], weights=R.resid.values[ok], minlength=nrc); Scnt = np.bincount(R.rc.values[ok], minlength=nrc).astype(float)
    V = R[R.dn.notna() & R.rn.notna()].copy()
    V['key'] = V.rc.values.astype('int64') * 1_000_000 + V.dn.values.astype('int64')
    V = V.sort_values('key')
    z = lambda x: np.concatenate([[0.0], np.cumsum(x)])
    tab = dict(keys=V.key.values, cr=z(V.rn.values), cd=z(V.dw.fillna(0).values), cdn=z(V.dw.notna().astype(float).values))
    return R, Ssum, Scnt, tab


def add_frank(df, FR):
    R, Ssum, Scnt, tab = FR
    df = df.copy()
    o = df.sort_values(['horse_id', 'date'])
    look = R.reset_index()[['horse_id', 'date', 'index']].rename(columns={'date': 'ld', 'index': 'ri'})
    ti = df.date.values.astype('datetime64[D]').astype('int64')
    new = {}
    for k in (1, 2, 3):
        ld = o.groupby('horse_id').date.shift(k).reindex(df.index)
        q = pd.DataFrame({'horse_id': df.horse_id.values, 'ld': ld.values}).merge(look, on=['horse_id', 'ld'], how='left')
        ri = q.ri.values; has = ~np.isnan(ri); r = np.where(has, ri, 0).astype(int)
        rc = R.rc.values[r]; own = R.resid.values[r]; own_ok = ~np.isnan(own)
        n_oth = Scnt[rc] - own_ok
        rl = (Ssum[rc] - np.where(own_ok, own, 0.0)) / np.where(n_oth > 0, n_oth, np.nan)
        lo = np.searchsorted(tab['keys'], rc.astype('int64') * 1_000_000, side='left')
        hi = np.searchsorted(tab['keys'], rc.astype('int64') * 1_000_000 + ti, side='left')
        sr, sd, nd, nn = tab['cr'][hi] - tab['cr'][lo], tab['cd'][hi] - tab['cd'][lo], tab['cdn'][hi] - tab['cdn'][lo], (hi - lo).astype(float)
        # the horse's own next run after that race is not a rival's
        odn, orn, odw = R.dn.values[r], R.rn.values[r], R.dw.values[r]
        mine = (~np.isnan(odn)) & (~np.isnan(orn)) & (odn < ti)
        sr = sr - np.where(mine, orn, 0.0); nn = nn - mine
        md = mine & ~np.isnan(odw)
        sd = sd - np.where(md, odw, 0.0); nd = nd - md
        nan = lambda x: np.where(has, x, np.nan)
        new[f'rl{k}'] = nan(rl); new[f'rln{k}'] = nan(n_oth)
        new[f'fk{k}'] = nan(sr / (nn + 3.0)); new[f'fkd{k}'] = nan(sd / (nd + 3.0)); new[f'fkn{k}'] = nan(nn)
    w = np.array([0.5, 0.3, 0.2])
    for p in ('rl', 'fk'):
        M = np.column_stack([new[f'{p}{k}'] for k in (1, 2, 3)]); ok = ~np.isnan(M)
        den = (ok * w).sum(axis=1)
        new[f'{p}_w'] = np.where(den > 0, (np.nan_to_num(M) * w).sum(axis=1) / np.where(den > 0, den, 1), np.nan)
    return pd.concat([df, pd.DataFrame(new, index=df.index)], axis=1)


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
    Rr = df[[f'r{k}' for k in range(1, 9)]]
    df['m8'], df['max8'] = Rr.mean(axis=1), Rr.max(axis=1)
    return C.add_field_rel(df, DIRF_BASE + ['weightCarried', 'barr_f'])


LFLD = ['lfv1', 'lfv2', 'lfv3', 'lkf1', 'lkf2', 'lkf3']


def add_lfld(df):
    """strength of the horse's last three fields: its formula figure against the other runners' (and its rank in the field) at each of those runs."""
    df = df.copy()
    o = df.sort_values(['horse_id', 'date']); g = o.groupby('horse_id')
    for k in (1, 2, 3):
        df[f'lfv{k}'] = g.f_vs_fld.shift(k).reindex(df.index); df[f'lkf{k}'] = g.k_f.shift(k).reindex(df.index)
    return df


if want('lfld', 'allz'):
    cv, pg = add_lfld(cv), add_lfld(pg); log('last-field strength done')
if want('ped', 'allx', 'allz'):
    cv, pg = add_ped(cv), add_ped(pg); log('pedigree done')
if want('dirf', 'allx', 'allz'):
    cv, pg = add_dirf(cv), add_dirf(pg); log('finishing-position inputs done')
if want('tfu', 'allx', 'allz'):
    cv, pg = add_tfu(cv), add_tfu(pg); log('trainer patterns done')
if want('jsw', 'allx'):
    cv, pg = add_jsw(cv), add_jsw(pg); log('jockey switch done')
if want('frank', 'allx', 'allz'):
    FR = build_frank()
    cv, pg = add_frank(cv, FR), add_frank(pg, FR); log('collateral form done')
    for nm, d in (('converted', cv), ('page', pg)):
        print(nm, 'collateral coverage:', {c: round(float(d[c].notna().mean()), 3) for c in ('rl1', 'fk1', 'rl3')}, 'mean rivals run since (last race)', round(float(d.fkn1.mean()), 2), flush=True)

FR_BASE = ['n', 'ldays', 'std4', 'max4', 'c_max', 'c_mean', 'sim_dist', 'sim_going', 'h_dist', 'wt_chg', 'dist_chg', 'trk_n', 'pair_n', 'style', 'dist_from_best', 'going_best_gap', 'tr_trel']
FRM = [p_ + c for c in FR_BASE for p_ in ('r_', 'k_')]
if want('frm', 'allz'):
    cv, pg = C.add_field_rel(cv, FR_BASE), C.add_field_rel(pg, FR_BASE); log('more field-relative inputs done')

classes = sorted(pg.cls.dropna().unique().tolist())
for d in (cv, pg):
    d['cls_c'] = C._cls(d.cls, classes)
    d['rk'] = C._race_key(d)
pa = pd.concat([cv[cv.date < CUT], pg[pg.date < CUT]], ignore_index=True)
tr, va = pa[pa.date < ES], pa[(pa.date >= ES) & (pa.date < CUT)]
tests = {'pg': pg[pg.date >= CUT].copy(), 'cv': cv[cv.date >= CUT].copy()}
log('train', len(tr), 'valid', len(va), 'tests', {k: len(v) for k, v in tests.items()})

F0 = C.FEATS2 + C.TRIAL_FEATS
F1 = C.FEATS2 + C.REL_FEATS2 + C.FIT_FEATS + C.TRIAL_FEATS
ADD = {'lfld': LFLD, 'frm': FRM, 'ped': PED, 'dirf': DIRF, 'tfu': TFU, 'jsw': JSW, 'frank': FRK, 'allx': PED + DIRF + TFU + JSW + FRK, 'allz': PED + DIRF + TFU + FRK + LFLD + FRM}
P06 = dict(learning_rate=0.06, n_estimators=10000)
PAR = {'base': dict(learning_rate=0.03, n_estimators=4000), 'long': dict(learning_rate=0.03, n_estimators=16000),
       'big': dict(learning_rate=0.05, n_estimators=8000, num_leaves=127, min_child_samples=200),
       'deep': dict(learning_rate=0.05, n_estimators=6000, num_leaves=255, min_child_samples=400, colsample_bytree=0.6),
       'cs5': dict(P06, colsample_bytree=0.5), 'small': dict(P06, num_leaves=15, n_estimators=16000), 'reg': dict(P06, reg_lambda=30, min_child_samples=300),
       'hub25': dict(P06, alpha=2.5), 'hub8': dict(P06, alpha=8.0), 'l2': dict(P06, objective='regression'), 'xt': dict(P06, extra_trees=True),
       'lin': dict(P06, linear_tree=True, linear_lambda=1.0)}
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]

out = {k: t[['horse_id', 'date', 'wpr', 'positionFinish', 'n', 'd_last', 'field_size', 'vn', 'distance', 'cls']].copy() for k, t in tests.items()}
for k, t in out.items():
    t['f'] = tests[k].f.values
info = {}
for full, seed in JOBS:
    name, _, flags = full.partition('.')
    is_rdm, is_cat = (name == 'rdm' or 'R' in flags), (name == 'cat' or 'C' in flags)
    A, B = F0 + ADD.get(name, []), F1 + ADD.get(name, [])
    P = dict(num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0, random_state=seed)
    P.update(PAR.get(name, P06))
    P['n_estimators'] = max(20, int(P['n_estimators'] * a.tree_scale))
    t0, v0, ycol = tr, va, 'resid'
    wfn = None
    if name == 'wrec':
        wfn = lambda d: np.exp(-(CUT - d.date).dt.days.values / 1095.0)
    if name == 'wpg':
        wfn = lambda d: np.where(d.src == 'pg', 3.0, 1.0)
    if name == 'cshort':       # value of the newest converted rows: drop those after 2025-03-31 from the fit
        t0 = tr[(tr.src == 'pg') | (tr.date <= '2025-03-31')]
    if name == 'nopg':         # converted rows only (complete fields), no runner-page training rows
        t0, v0 = tr[tr.src == 'cv'], va[va.src == 'cv']
    if is_rdm:
        t0, v0 = t0.copy(), v0.copy()
        for d in (t0, v0):
            g = d.groupby('rk').resid
            d['resid_dm'] = (d.resid - g.transform('mean')).where(g.transform('size') >= 4)
        t0, v0, ycol = t0[t0.resid_dm.notna()], v0[v0.resid_dm.notna()], 'resid_dm'

    def fit(Fs, t, v):
        if is_cat:
            from catboost import CatBoostRegressor
            X = lambda d: d[Fs].assign(cls_c=d.cls_c.cat.codes.astype(float)) if 'cls_c' in Fs else d[Fs]
            m = CatBoostRegressor(loss_function='Huber:delta=4', eval_metric='Huber:delta=4', iterations=max(20, int(8000 * a.tree_scale)), learning_rate=0.06, depth=8, l2_leaf_reg=5,
                                  random_seed=seed, thread_count=4, od_type='Iter', od_wait=150, verbose=500)
            m.fit(X(t), t[ycol], eval_set=(X(v), v[ycol]), use_best_model=True)
            return (lambda d: m.predict(X(d))), int(m.get_best_iteration() or 0), None
        m = lgb.LGBMRegressor(**P).fit(t[Fs], t[ycol], sample_weight=None if wfn is None else wfn(t), eval_set=[(v[Fs], v[ycol])], callbacks=[lgb.early_stopping(150, verbose=False)])
        return (lambda d: m.predict(d[Fs])), int(m.best_iteration_), pd.Series(m.booster_.feature_importance('gain'), index=Fs)

    p0, b0, _ = fit(A, t0, v0); log(full, seed, 'plain model trees', b0)
    one = name == 'one'        # one model with the relevance inputs for every horse
    p1, b1, imp = fit(B, t0 if one else rel(t0), v0 if one else rel(v0)); log(full, seed, 'relevance model trees', b1)
    col = f'{full}_s{seed}'
    for k, te in tests.items():
        use = (te.n >= C.REL_MIN_RUNS).values
        c = p1(te) if one else p0(te)
        if not one:
            c[use] = p1(te.loc[use])
        if not is_rdm and name != 'nocap' and 'N' not in flags:     # 'nocap' = lr06 without the cap for horses with under 3 runs (the combine step re-applies caps of 3 to 8)
            c = np.where(use, c, np.clip(c, -2, 2))           # run.py CTX_CAP_FEW for under 3 runs
        out[k][col] = te.f.values + c
    newf = [x for x in B if x not in F1]
    info[col] = dict(trees=b1, trees_plain=b0, cap=int(P['n_estimators']),
                     new_share=round(float(imp[newf].sum() / imp.sum()), 4) if (newf and imp is not None) else 0.0,
                     top_new={x: round(float(v), 4) for x, v in (imp[newf] / imp.sum()).sort_values(ascending=False).head(10).items()} if (newf and imp is not None) else {})
    print(col, info[col], flush=True)
os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
for k, t in out.items():
    t.to_pickle(f'{a.out}_{k}.pkl')
json.dump(info, open(f'{a.out}_info.json', 'w'), indent=1)
log('done')
