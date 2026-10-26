"""Direct finishing-position model v4 (26 Oct 2026): race shape, pace, settling and today's conditions, tested properly.
Question: does race shape / pace / settling / track conditions close the gap to the market? v3 used only crude shape history. Here:
  F1  stage-1 PREDICTED early position for today (gap behind the leader and position fraction at 800m, out-of-fold by half-year block, time-forward)
  F2  field pace pressure built from those predictions (likely leaders, lone speed, crowding, who is blocked or has cover, wide and forward, back and inside, predicted tempo)
  F3  today's conditions: rail, going, grading, as-of front / back bias by track x distance (x rail, x wet), draw by rail, with interactions
  F4  meeting-day lean from the EARLIER races at the same meeting, draw based (can be built live from TAB finishing order)
  F5  meeting-day lean, leader based (needs 800m positions of earlier races: NOT available live outside VIC/SA GPS)
  F6  horse sensitivities, as-of: rating residual when the race was hot / slow, as a front-runner / backmarker in each, wide / inside draws
  F7  early-speed history (race-demeaned early sectional) and the field's early-speed pressure
  F8  ORACLE (post-race): realised 800m position, gap, tempo, leaders. Upper bound of what shape could add, not usable.
Each family is added alone to the V3a control (ctx/relevance/speed inputs), then cumulatively; paired winner log-lik gain with se, top pick, value read against the
closing price, and gain in subgroups (sprint / middle / staying, wet, big fields, hot pace, lone speed).
  PYTHONPATH=.:projection:research python research/direct_shape_v4.py     (needs /tmp/direct_ctx_feats.pkl from direct_ctx_features.py)
"""
import os, sys, re, glob, time
import numpy as np, pandas as pd
import lightgbm as lgb

DEBUG = os.environ.get('V4_DEBUG') == '1'
HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, 'direct_finish_v3.py')).read()
i1, i2, i3 = src.index('MODELS = {}'), src.index('def cond_logit'), src.index('price_gain(te, P1')
exec(compile(src[:i1], 'v3_prep', 'exec'))
exec(compile(src[i2:i3], 'v3_eval', 'exec'))
T0 = time.time()


def log(*a):
    print(f'[{(time.time() - T0) / 60:5.1f}m]', *a, flush=True)


# ------------------------------------------------------------------ raw extras for the shape tables
extra = ['race_id', 'horse_id', 'meeting_id', 'raceNumber', 'rail_position', 'trackGrading', 'margin800m', 'raceShapeEarly', 'sect_i_early']
ex = pd.concat([pd.read_csv(f, usecols=lambda c: c in extra, low_memory=False) for f in fs], ignore_index=True)
ex['horse_id'] = pd.to_numeric(ex.horse_id, errors='coerce').astype(float)
ex = ex.drop_duplicates(['race_id', 'horse_id'])
S = r.merge(ex, on=['race_id', 'horse_id'], how='left')
assert len(S) == len(r)
S = S.reset_index(drop=True)
S['nr'] = S.groupby('race_id').horse_id.transform('size')
S['g0'] = pd.to_numeric(S.margin800m, errors='coerce').clip(0, 20)
S['e0'] = pd.to_numeric(S.position800m, errors='coerce') / S.nr
S['es'] = pd.to_numeric(S.sect_i_early, errors='coerce')
S['es'] = S.es - S.groupby('race_id').es.transform('max')
S['tp'] = pd.to_numeric(S.raceShapeEarly, errors='coerce')


def rail_num(x):
    if not isinstance(x, str):
        return np.nan
    m = re.search(r'([+-]?\d+(?:\.\d+)?)\s*m', x)
    if not m:
        return 0.0
    v = float(m.group(1))
    return v if not x.lower().startswith('out') else abs(v)


S['rail_m'] = S.rail_position.map(rail_num)
S['rail_b'] = S.rail_m.fillna(-1).clip(-1, 8).round()
S['grade'] = pd.Categorical(S.trackGrading.astype(str)).codes.astype(float)
S['vcode'] = pd.Categorical(S.vk.astype(str)).codes.astype(float)
S['wet'] = (S.gs >= 5).astype(float).where(S.gs.notna())
gS = S.groupby('horse_id')


def lagmat(col, K):
    return np.column_stack([gS[col].shift(k).values for k in range(1, K + 1)])


NEW = {}
E8, D8, G8, ES8 = lagmat('e0', 8), lagmat('distance', 8), lagmat('g0', 8), lagmat('es', 8)
with np.errstate(all='ignore'):
    NEW['e_m4'] = np.nanmean(E8[:, :4], 1)
    NEW['e_l1'] = E8[:, 0]
    NEW['e_min4'] = np.nanmin(np.where(np.isnan(E8[:, :4]), np.inf, E8[:, :4]), 1)
    NEW['e_min4'][~np.isfinite(NEW['e_min4'])] = np.nan
    NEW['g_m4'] = np.nanmean(G8[:, :4], 1)
    NEW['g_l1'] = G8[:, 0]
    NEW['g_min4'] = np.nanmin(np.where(np.isnan(G8[:, :4]), np.inf, G8[:, :4]), 1)
    NEW['g_min4'][~np.isfinite(NEW['g_min4'])] = np.nan
    NEW['es_m4'] = np.nanmean(ES8[:, :4], 1)
    NEW['es_max4'] = np.nanmax(np.where(np.isnan(ES8[:, :4]), -np.inf, ES8[:, :4]), 1)
    NEW['es_max4'][~np.isfinite(NEW['es_max4'])] = np.nan
    near = np.abs(D8 - S.distance.values[:, None]) <= 200
    Ed = np.where(near, E8, np.nan)
    NEW['e_dist'] = np.nanmean(Ed, 1)
    NEW['g_dist'] = np.nanmean(np.where(near, G8, np.nan), 1)
    NEW['n_e'] = np.isfinite(E8[:, :8]).sum(1).astype(float)
for k, v in NEW.items():
    S[k] = v
S['n_runs'] = gS.cumcount().astype(float)
S['days'] = gS.date.diff().dt.days
S['jk_e'] = asof_rate(S, 'jk', 'e0', prior=0.5, k=30)
S['tk_e'] = asof_rate(S, 'tk', 'e0', prior=0.5, k=30)
S['dk_e'] = asof_rate(S, 'dk', 'e0', prior=0.5, k=100)
gR = S.groupby('race_id')
for c in ('e_m4', 'g_m4', 'es_m4'):
    S['r_' + c] = S[c] - gR[c].transform('mean')
    S['k_' + c] = gR[c].rank(pct=True)
S['race_min_e'] = gR.e_m4.transform('min')
log('history features done', len(S))

# ------------------------------------------------------------------ stage 1: predicted early position, out-of-fold by half-year block
ST1 = ['e_m4', 'e_l1', 'e_min4', 'g_m4', 'g_l1', 'g_min4', 'es_m4', 'es_max4', 'e_dist', 'g_dist', 'n_e', 'jk_e', 'tk_e', 'dk_e', 'barrier', 'barfrac', 'nr', 'distance', 'gs', 'rail_m',
       'vcode', 'n_runs', 'days', 'r_e_m4', 'k_e_m4', 'r_g_m4', 'r_es_m4', 'race_min_e']
P1 = dict(objective='regression', learning_rate=0.08, num_leaves=63, min_data_in_leaf=100, feature_fraction=0.8, bagging_fraction=0.7, bagging_freq=1, lambda_l2=5, verbose=-1, num_threads=0)
NR1 = 60 if DEBUG else 250
edges = list(pd.date_range('2021-01-01', '2026-01-01', freq='6MS'))
S['pg'] = np.nan
S['pe'] = np.nan
for a, b in zip(edges[:-1], edges[1:]):
    trn = S[(S.date < a) & S.g0.notna() & S.e_m4.notna()]
    if len(trn) > 700_000:
        trn = trn.sample(700_000, random_state=1)
    blk = (S.date >= a) & (S.date < b)
    for tgt, outc in (('g0', 'pg'), ('e0', 'pe')):
        m = lgb.train(P1, lgb.Dataset(trn[ST1], trn[tgt], categorical_feature=['vcode']), NR1)
        S.loc[blk, outc] = m.predict(S.loc[blk, ST1])
    log('stage 1 block', a.date(), len(trn), 'train rows', int(blk.sum()), 'predicted')
S['pg'] = S.pg.clip(0, 20)
for yr in (2022, 2023, 2024, 2025):
    t = S[(S.date.dt.year == yr) & S.g0.notna() & S.pg.notna() & (S.nr >= 8)]
    dm = lambda c: t[c] - t.groupby('race_id')[c].transform('mean')
    log(f'stage 1 quality {yr}: within-race corr predicted gap vs realised {np.corrcoef(dm("pg"), dm("g0"))[0, 1]:.3f}  (simple past-gap baseline {np.corrcoef(dm("g_m4").fillna(0), dm("g0"))[0, 1]:.3f}), position fraction {np.corrcoef(dm("pe"), dm("e0").fillna(0))[0, 1]:.3f}')

# ------------------------------------------------------------------ F2 field pace pressure from predicted settle
gR = S.groupby('race_id')
S['pg_rank'] = gR.pg.rank(method='min')
S['pe_rank'] = gR.pe.rank(method='min')
S['pg_gap_ld'] = S.pg - gR.pg.transform('min')
S['pe_gap_ld'] = S.pe - gR.pe.transform('min')
for thr in (1.0, 2.0, 4.0):
    S[f'n_lead{int(thr)}'] = (S.pg < thr).groupby(S.race_id).transform('sum').astype(float)
srt = S.groupby('race_id').pg.apply(lambda s: np.sort(s.dropna().values))


def second_gap(rid):
    a = srt.get(rid)
    return a[1] - a[0] if a is not None and len(a) > 1 else np.nan


def top3mean(rid):
    a = srt.get(rid)
    return a[:3].mean() if a is not None and len(a) > 0 else np.nan


rid_u = srt.index
lone = pd.Series([second_gap(x) for x in rid_u], index=rid_u)
top3 = pd.Series([top3mean(x) for x in rid_u], index=rid_u)
S['lone'] = S.race_id.map(lone)
S['pg_top3'] = S.race_id.map(top3)
S['pg_mean'] = gR.pg.transform('mean')
S['pg_sd'] = gR.pg.transform('std')
S['hot'] = np.exp(-S.pg / 2).groupby(S.race_id).transform('sum')
S['my_share'] = np.exp(-S.pg / 2) / S.hot
S['lead_free'] = ((S.pg_rank == 1) & (S.lone > 1.5)).astype(float)
S['wide_fwd'] = ((S.pg < 2.5) & (S.barfrac > 0.66)).astype(float)
S['back_in'] = ((S.pg > 6) & (S.barfrac < 0.33)).astype(float)
# neighbours: others within 1.5 L; inside and ahead; outside and ahead
rows = []
for rid, grp in S[['race_id', 'pg', 'barrier']].groupby('race_id', sort=False):
    pg, br = grp.pg.values, grp.barrier.values
    if len(pg) < 2 or np.isnan(pg).all():
        rows.append(pd.DataFrame({'n_near': np.nan, 'in_ahead': np.nan, 'out_ahead': np.nan, 'n_behind_in': np.nan}, index=grp.index))
        continue
    dpg = pg[None, :] - pg[:, None]
    ahead = dpg < 0
    ahead_of_me = (pg[None, :] < pg[:, None])
    in_ = br[None, :] < br[:, None]
    n_near = (np.abs(dpg) <= 1.5).sum(1) - 1
    in_ahead = (ahead_of_me & in_).sum(1)
    out_ahead = (ahead_of_me & ~in_).sum(1)
    n_behind_in = ((pg[None, :] > pg[:, None]) & in_).sum(1)
    rows.append(pd.DataFrame({'n_near': n_near, 'in_ahead': in_ahead, 'out_ahead': out_ahead, 'n_behind_in': n_behind_in}, index=grp.index))
S = S.join(pd.concat(rows))
for c in ('n_near', 'in_ahead', 'out_ahead', 'n_behind_in'):
    S[c] = S[c].astype(float)
S['es_top3'] = S.groupby('race_id').es_m4.transform(lambda s: np.sort(s.dropna().values)[::-1][:3].mean() if s.notna().any() else np.nan)
S['n_fast_es'] = (S.es_m4 > -1.5).groupby(S.race_id).transform('sum').astype(float)
log('F2 field pressure done')

# predicted tempo (race level), out-of-fold by the same blocks
RT = S.groupby('race_id').agg(date=('date', 'first'), tp=('tp', 'first'), pg_top3=('pg_top3', 'first'), n_lead1=('n_lead1', 'first'), n_lead2=('n_lead2', 'first'), lone=('lone', 'first'),
                              pg_sd=('pg_sd', 'first'), pg_mean=('pg_mean', 'first'), es_top3=('es_top3', 'first'), n_fast_es=('n_fast_es', 'first'), nr=('nr', 'first'), distance=('distance', 'first'),
                              gs=('gs', 'first'), vcode=('vcode', 'first'), rail_m=('rail_m', 'first'), hot=('hot', 'first'))
TPF = [c for c in RT.columns if c not in ('date', 'tp')]
RT['pred_tp'] = np.nan
for a, b in zip(edges[:-1], edges[1:]):
    trn = RT[(RT.date < a) & RT.tp.notna() & RT.pg_top3.notna()]
    blk = (RT.date >= a) & (RT.date < b)
    if len(trn) < 500:
        continue
    m = lgb.train(dict(P1, num_leaves=31, min_data_in_leaf=50), lgb.Dataset(trn[TPF], trn.tp, categorical_feature=['vcode']), 80 if DEBUG else 200)
    RT.loc[blk, 'pred_tp'] = m.predict(RT.loc[blk, TPF])
ok = RT.tp.notna() & RT.pred_tp.notna() & (RT.date >= '2022-01-01')
log(f'predicted tempo: race-level corr with realised {np.corrcoef(RT.tp[ok], RT.pred_tp[ok])[0, 1]:.3f} over {int(ok.sum())} races')
S['pred_tp'] = S.race_id.map(RT.pred_tp)
TQ = S.loc[S.date < '2021-01-01', 'tp'].quantile([0.3, 0.5, 0.7]).values
S['tp_z'] = (S.pred_tp - TQ[1]) / S.loc[S.date < '2021-01-01', 'tp'].std()

# ------------------------------------------------------------------ F3 conditions, track bias by track x distance (x rail, x wet), draw by rail
S['fl'] = S.finpct
S['lead_fin'] = S.fl.where(S.e0 < 0.30)
S['back_fin'] = S.fl.where(S.e0 > 0.70)
S['dall_r'] = S.dall + '|r' + S.rail_b.astype(str)
S['dall_w'] = S.dall + '|w' + S.wet.fillna(-1).astype(str)
for tag, key in (('', 'dall'), ('_rail', 'dall_r'), ('_wet', 'dall_w')):
    base = asof_rate(S, key, 'fl', prior=0.5, k=100)
    S['front_bias' + tag] = asof_rate(S, key, 'lead_fin', prior=0.35, k=60) - base
    S['back_bias' + tag] = asof_rate(S, key, 'back_fin', prior=0.6, k=60) - base
S['dk_r'] = S.dk + '|r' + S.rail_b.astype(str)
S['draw_rail'] = asof_rate(S, 'dk_r', 'fl', prior=0.5, k=100) - asof_rate(S, 'dall_r', 'fl', prior=0.5, k=100)
S['fb_x_pe'] = S.front_bias_rail * (0.5 - S.pe)
S['bb_x_pe'] = S.back_bias_rail * (S.pe - 0.5)
S['draw_x_bar'] = S.draw_rail * (S.barfrac - 0.5)
S['rail_x_bar'] = S.rail_m * (S.barfrac - 0.5)
S['pe_x_wet'] = (S.pe - 0.5) * S.wet
log('F3 conditions done')

# ------------------------------------------------------------------ F4 / F5 meeting-day lean from EARLIER races of the same meeting
top4 = S[S.pos <= 4]
RM = S.groupby('race_id').agg(meeting=('meeting_id', 'first'), rn=('raceNumber', 'first'), date=('date', 'first'), nr=('nr', 'first'))
RM['dl'] = top4.groupby('race_id').barfrac.mean() - 0.5
RM['ll'] = S.groupby('race_id').e0.mean() - top4.groupby('race_id').e0.mean()
RM['wl'] = S.groupby('race_id').e0.mean() - S[S.pos == 1].groupby('race_id').e0.mean()
RM = RM[(RM.nr >= 8) | True].sort_values(['meeting', 'rn'])
ok8 = RM.nr >= 8
for c in ('dl', 'll', 'wl'):
    v = RM[c].where(ok8)
    cs = v.fillna(0).groupby(RM.meeting).cumsum() - v.fillna(0)
    cn = ok8.astype(float).groupby(RM.meeting).cumsum() - ok8.astype(float)
    RM['m_' + c] = cs / cn.replace(0, np.nan)
    if c == 'dl':
        RM['m_n'] = cn
S = S.merge(RM[['m_dl', 'm_ll', 'm_wl', 'm_n']], left_on='race_id', right_index=True, how='left')
S['lean_draw'] = S.m_dl.where(S.m_n >= 2)
S['lean_lead'] = S.m_ll.where(S.m_n >= 2)
S['lean_win'] = S.m_wl.where(S.m_n >= 2)
S['lean_draw_x'] = S.lean_draw * (S.barfrac - 0.5)
S['lean_lead_x'] = S.lean_lead * (S.pe - 0.5)
S['lean_draw_x_pe'] = S.lean_draw * (S.barfrac - 0.5) * (1 - 2 * S.pe)
S['lean_win_x'] = S.lean_win * (S.pe - 0.5)
log('F4/F5 meeting lean done')

# ------------------------------------------------------------------ F6 horse sensitivities (as-of rating residual by scenario)
S['q'] = S.wpr - S.groupby('race_id').wpr.transform('mean')
Q8 = np.column_stack([S.groupby('horse_id').q.shift(k).values for k in range(1, 9)])
with np.errstate(all='ignore'):
    S['resid'] = S.q - np.nanmean(Q8, 1)
hot = (S.tp >= TQ[2]) & S.tp.notna()
slow = (S.tp <= TQ[0]) & S.tp.notna()
front = S.e0 < 0.30
back = S.e0 > 0.60
conds = {'hot': hot, 'slow': slow, 'fh': front & hot, 'fs': front & slow, 'bh': back & hot, 'bs': back & slow, 'wide': S.barfrac > 0.66, 'inner': S.barfrac < 0.33, 'wet': S.wet == 1}
K = 4.0
for nm, mk in conds.items():
    v = S.resid.where(mk)
    cs = v.fillna(0).groupby(S.horse_id).cumsum() - v.fillna(0)
    cn = (v.notna().astype(float)).groupby(S.horse_id).cumsum() - v.notna().astype(float)
    S['s_' + nm] = cs / (cn + K)
    S['n_' + nm] = cn
S['s_hot_slow'] = S.s_hot - S.s_slow
S['s_tempo_today'] = S.tp_z * S.s_hot_slow
S['s_style_today'] = np.where(S.pg < 2.5, np.where(S.tp_z > 0, S.s_fh, S.s_fs), np.where(S.pg > 6, np.where(S.tp_z > 0, S.s_bh, S.s_bs), 0.0))
S['s_draw_today'] = np.where(S.barfrac > 0.66, S.s_wide, np.where(S.barfrac < 0.33, S.s_inner, 0.0))
log('F6 sensitivities done')

# ------------------------------------------------------------------ F8 oracle (realised shape)
S['o_nlead'] = (S.g0 < 1.0).groupby(S.race_id).transform('sum').astype(float)
S['o_lone'] = S.groupby('race_id').g0.transform(lambda s: np.sort(s.dropna().values)[1] - np.sort(s.dropna().values)[0] if s.notna().sum() > 1 else np.nan)
S['o_pe_rank'] = S.groupby('race_id').e0.rank(method='min')
ORACLE = ['e0', 'g0', 'es', 'tp', 'o_nlead', 'o_lone', 'o_pe_rank']

# ------------------------------------------------------------------ families
FAM = {
    'F1 predicted settle': ['pg', 'pe', 'pg_rank', 'pe_rank', 'pg_gap_ld', 'pe_gap_ld', 'e_m4', 'g_m4', 'e_dist', 'g_dist', 'jk_e', 'tk_e', 'dk_e'],
    'F2 field pressure': ['n_lead1', 'n_lead2', 'n_lead4', 'lone', 'pg_top3', 'pg_mean', 'pg_sd', 'hot', 'my_share', 'lead_free', 'wide_fwd', 'back_in', 'n_near', 'in_ahead', 'out_ahead',
                          'n_behind_in', 'pred_tp', 'tp_z'],
    'F3 conditions/bias': ['rail_m', 'grade', 'wet', 'front_bias', 'back_bias', 'front_bias_rail', 'back_bias_rail', 'front_bias_wet', 'back_bias_wet', 'draw_rail', 'fb_x_pe', 'bb_x_pe',
                           'draw_x_bar', 'rail_x_bar', 'pe_x_wet'],
    'F4 meeting lean (draw)': ['lean_draw', 'lean_draw_x', 'lean_draw_x_pe', 'm_n'],
    'F5 meeting lean (leaders)': ['lean_lead', 'lean_win', 'lean_lead_x', 'lean_win_x', 'm_n'],
    'F6 horse sensitivities': [c for c in S.columns if c.startswith('s_') or c.startswith('n_') and c.split('_', 1)[1] in conds] + ['s_hot_slow'],
    'F7 early speed': ['es_m4', 'es_max4', 'r_es_m4', 'k_es_m4', 'es_top3', 'n_fast_es'],
}
FAM = {k: list(dict.fromkeys(v)) for k, v in FAM.items()}
NEWCOLS = sorted(set(sum(FAM.values(), []) + ORACLE + ['r_e_m4', 'k_e_m4', 'r_g_m4', 'k_g_m4']) - set(V3A))
keep = ['race_id', 'horse_id'] + [c for c in NEWCOLS if c in S.columns]
N = S[keep].copy()
for c in N.columns[2:]:
    N[c] = N[c].astype('float32')
dup = [c for c in N.columns[2:] if c in tr.columns]
log('new columns', len(N.columns) - 2, 'already present', dup)


def attach(df):
    return df.drop(columns=dup).merge(N, on=['race_id', 'horse_id'], how='left')


tr, va, te = attach(tr), attach(va), attach(te)
for df in (tr, va, te):
    df['rk'] = df.race_id
# races where the stage-1 shape exists for the whole field
cover = te.groupby('race_id').pg.transform(lambda s: s.notna().all())
log(f'test races with predicted settle for the whole field: {te[cover].race_id.nunique()} of {te.race_id.nunique()}')

# ------------------------------------------------------------------ models
RUNS = {'A0 control (V3a)': V3A}
for k, cols in FAM.items():
    RUNS['+ ' + k] = V3A + [c for c in cols if c in tr.columns and c not in V3A]
LIVE_FAM = ['F1 predicted settle', 'F2 field pressure', 'F3 conditions/bias', 'F4 meeting lean (draw)', 'F6 horse sensitivities', 'F7 early speed']
cum = list(V3A)
for k in LIVE_FAM:
    cum += [c for c in FAM[k] if c in tr.columns and c not in cum]
    RUNS['cum to ' + k.split()[0]] = list(cum)
allf = list(cum) + [c for c in FAM['F5 meeting lean (leaders)'] if c in tr.columns and c not in cum]
RUNS['all live + F5'] = allf
RUNS['ORACLE all + realised shape'] = allf + [c for c in ORACLE if c in tr.columns]
if DEBUG:
    RUNS = {k: RUNS[k] for k in list(RUNS)[:2]}
MOD, LLs, PR = {}, {}, {}
for name, fl in RUNS.items():
    fl = list(dict.fromkeys(fl))
    m, T = train_b3(fl)
    MOD[name] = (m, T, fl)
    PR[name] = softmax(te, m.predict(te[fl]), T, 'rk')
    log(f'{name}: {len(fl)} inputs, {m.best_iteration} trees')
    LLs[name] = metrics(te, PR[name], name)
print('\nPaired winner log-lik gain over the A0 control (2025 test, all test races):')
base = LLs['A0 control (V3a)']
for name in list(RUNS)[1:]:
    df = LLs[name] - base
    print(f'   {name:34s} {df.mean():+.4f} (se {df.std() / np.sqrt(len(df)):.4f})')

print('\nSame, restricted to test races where the whole field has predicted settle:')
cv = te[cover].race_id.unique()
for name in list(RUNS)[1:]:
    df = (LLs[name] - base)[lambda s: s.index.isin(cv)]
    print(f'   {name:34s} {df.mean():+.4f} (se {df.std() / np.sqrt(len(df)):.4f}) over {len(df)} races')

price_gain(te, PR, te.priceStarting, 'T1 2025 closing price (shape families)')

# ------------------------------------------------------------------ subgroups for the best live variant
best = max([n for n in RUNS if n.startswith('cum to') or n.startswith('all live')], key=lambda n: (LLs[n] - base).mean())
print(f'\nBest live variant by overall gain: {best}')
rc = te.groupby('race_id').agg(dist=('distance', 'first'), gs=('gs', 'first'), nr=('nr', 'first'), nl=('n_lead1', 'first'), lone=('lone', 'first'), wf=('wide_fwd', 'sum'), lead_free=('lead_free', 'sum'))
SUB = {
    'sprint (<=1300m)': rc.dist <= 1300, 'middle (1400-1700m)': (rc.dist > 1300) & (rc.dist <= 1700), 'staying (>=1800m)': rc.dist >= 1800,
    'wet (going 5+)': rc.gs >= 5, 'dry (going <5)': rc.gs < 5, 'field 12+': rc.nr >= 12, 'field 8-11': (rc.nr >= 8) & (rc.nr < 12), 'field <8': rc.nr < 8,
    'hot pace (3+ predicted leaders)': rc.nl >= 3, 'no predicted leader (0)': rc.nl == 0, 'lone speed (gap to 2nd > 2L)': rc.lone > 2, 'wide-forward runner present': rc.wf > 0,
}
dd = LLs[best] - base
for lab, msk in SUB.items():
    idx = rc.index[msk.values]
    s = dd[dd.index.isin(idx)]
    if len(s) > 100:
        print(f'   {lab:34s} {s.mean():+.4f} (se {s.std() / np.sqrt(len(s)):.4f}) over {len(s)} races')
mb, Tb, flb = MOD[best]
imp = pd.Series(mb.feature_importance('gain'), index=flb).sort_values(ascending=False)
print('top inputs by gain:', ', '.join(f'{k} {v / imp.sum():.1%}' for k, v in imp.head(25).items()))
for k, cols in FAM.items():
    print(f'   share of gain, {k}: {imp[[c for c in imp.index if c in set(cols) and c not in V3A]].sum() / imp.sum():.1%}')
log('done')
