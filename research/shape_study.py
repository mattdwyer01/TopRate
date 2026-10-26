"""Race shape prediction study (26 Oct 2026). Goal: predict, before the race, how it will be run: each runner's position and gap at 800m, who leads,
the early pace. Trained and scored time-forward (half-year blocks, train on everything earlier) on the results files 2016-2026, test blocks 2025-01 on.
Targets (realised, from the results files): e0 = position at 800m / field size, g0 = lengths behind the leader at 800m (0 to 20), lead = leading at 800m.
Metrics (races with every runner's 800m position known, 6+ runners): within-race Spearman of prediction with e0, top-1 leader accuracy, leader in predicted
top 3, AUC of lead, MAE of g0 (lengths), and race-level correlation for tempo. Variants add families of inputs / change the learner:
  V0 baseline (v4 stage 1)          V1 + gear, pair, class, age, weight, days, spell      V2 + residual-style lags (position net of draw), contexts of lags
  V3 + latent effects (ridge: horse / jockey / trainer / track-barrier)                   V4 + field competition features
  V5 lambdarank on position       V6 g0 Huber       V7 softmax leader (custom)       V8 rank ensemble of V4 + V5 + V6 + V7
  V9 + GPS early speed history (ATC, racing.com, RQ)     V10 + legacy sectional history     V11 + trainer-at-track, jockey-at-track, trainer x distance
  V12 = V8 learners on the union of all inputs (everything)
Run:  PYTHONPATH=.:projection:research python research/shape_study.py --variants V0,V1 [--debug]
"""
import argparse, glob, os, re, sys, time, json
import numpy as np, pandas as pd
import lightgbm as lgb
from scipy.stats import spearmanr
from sklearn.metrics import roc_auc_score

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
T0 = time.time()


def log(*a):
    print(f'[{(time.time() - T0) / 60:6.1f}m]', *a, flush=True)


ap = argparse.ArgumentParser()
ap.add_argument('--variants', default='V0')
ap.add_argument('--debug', action='store_true')
ap.add_argument('--seeds', type=int, default=1)
ap.add_argument('--out', default='/tmp/shape_out')
ARGS, _ = ap.parse_known_args()
DEBUG = ARGS.debug
os.makedirs(ARGS.out, exist_ok=True)

# ------------------------------------------------------------------ load
COLS = ['race_id', 'meeting_id', 'date', 'horse_id', 'horse', 'barrier', 'distance', 'going', 'rail_position', 'trackGrading', 'venue', 'track', 'jockey', 'trainer',
        'weightCarried', 'race_class', 'horse_age', 'horse_sex', 'blinkers_on', 'gear_changes', 'is_letup', 'is_spell', 'isBarrierTrial', 'is_jumpout', 'position800m', 'margin800m',
        'sect_i_early', 'sect_ld_early', 'sect_i_to600', 'sect_i_l600', 'sect_i_l400', 'raceShapeEarly', 'positionFinish', 'marginFinish', 'priceStarting', 'wpr']
yrs = range(2022 if DEBUG else 2016, 2027)
S = pd.concat([pd.read_csv(os.path.join(ROOT, f'race_results_{y}.csv.gz'), usecols=lambda c: c in COLS, low_memory=False) for y in yrs], ignore_index=True)
S = S[~S.isBarrierTrial.astype(bool) & ~S.is_jumpout.fillna(False).astype(bool)].copy()
S['date'] = pd.to_datetime(S.date)
S['horse_id'] = pd.to_numeric(S.horse_id, errors='coerce').astype(float)
S = S.drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
S['nr'] = S.groupby('race_id').horse_id.transform('size')
S['pos800'] = pd.to_numeric(S.position800m, errors='coerce')
S['e0'] = S.pos800 / S.nr
S['g0'] = pd.to_numeric(S.margin800m, errors='coerce').clip(0, 20)
S['lead'] = np.where(S.pos800.notna(), (S.pos800 == 1).astype(float), np.nan)
S['es'] = pd.to_numeric(S.sect_i_early, errors='coerce')
S['es'] = S.es - S.groupby('race_id').es.transform('max')
S['tp'] = pd.to_numeric(S.raceShapeEarly, errors='coerce')
S['pos'] = pd.to_numeric(S.positionFinish, errors='coerce')
S['finpct'] = (S.pos - 1) / (S.nr - 1)
S['barfrac'] = (S.barrier - 1) / (S.nr - 1)
S['gs'] = pd.to_numeric(S.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
S['wet'] = (S.gs >= 5).astype(float).where(S.gs.notna())


def rail_num(x):
    if not isinstance(x, str):
        return np.nan
    m = re.search(r'([+-]?\d+(?:\.\d+)?)\s*m', x)
    return 0.0 if not m else float(m.group(1))


S['rail_m'] = S.rail_position.map(rail_num)
S['rail_b'] = S.rail_m.fillna(-1).clip(-1, 8).round()
S['grade'] = pd.Categorical(S.trackGrading.astype(str)).codes.astype(float)
SPONSOR = re.compile(r'\b(sportsbet|bet365|ladbrokes|tab|picklebet|aquis|ladbrokes|neds|pointsbet|bluebet|unibet|bet|park|racecourse|synthetic|poly|track)\b')
S['vk'] = S.venue.astype(str).str.lower().map(lambda x: re.sub(r'[^a-z]', '', SPONSOR.sub('', x)))
S['vcode'] = pd.Categorical(S.vk).codes.astype(float)
S['dband'] = (S.distance / 200).round()
S['dall'] = S.vk + '|' + S.dband.astype(str)
S['third'] = np.minimum((S.barfrac * 3).fillna(1).astype(int), 2)
S['bq'] = np.minimum((S.barfrac * 5).fillna(2).astype(int), 4)
S['dk'] = S.dall + '|' + S.bq.astype(str)
S['dkr'] = S.dk + '|r' + S.rail_b.astype(str)
S['hname'] = S.horse.astype(str).str.lower().str.replace(r'[^a-z]', '', regex=True)
SEX = {'G': 0, 'M': 1, 'F': 2, 'C': 3, 'H': 4, 'R': 5}
S['sex'] = S.horse_sex.astype(str).str.upper().str[:1].map(SEX)
S['clsc'] = pd.Categorical(S.race_class.astype(str)).codes.astype(float)


def nk(x):
    if not isinstance(x, str):
        return None
    t = re.sub(r"[^A-Za-z\s'-]", '', x).split()
    return (t[0][0] + t[-1]).lower().replace("'", '').replace('-', '') if t else None


S['jk'], S['tk'] = S.jockey.map(nk), S.trainer.map(nk)
# race order within a meeting: race_id rises with the race number (raceNumber is blank in the files)
rr = S.drop_duplicates('race_id')[['race_id', 'meeting_id']].sort_values(['meeting_id', 'race_id'])
rr['rn'] = rr.groupby('meeting_id').cumcount() + 1
S = S.merge(rr[['race_id', 'rn']], on='race_id', how='left')
log('loaded', len(S), 'runs', S.race_id.nunique(), 'races', S.date.min().date(), S.date.max().date())


def asof_rate(df, key, value, window_days=None, prior=0.5, k=50):
    v = df[value]
    t = pd.DataFrame({'key': df[key].values, 'date': df.date.values, 'v': v.values}).dropna(subset=['key', 'v'])
    a = t.groupby(['key', 'date']).v.agg(['sum', 'count']).reset_index().sort_values(['key', 'date'])
    a['cs'] = a.groupby('key')['sum'].cumsum()
    a['cn'] = a.groupby('key')['count'].cumsum()
    q = pd.DataFrame({'key': df[key].values, 'date': df.date.values, '_i': np.arange(len(df))}).dropna(subset=['key'])
    m = pd.merge_asof(q.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
    cs, cn = m.cs.fillna(0).values, m.cn.fillna(0).values
    if window_days:
        q2 = q.assign(date=q.date - pd.Timedelta(days=window_days))
        m2 = pd.merge_asof(q2.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
        cs, cn = cs - m2.cs.fillna(0).values, cn - m2.cn.fillna(0).values
    out = np.full(len(df), np.nan)
    out[m._i.values] = (cs + prior * k) / (cn + k)
    return out


# ------------------------------------------------------------------ base history features (V0)
F = {}
gS = S.groupby('horse_id')
S['dk_e'] = asof_rate(S, 'dk', 'e0', prior=0.5, k=100)
S['dall_e'] = asof_rate(S, 'dall', 'e0', prior=0.5, k=100)
S['res0'] = S.e0 - S.dk_e          # position net of the draw's usual effect at this track and distance
S['resg'] = S.g0 - asof_rate(S, 'dk', 'g0', prior=4.0, k=100)


def lagmat(col, K):
    return np.column_stack([S.groupby('horse_id')[col].shift(k).values for k in range(1, K + 1)])


L = {c: lagmat(c, 8) for c in ('e0', 'g0', 'es', 'res0', 'resg', 'distance', 'nr', 'barfrac', 'lead')}
with np.errstate(all='ignore'):
    def nm(a, n):
        return np.nanmean(a[:, :n], 1)

    def nmin(a, n):
        r = np.nanmin(np.where(np.isnan(a[:, :n]), np.inf, a[:, :n]), 1)
        r[~np.isfinite(r)] = np.nan
        return r
    F['e_m4'] = nm(L['e0'], 4); F['e_l1'] = L['e0'][:, 0]; F['e_min4'] = nmin(L['e0'], 4); F['e_m8'] = nm(L['e0'], 8)
    F['g_m4'] = nm(L['g0'], 4); F['g_l1'] = L['g0'][:, 0]; F['g_min4'] = nmin(L['g0'], 4)
    F['es_m4'] = nm(L['es'], 4)
    near = np.abs(L['distance'] - S.distance.values[:, None]) <= 200
    F['e_dist'] = np.nanmean(np.where(near, L['e0'], np.nan), 1)
    F['g_dist'] = np.nanmean(np.where(near, L['g0'], np.nan), 1)
    F['n_e'] = np.isfinite(L['e0']).sum(1).astype(float)
    F['res_m4'] = nm(L['res0'], 4); F['res_l1'] = L['res0'][:, 0]; F['res_m8'] = nm(L['res0'], 8)
    F['resg_m4'] = nm(L['resg'], 4)
    F['lead_r4'] = nm(L['lead'], 4); F['lead_r8'] = nm(L['lead'], 8)
    w = np.array([0.4, 0.25, 0.15, 0.1, 0.05, 0.03, 0.01, 0.01])[None, :]
    ok = np.isfinite(L['res0'])
    F['res_ewm'] = np.nansum(np.where(ok, L['res0'], 0) * w, 1) / np.maximum((ok * w).sum(1), 1e-9)
    F['res_ewm'][ok.sum(1) == 0] = np.nan
    F['res_sd8'] = np.nanstd(L['res0'], 1)
F = pd.DataFrame(F, index=S.index)
S = pd.concat([S, F], axis=1)
S['n_runs'] = S.groupby('horse_id').cumcount().astype(float)
S['days'] = S.groupby('horse_id').date.diff().dt.days
S['jk_e'] = asof_rate(S, 'jk', 'e0'); S['tk_e'] = asof_rate(S, 'tk', 'e0')
gR = S.groupby('race_id')
for c in ('e_m4', 'g_m4', 'es_m4', 'res_m4', 'res_ewm', 'lead_r4'):
    S['r_' + c] = S[c] - gR[c].transform('mean')
    S['k_' + c] = gR[c].rank(pct=True)
S['race_min_e'] = gR.e_m4.transform('min')
S['race_min_res'] = gR.res_m4.transform('min')
log('base history features done')

# ------------------------------------------------------------------ V1 extras: gear, pairing, class, age, weight, days, spell
S['blink'] = S.blinkers_on.map({True: 1.0, False: 0.0, 'True': 1.0, 'False': 0.0})
S['blink_prev'] = S.groupby('horse_id').blink.shift(1)
S['blink_first'] = ((S.blink == 1) & (S.blink_prev == 0)).astype(float).where(S.blink.notna() & S.blink_prev.notna())
S['gear_n'] = S.gear_changes.map(lambda x: np.nan if not isinstance(x, str) else (0.0 if x in ('[]', 'None', '') else float(x.count(',') + 1)))
S['wchg'] = S.weightCarried - S.groupby('horse_id').weightCarried.shift(1)
S['dchg'] = S.distance - S.groupby('horse_id').distance.shift(1)
S['jk_prev'] = S.groupby('horse_id').jk.shift(1)
S['jk_same'] = (S.jk == S.jk_prev).astype(float).where(S.jk_prev.notna() & S.jk.notna())
S['pair'] = S.horse_id.astype(str) + '|' + S.jk.astype(str)
S['pair_res'] = asof_rate(S, 'pair', 'res0', prior=0.0, k=2)
S['pair_n'] = S.groupby('pair').cumcount().astype(float)
S['letup'] = S.is_letup.map({True: 1.0, False: 0.0, 'True': 1.0, 'False': 0.0})
S['spell'] = S.is_spell.map({True: 1.0, False: 0.0, 'True': 1.0, 'False': 0.0})
S['age'] = pd.to_numeric(S.horse_age, errors='coerce')
S['jk_res'] = asof_rate(S, 'jk', 'res0', prior=0.0, k=30)
S['tk_res'] = asof_rate(S, 'tk', 'res0', prior=0.0, k=30)
S['jk_res90'] = asof_rate(S, 'jk', 'res0', window_days=90, prior=0.0, k=15)
S['tk_res90'] = asof_rate(S, 'tk', 'res0', window_days=90, prior=0.0, k=15)
S['r_jk_res'] = S.jk_res - S.groupby('race_id').jk_res.transform('mean')
S['r_tk_res'] = S.tk_res - S.groupby('race_id').tk_res.transform('mean')

# ------------------------------------------------------------------ V2 extras: contexts of the last runs (what those positions were up against)
S['ctx_nr1'] = L['nr'][:, 0]; S['ctx_bf1'] = L['barfrac'][:, 0]; S['ctx_dd1'] = L['distance'][:, 0] - S.distance
S['ctx_nr2'] = L['nr'][:, 1]; S['ctx_bf2'] = L['barfrac'][:, 1]
S['e_l2'] = L['e0'][:, 1]; S['e_l3'] = L['e0'][:, 2]; S['g_l2'] = L['g0'][:, 1]; S['res_l2'] = L['res0'][:, 1]; S['res_l3'] = L['res0'][:, 2]
S['dkr_e'] = asof_rate(S, 'dkr', 'e0', prior=0.5, k=100) - S.dk_e      # rail effect on top of the draw effect
S['dall_g'] = asof_rate(S, 'dall', 'g0', prior=4.0, k=100)
S['dk_g'] = asof_rate(S, 'dk', 'g0', prior=4.0, k=100)
S['dk_lead'] = asof_rate(S, 'dk', 'lead', prior=0.1, k=100)
S['dall_lead'] = asof_rate(S, 'dall', 'lead', prior=0.1, k=100)

# ------------------------------------------------------------------ V11 extras: trainer / jockey at the track, trainer x distance band
S['tkv'] = S.tk.astype(str) + '|' + S.vk
S['jkv'] = S.jk.astype(str) + '|' + S.vk
S['tkd'] = S.tk.astype(str) + '|' + S.dband.astype(str)
S['tkv_res'] = asof_rate(S, 'tkv', 'res0', prior=0.0, k=20)
S['jkv_res'] = asof_rate(S, 'jkv', 'res0', prior=0.0, k=20)
S['tkd_res'] = asof_rate(S, 'tkd', 'res0', prior=0.0, k=20)
S['jk_dband_res'] = asof_rate(S.assign(k2=S.jk.astype(str) + '|' + S.dband.astype(str)), 'k2', 'res0', prior=0.0, k=20)
log('V1/V2/V11 extras done')

# ------------------------------------------------------------------ V10 legacy sectional history (as-of; blank for upcoming runs from 9 Oct 2026 on racing.com results)
for c in ('sect_i_to600', 'sect_i_l600', 'sect_i_l400'):
    S[c] = pd.to_numeric(S[c], errors='coerce')
S['to600_rel'] = S.sect_i_to600 - S.groupby('race_id').sect_i_to600.transform('max')
S['ldr_early'] = pd.to_numeric(S.sect_ld_early, errors='coerce')
S['to600_m4'] = np.nanmean(lagmat('to600_rel', 4), 1)
S['l600_m4'] = np.nanmean(lagmat('sect_i_l600', 4), 1)
S['es_max4'] = np.nanmax(np.where(np.isnan(L['es'][:, :4]), -np.inf, L['es'][:, :4]), 1)
S.loc[~np.isfinite(S.es_max4), 'es_max4'] = np.nan
S['r_to600_m4'] = S.to600_m4 - S.groupby('race_id').to600_m4.transform('mean')
S['k_to600_m4'] = S.groupby('race_id').to600_m4.rank(pct=True)

# ------------------------------------------------------------------ V9 GPS early-speed history (ATC NSW metro 2016+, racing.com VIC/SA 2021+, RQ), joined on date + horse name
gp = []
for f in glob.glob(os.path.join(ROOT, 'data', 'gps', 'rc_gps_runs_*.parquet')):
    g = pd.read_parquet(f)
    g['date'] = pd.to_datetime(g.start_utc.astype(str).str[:10])
    g['hname'] = g.horse.astype(str).str.lower().str.replace(r'[^a-z]', '', regex=True)
    g['gk'] = g.meet_code.astype(str) + '|' + g.race_no.astype(str)
    g['gps_early'] = pd.to_numeric(g.speed_early_ms, errors='coerce')
    g['gps_mid'] = pd.to_numeric(g.speed_mid_ms, errors='coerce')
    g['gps_rail'] = pd.to_numeric(g.rail_avg_m, errors='coerce')
    gp.append(g[['date', 'hname', 'gk', 'gps_early', 'gps_mid', 'gps_rail']])
for f in glob.glob(os.path.join(ROOT, 'data', 'gps', 'atc_gps_runs_*.parquet')):
    g = pd.read_parquet(f)
    g['date'] = pd.to_datetime(g.race_date)
    g['hname'] = g.horse.astype(str).str.lower().str.replace(r'[^a-z]', '', regex=True)
    g['gk'] = g.meet_code.astype(str) + '|' + g.race_no.astype(str)
    d4 = pd.to_numeric(g.distance, errors='coerce')
    g['gps_early'] = 400.0 / pd.to_numeric(g.first400_s, errors='coerce')
    g['gps_mid'] = np.nan
    g['gps_rail'] = np.nan
    gp.append(g[['date', 'hname', 'gk', 'gps_early', 'gps_mid', 'gps_rail']])
GP = pd.concat(gp, ignore_index=True).dropna(subset=['gps_early']).drop_duplicates(['date', 'hname'])
GP['gps_z'] = (GP.gps_early - GP.groupby('gk').gps_early.transform('mean')) / GP.groupby('gk').gps_early.transform('std').clip(lower=0.05)
S = S.merge(GP[['date', 'hname', 'gps_z']], on=['date', 'hname'], how='left')
S['gps_z_m3'] = np.nanmean(lagmat('gps_z', 3), 1)
S['gps_z_l1'] = S.groupby('horse_id').gps_z.shift(1)
S['gps_n'] = np.isfinite(lagmat('gps_z', 8)).sum(1).astype(float)
S['r_gps_z_m3'] = S.gps_z_m3 - S.groupby('race_id').gps_z_m3.transform('mean')
log('GPS joined: runs with a GPS early-speed z', int(S.gps_z.notna().sum()))

# ------------------------------------------------------------------ V3 latent effects: ridge on horse / jockey / trainer / track-barrier, refit by half-year block on earlier data only
LAT_EDGES = list(pd.date_range('2018-01-01', '2027-01-01', freq='6MS'))
S['lat_horse'] = np.nan; S['lat_jk'] = np.nan; S['lat_tk'] = np.nan; S['lat_tb'] = np.nan; S['lat_pred'] = np.nan


def latent_block(a, b):
    from scipy import sparse
    from sklearn.linear_model import Ridge
    trn = S[(S.date < a) & S.e0.notna()]
    if len(trn) < 20000:
        return
    cols = {}
    mats = []
    maps = {}
    for nm_, key in (('h', 'horse_id'), ('j', 'jk'), ('t', 'tk'), ('b', 'dkr')):
        cats = pd.Categorical(trn[key])
        maps[nm_] = {c: i for i, c in enumerate(cats.categories)}
        codes = cats.codes
        ok = codes >= 0
        m = sparse.csr_matrix((np.ones(ok.sum()), (np.where(ok)[0], codes[ok])), shape=(len(trn), len(cats.categories)))
        mats.append(m)
    X = sparse.hstack(mats).tocsr()
    y = (trn.e0 - trn.e0.mean()).values
    # the penalty differs by block: horses are the most informative, the track-barrier cell the least noisy
    alphas = [8.0, 30.0, 30.0, 40.0]
    scale = np.concatenate([np.full(mats[i].shape[1], 1.0 / np.sqrt(alphas[i])) for i in range(4)])
    Xs = X.multiply(scale[None, :]).tocsr()
    mdl = Ridge(alpha=1.0, solver='sparse_cg', fit_intercept=False, max_iter=60, tol=1e-3).fit(Xs, y)
    coef = mdl.coef_ * scale
    off = np.cumsum([0] + [m.shape[1] for m in mats])
    blk = (S.date >= a) & (S.date < b)
    idx = np.where(blk)[0]
    tot = np.zeros(len(idx))
    for i, (nm_, key, col) in enumerate((('h', 'horse_id', 'lat_horse'), ('j', 'jk', 'lat_jk'), ('t', 'tk', 'lat_tk'), ('b', 'dkr', 'lat_tb'))):
        mp = maps[nm_]
        vals = np.array([coef[off[i] + mp[k]] if k in mp else 0.0 for k in S[key].values[idx]])
        S.loc[S.index[idx], col] = vals
        tot += vals
    S.loc[S.index[idx], 'lat_pred'] = tot


def run_latent():
    for a, b in zip(LAT_EDGES[:-1], LAT_EDGES[1:]):
        if a > S.date.max():
            break
        latent_block(a, b)
        log('latent block', a.date())
    S['r_lat_pred'] = S.lat_pred - S.groupby('race_id').lat_pred.transform('mean')
    S['k_lat_pred'] = S.groupby('race_id').lat_pred.rank(pct=True)
    S['r_lat_horse'] = S.lat_horse - S.groupby('race_id').lat_horse.transform('mean')


NEED_LAT = any(v in ARGS.variants for v in ('V3', 'V4', 'V5', 'V6', 'V7', 'V8', 'V12'))
if NEED_LAT:
    run_latent()

# ------------------------------------------------------------------ V4 field competition from the history-only style numbers (stage 2 below uses predictions instead)
for pre, col in (('hist', 'res_ewm'), ('lat', 'lat_pred')):
    if col not in S or S[col].notna().sum() == 0:
        continue
    x = S[col]
    S[f'{pre}_rank'] = S.groupby('race_id')[col].rank(method='min')
    S[f'{pre}_gap_ld'] = x - S.groupby('race_id')[col].transform('min')
    for thr in (0.05, 0.10, 0.20):
        S[f'{pre}_n_lead{int(thr * 100)}'] = ((x - S.groupby('race_id')[col].transform('min')) < thr).groupby(S.race_id).transform('sum').astype(float)
    srt = S.groupby('race_id')[col].apply(lambda s: np.sort(s.dropna().values))
    two = pd.Series({k: (v[1] - v[0]) if len(v) > 1 else np.nan for k, v in srt.items()})
    S[f'{pre}_lone'] = S.race_id.map(two)
    S[f'{pre}_top3'] = S.race_id.map(pd.Series({k: v[:3].mean() if len(v) else np.nan for k, v in srt.items()}))
    S[f'{pre}_sd'] = S.groupby('race_id')[col].transform('std')
    S[f'{pre}_mean'] = S.groupby('race_id')[col].transform('mean')
# crowding by barrier: rivals drawn inside and predicted ahead, outside and ahead
rows = []
for rid, grp in S[['race_id', 'res_ewm', 'barrier']].groupby('race_id', sort=False):
    x, br = grp.res_ewm.values, grp.barrier.values
    if len(x) < 2 or np.isnan(x).all():
        rows.append(pd.DataFrame({'in_ahead': np.nan, 'out_ahead': np.nan, 'n_near': np.nan}, index=grp.index))
        continue
    ahead = x[None, :] < x[:, None]
    inside = br[None, :] < br[:, None]
    rows.append(pd.DataFrame({'in_ahead': (ahead & inside).sum(1), 'out_ahead': (ahead & ~inside).sum(1), 'n_near': (np.abs(x[None, :] - x[:, None]) < 0.08).sum(1) - 1}, index=grp.index))
S = S.join(pd.concat(rows).astype('float64'), rsuffix='_c')
log('competition features done')

# ------------------------------------------------------------------ feature sets
BASE = ['e_m4', 'e_l1', 'e_min4', 'g_m4', 'g_l1', 'g_min4', 'es_m4', 'es_max4', 'e_dist', 'g_dist', 'n_e', 'jk_e', 'tk_e', 'dk_e', 'barrier', 'barfrac', 'nr', 'distance', 'gs', 'rail_m',
        'vcode', 'n_runs', 'days', 'r_e_m4', 'k_e_m4', 'r_g_m4', 'r_es_m4', 'race_min_e']
X1 = ['blink', 'blink_first', 'gear_n', 'wchg', 'dchg', 'jk_same', 'pair_res', 'pair_n', 'letup', 'spell', 'age', 'sex', 'clsc', 'weightCarried', 'jk_res', 'tk_res', 'jk_res90', 'tk_res90', 'r_jk_res',
      'r_tk_res', 'grade', 'wet', 'res_m4', 'res_l1', 'res_m8', 'res_ewm', 'resg_m4', 'lead_r4', 'lead_r8', 'res_sd8', 'r_res_m4', 'k_res_m4', 'r_res_ewm', 'k_res_ewm', 'race_min_res', 'r_lead_r4']
X2 = ['ctx_nr1', 'ctx_bf1', 'ctx_dd1', 'ctx_nr2', 'ctx_bf2', 'e_l2', 'e_l3', 'g_l2', 'res_l2', 'res_l3', 'dkr_e', 'dall_g', 'dk_g', 'dk_lead', 'dall_lead', 'e_m8']
X3 = ['lat_horse', 'lat_jk', 'lat_tk', 'lat_tb', 'lat_pred', 'r_lat_pred', 'k_lat_pred', 'r_lat_horse']
X4 = [c for c in S.columns if c.startswith(('hist_', 'lat_n', 'lat_rank', 'lat_gap', 'lat_lone', 'lat_top3', 'lat_sd', 'lat_mean')) and c not in X3] + ['in_ahead', 'out_ahead', 'n_near']
X9 = ['gps_z_m3', 'gps_z_l1', 'gps_n', 'r_gps_z_m3']
X10 = ['to600_m4', 'l600_m4', 'r_to600_m4', 'k_to600_m4']
X11 = ['tkv_res', 'jkv_res', 'tkd_res', 'jk_dband_res']


def U(*lists):
    out = []
    for l in lists:
        out += [c for c in l if c in S.columns and c not in out]
    return out


FS = {'V0': U(BASE), 'V1': U(BASE, X1), 'V2': U(BASE, X1, X2), 'V3': U(BASE, X1, X2, X3), 'V4': U(BASE, X1, X2, X3, X4), 'V9': U(BASE, X1, X2, X3, X4, X9),
      'V10': U(BASE, X1, X2, X3, X4, X10), 'V11': U(BASE, X1, X2, X3, X4, X11), 'V12': U(BASE, X1, X2, X3, X4, X9, X10, X11)}

# ------------------------------------------------------------------ learners and metrics
TEST_EDGES = list(pd.date_range('2025-01-01', '2027-01-01', freq='6MS'))
if DEBUG:
    TEST_EDGES = TEST_EDGES[:2]
TRAIN_CAP = 250_000 if DEBUG else 700_000
NR = 60 if DEBUG else 300
P0 = dict(learning_rate=0.08, num_leaves=63, min_data_in_leaf=100, feature_fraction=0.8, bagging_fraction=0.7, bagging_freq=1, lambda_l2=5, verbose=-1, num_threads=0)


def group_sizes(df):
    return df.groupby('race_id', sort=False).size().values


def softmax_lead_obj(df):
    sizes = group_sizes(df)
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    y = df.lead.values.astype(float)

    def fobj(preds, ds):
        z = preds - np.repeat(np.maximum.reduceat(preds, starts), sizes)
        e = np.exp(z)
        p = e / np.repeat(np.add.reduceat(e, starts), sizes)
        return p - y, np.maximum(p * (1 - p), 1e-6)
    return fobj


def fit_predict(kind, feats, trn, blk, seed=None):
    p = dict(P0) if seed is None else dict(P0, seed=seed)
    if kind == 'reg_e':
        m = lgb.train(dict(p, objective='regression'), lgb.Dataset(trn[feats], trn.e0), NR)
        return m.predict(blk[feats])
    if kind == 'reg_g':
        m = lgb.train(dict(p, objective='huber', alpha=3.0), lgb.Dataset(trn[feats], trn.g0), NR)
        return m.predict(blk[feats])
    if kind == 'rank':
        t = trn.sort_values(['race_id'])
        t = t.assign(rr=t.groupby('race_id').pos800.rank(method='first'))
        lab = np.maximum(0, 18 - t.rr.values).astype(int)
        m = lgb.train(dict(p, objective='lambdarank', metric='ndcg', lambdarank_truncation_level=8, label_gain=list(range(0, 40)), eval_at=[3]), lgb.Dataset(t[feats], lab, group=group_sizes(t)), NR)
        return -m.predict(blk[feats])          # larger = further back, like e0
    if kind == 'lead':
        t = trn.sort_values(['race_id', 'horse_id'])
        m = lgb.train(dict(p, objective=softmax_lead_obj(t), metric='None'), lgb.Dataset(t[feats], t.lead.values), NR)
        return -m.predict(blk[feats], raw_score=True)
    raise ValueError(kind)


def race_corr(d, a, b):
    ra, rb = d.groupby('race_id')[a].rank(), d.groupby('race_id')[b].rank()
    ra, rb = ra - ra.groupby(d.race_id).transform('mean'), rb - rb.groupby(d.race_id).transform('mean')
    num = (ra * rb).groupby(d.race_id).sum()
    den = np.sqrt((ra ** 2).groupby(d.race_id).sum() * (rb ** 2).groupby(d.race_id).sum())
    return (num / den.replace(0, np.nan)).mean()


def evaluate(df, pred, name):
    d = df.assign(pr=np.asarray(pred))
    d = d[d.nr >= 6]
    cnt = d.groupby('race_id').pos800.transform('count')
    cp = d.groupby('race_id').pr.transform('count')
    sz = d.groupby('race_id').pr.transform('size')
    d = d[(cnt == sz) & (cp == sz)]
    sp = race_corr(d, 'pr', 'e0')
    top = d.loc[d.groupby('race_id').pr.idxmin()]
    acc = (top.lead == 1).mean()
    rk = d.groupby('race_id').pr.rank(method='first')
    lw = d[d.lead == 1].assign(rk=rk)
    in3, in1 = lw.rk.le(3).mean(), lw.rk.le(1).mean()
    try:
        auc = roc_auc_score(d.lead, -d.pr)
    except Exception:
        auc = np.nan
    cg = race_corr(d[d.g0.notna()], 'pr', 'g0')
    res = dict(name=name, races=d.race_id.nunique(), spearman_pos=sp, spearman_gap=cg, leader_top1=acc, leader_in_top3=in3, auc_lead=auc)
    log(f'  {name:34s} races {res["races"]:6d}  spearman(pos) {sp:.4f}  spearman(gap) {cg:.4f}  leader top1 {acc:.3%}  leader in top3 {in3:.3%}  AUC lead {auc:.4f}')
    return res


def run_variant(vname, kinds, feats, tag=None):
    tag = tag or vname
    results = []
    preds = {k: pd.Series(np.nan, index=S.index) for k in kinds}
    for a, b in zip(TEST_EDGES[:-1], TEST_EDGES[1:]):
        trn = S[(S.date < a) & S.e0.notna() & S.g0.notna()]
        trn = trn.groupby('race_id').filter(lambda g: True) if False else trn
        if len(trn) > TRAIN_CAP:
            trn = trn[trn.race_id.isin(trn.race_id.drop_duplicates().sample(frac=TRAIN_CAP / len(trn), random_state=1))]
        blk = S[(S.date >= a) & (S.date < b) & S.e0.notna()]
        if len(blk) == 0:
            continue
        for k in kinds:
            preds[k].loc[blk.index] = fit_predict(k, feats, trn, blk)
    test = S[(S.date >= TEST_EDGES[0]) & (S.date < TEST_EDGES[-1]) & S.e0.notna()]
    outs = {}
    for k in kinds:
        outs[k] = evaluate(test, preds[k].loc[test.index], f'{tag}/{k}')
        results.append(outs[k])
    if len(kinds) > 1:
        rk = pd.concat([preds[k].loc[test.index].groupby(test.race_id).rank(pct=True) for k in kinds], axis=1).mean(axis=1)
        results.append(evaluate(test, rk, f'{tag}/ensemble'))
    pd.DataFrame(results).to_csv(os.path.join(ARGS.out, f'{tag}.csv'), index=False)
    for k in kinds:
        preds[k].loc[test.index].to_pickle(os.path.join(ARGS.out, f'pred_{tag}_{k}.pkl'))
    return results


if __name__ == '__main__':
    base_kinds = ['reg_e']
    for v in ARGS.variants.split(','):
        v = v.strip()
        if v in ('V0', 'V1', 'V2', 'V3', 'V4', 'V9', 'V10', 'V11', 'V12') and v != 'V12':
            run_variant(v, base_kinds, FS[v])
        elif v == 'V5':
            run_variant('V5', ['rank'], FS['V4'])
        elif v == 'V6':
            run_variant('V6', ['reg_g'], FS['V4'])
        elif v == 'V7':
            run_variant('V7', ['lead'], FS['V4'])
        elif v == 'V8':
            run_variant('V8', ['reg_e', 'rank', 'reg_g', 'lead'], FS['V4'])
        elif v == 'V12':
            run_variant('V12', ['reg_e', 'rank', 'reg_g', 'lead'], FS['V12'])
        elif v == 'NOISE':
            for sd in range(ARGS.seeds):
                P0['seed'] = sd
                run_variant('V0', base_kinds, FS['V0'], tag=f'V0_seed{sd}')
                P0['seed'] = 0
    log('done')
