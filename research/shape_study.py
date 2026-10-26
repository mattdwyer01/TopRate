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
        'sect_i_early', 'sect_ld_early', 'comments_steward', 'comments_video', 'sire_id', 'sire_of_dam', 'sect_i_to600', 'sect_i_l600', 'sect_i_l400', 'raceShapeEarly', 'positionFinish', 'marginFinish', 'priceStarting', 'wpr']
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

# ------------------------------------------------------------------ X13 new ideas: more recency weightings, horse x jockey early tendency, jockey change, who I must cross (history based), weight rank
w2 = np.array([0.5, 0.25, 0.12, 0.07, 0.03, 0.02, 0.005, 0.005])[None, :]
w1 = np.array([0.7, 0.2, 0.06, 0.02, 0.01, 0.005, 0.003, 0.002])[None, :]
okE = np.isfinite(L['e0'])
for nm_, ww in (('e_ewm1', w1), ('e_ewm2', w2)):
    S[nm_] = np.nansum(np.where(okE, L['e0'], 0) * ww, 1) / np.maximum((okE * ww).sum(1), 1e-9)
    S.loc[okE.sum(1) == 0, nm_] = np.nan
S['pair_e'] = asof_rate(S, 'pair', 'e0', prior=0.0, k=2)
S['pair_dev'] = S.pair_e - S.e_m4
S['jk_e_prev'] = S.groupby('horse_id').jk_e.shift(1)
S['jk_e_chg'] = S.jk_e - S.jk_e_prev
S['e_sd4'] = np.nanstd(L['e0'][:, :4], 1)
S['e_trend'] = L['e0'][:, 0] - np.nanmean(L['e0'][:, 1:4], 1)
S['wt_rank'] = S.groupby('race_id').weightCarried.rank(pct=True)
S['wt_rel'] = S.weightCarried - S.groupby('race_id').weightCarried.transform('mean')
S['age_sex'] = S.age * 10 + S.sex.fillna(0)
cross = {k: np.full(len(S), np.nan) for k in ('cross_in', 'cross_out', 'cross_in_g', 'ahead_n')}
for rid, grp in S[['race_id', 'barrier', 'e_ewm2', 'g_m4']].groupby('race_id', sort=False):
    if len(grp) < 2:
        continue
    ix_ = grp.index.values
    b, e, gg = grp.barrier.values, grp.e_ewm2.values, grp.g_m4.values
    inside = b[None, :] < b[:, None]
    faster = e[None, :] < e[:, None]
    cross['cross_in'][ix_] = (inside & faster).sum(1)
    cross['cross_out'][ix_] = (~inside & faster).sum(1) - (faster & (b[None, :] == b[:, None])).sum(1)
    cross['cross_in_g'][ix_] = (inside & (gg[None, :] < gg[:, None])).sum(1)
    cross['ahead_n'][ix_] = faster.sum(1)
for k_, v_ in cross.items():
    S[k_] = v_
S['cross_in_frac'] = S.cross_in / (S.nr - 1).clip(lower=1)
log('X13 features done')

# ------------------------------------------------------------------ X14 start quality from the comments of the PAST runs (post-race text, used as the horse's earlier history only)
ctxt = (S.comments_steward.fillna('') + ' | ' + S.comments_video.fillna('')).str.lower()
START = {
    'st_slow': r'slow(ly)? (to )?(begin|away|out)|slowly away|missed the start|began awkwardly|dwelt|jumped (late|awkward)|awkward(ly)? (start|away)|fumbled|a bit slow out|bit slow',
    'st_fwd': r'quickly went forward|went forward|crossed to lead|crossed to the lead|soon went forward|bustled|ridden forward|pushed forward|straight to the lead|led from',
    'st_well': r'jumped (well|fine|cleanly)|began well|away well|good start',
    'st_back': r'eased back|restrained|settled (at )?the rear|last early|dropped back|stepped back|shuffled back|not (bustled|hurried)',
}
for k_, p_ in START.items():
    S[k_] = ctxt.str.contains(p_, regex=True).astype(float).where(ctxt.str.len() > 5)
gX = S.groupby('horse_id')
for k_ in START:
    cs_ = gX[k_].cumsum() - S[k_].fillna(0)
    cn_ = gX[k_].transform(lambda s: s.notna().cumsum()) - S[k_].notna().astype(float)
    S['h_' + k_] = (cs_ + 0.15 * 4) / (cn_ + 4)
    S['l3_' + k_] = gX[k_].transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
S['st_net'] = S.h_st_fwd + S.h_st_well - S.h_st_slow - S.h_st_back
S['r_st_net'] = S.st_net - S.groupby('race_id').st_net.transform('mean')
S['r_h_st_slow'] = S.h_st_slow - S.groupby('race_id').h_st_slow.transform('mean')
# gear types beyond blinkers (first time this gear, from the gear-change text)
gt = S.gear_changes.astype(str).str.lower()
for k_, p_ in (('g_ear', r'ear (plug|muff)|earplug'), ('g_tongue', r'tongue'), ('g_cheek', r'cheek'), ('g_winker', r'winker'), ('g_pacifier', r'pacifier')):
    S[k_] = gt.str.contains(p_, regex=True).astype(float)
# trainer x jockey pair early tendency
S['tkjk'] = S.tk.astype(str) + '|' + S.jk.astype(str)
S['tkjk_e'] = asof_rate(S, 'tkjk', 'e0', prior=0.5, k=15)
S['tkjk_res'] = asof_rate(S, 'tkjk', 'res0', prior=0.0, k=15)
S['up_n'] = S.groupby('horse_id').firstup.cumsum() if 'firstup' in S.columns else np.nan
log('X14 features done')

# ------------------------------------------------------------------ X15 pedigree (sire and dam-sire early tendency), X16 style mixture, X17 comment embeddings, X18 weather
S['sire_k'] = S.sire_id.astype(str)
S['sod_k'] = S.sire_of_dam.astype(str).str.lower()
S['sire_dband'] = S.sire_k + '|' + (S.distance / 400).round().astype(str)
S['sire_e'] = asof_rate(S, 'sire_k', 'e0', prior=0.5, k=60)
S['sire_res'] = asof_rate(S, 'sire_k', 'res0', prior=0.0, k=60)
S['sire_lead'] = asof_rate(S, 'sire_k', 'lead', prior=0.1, k=60)
S['sire_d_e'] = asof_rate(S, 'sire_dband', 'e0', prior=0.5, k=40)
S['sod_e'] = asof_rate(S, 'sod_k', 'e0', prior=0.5, k=60)
S['sod_res'] = asof_rate(S, 'sod_k', 'res0', prior=0.0, k=60)
S['r_sire_res'] = S.sire_res - S.groupby('race_id').sire_res.transform('mean')
S['ped_res'] = S.sire_res + S.sod_res
log('X15 pedigree done')
E0 = L['e0']
bins = [(E0 < 0.2), (E0 >= 0.2) & (E0 < 0.45), (E0 >= 0.45) & (E0 < 0.7), (E0 >= 0.7)]
wrec = np.array([0.3, 0.2, 0.15, 0.12, 0.1, 0.06, 0.04, 0.03])[None, :]
okm = np.isfinite(E0)
den = np.maximum((okm * wrec).sum(1), 1e-9)
shares = []
for nm_, b_ in zip(('sh_lead', 'sh_pace', 'sh_mid', 'sh_back'), bins):
    S[nm_] = np.where(okm.sum(1) > 0, (b_ * wrec * okm).sum(1) / den, np.nan)
    shares.append(S[nm_].values)
sh = np.column_stack(shares)
S['sh_ent'] = -np.nansum(np.where(sh > 0, sh * np.log(np.maximum(sh, 1e-9)), 0), 1)
S.loc[okm.sum(1) == 0, 'sh_ent'] = np.nan
gR2 = S.groupby('race_id')
S['n_lead_exp'] = gR2.sh_lead.transform('sum') - S.sh_lead.fillna(0)
S['n_pace_exp'] = gR2.sh_pace.transform('sum') - S.sh_pace.fillna(0)
S['lead_share_me'] = S.sh_lead / (gR2.sh_lead.transform('sum') + 0.3)
S['lead_alone'] = S.sh_lead * np.exp(-S.n_lead_exp)
log('X16 style mixture done')
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.decomposition import TruncatedSVD
ctxt2 = (S.comments_video.fillna('') + ' ' + S.comments_steward.fillna(''))
rs_ = np.random.default_rng(0)
samp_ = ctxt2.sample(250_000, random_state=0)
tf_ = TfidfVectorizer(max_features=20000, min_df=20, sublinear_tf=True, ngram_range=(1, 2), dtype=np.float32).fit(samp_)
svd_ = TruncatedSVD(24, random_state=0).fit(tf_.transform(samp_))
EMB = np.vstack([svd_.transform(tf_.transform(ctxt2.iloc[i:i + 100_000])) for i in range(0, len(S), 100_000)]).astype(np.float32)
hv = S.horse_id.values
acc = np.zeros_like(EMB); cnt = np.zeros(len(S))
for k_ in (1, 2, 3):
    sh_ = np.full_like(EMB, np.nan); sh_[k_:] = EMB[:-k_]
    same = np.r_[np.zeros(k_, bool), hv[k_:] == hv[:-k_]]
    sh_[~same] = np.nan
    ok_ = ~np.isnan(sh_[:, 0])
    acc[ok_] += sh_[ok_]; cnt += ok_
EM = np.where(cnt[:, None] > 0, acc / np.maximum(cnt[:, None], 1), np.nan)
for j_ in range(24):
    S[f'em_{j_}'] = EM[:, j_]
log('X17 comment embeddings done')
wxs = []
for f_ in glob.glob(os.path.join(ROOT, 'data', 'weather', 'daily_*.parquet')):
    w_ = pd.read_parquet(f_); w_['vk2'] = os.path.basename(f_)[6:-8].replace('_', '')
    wxs.append(w_)
if wxs:
    W = pd.concat(wxs, ignore_index=True)
    W['date'] = pd.to_datetime(W.time)
    W = W.sort_values(['vk2', 'date'])
    W['wx_rain0'] = W.precipitation_sum
    W['wx_rain3'] = W.groupby('vk2').precipitation_sum.transform(lambda s: s.shift(1).rolling(3, min_periods=1).sum())
    W['wx_wind'] = W.wind_speed_10m_max; W['wx_gust'] = W.wind_gusts_10m_max; W['wx_temp'] = W.temperature_2m_max
    W['wx_dsin'] = np.sin(np.deg2rad(W.wind_direction_10m_dominant)); W['wx_dcos'] = np.cos(np.deg2rad(W.wind_direction_10m_dominant))
    S = S.merge(W[['vk2', 'date', 'wx_rain0', 'wx_rain3', 'wx_wind', 'wx_gust', 'wx_temp', 'wx_dsin', 'wx_dcos']], left_on=['vk', 'date'], right_on=['vk2', 'date'], how='left').drop(columns='vk2')
    log('X18 weather joined for', int(S.wx_wind.notna().sum()), 'runs')
else:
    for c_ in ('wx_rain0', 'wx_rain3', 'wx_wind', 'wx_gust', 'wx_temp', 'wx_dsin', 'wx_dcos'):
        S[c_] = np.nan

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
X14 = ['h_st_slow', 'h_st_fwd', 'h_st_well', 'h_st_back', 'l3_st_slow', 'l3_st_fwd', 'l3_st_well', 'l3_st_back', 'st_net', 'r_st_net', 'r_h_st_slow', 'g_ear', 'g_tongue', 'g_cheek', 'g_winker', 'g_pacifier', 'tkjk_e', 'tkjk_res']
X15 = ['sire_e', 'sire_res', 'sire_lead', 'sire_d_e', 'sod_e', 'sod_res', 'r_sire_res', 'ped_res']
X16 = ['sh_lead', 'sh_pace', 'sh_mid', 'sh_back', 'sh_ent', 'n_lead_exp', 'n_pace_exp', 'lead_share_me', 'lead_alone']
X17 = [f'em_{j}' for j in range(24)]
X18 = ['wx_rain0', 'wx_rain3', 'wx_wind', 'wx_gust', 'wx_temp', 'wx_dsin', 'wx_dcos']
X13 = ['e_ewm1', 'e_ewm2', 'pair_e', 'pair_dev', 'jk_e_chg', 'e_sd4', 'e_trend', 'wt_rank', 'wt_rel', 'age_sex', 'cross_in', 'cross_out', 'cross_in_g', 'ahead_n', 'cross_in_frac']


def U(*lists):
    out = []
    for l in lists:
        out += [c for c in l if c in S.columns and c not in out]
    return out


FS = {'V0': U(BASE), 'V1': U(BASE, X1), 'V2': U(BASE, X1, X2), 'V3': U(BASE, X1, X2, X3), 'V4': U(BASE, X1, X2, X3, X4), 'V9': U(BASE, X1, X2, X3, X4, X9),
      'V10': U(BASE, X1, X2, X3, X4, X10), 'V11': U(BASE, X1, X2, X3, X4, X11), 'V12': U(BASE, X1, X2, X3, X4, X9, X10, X11), 'V13': U(BASE, X1, X2, X3, X4, X9, X10, X11, X13), 'V13a': U(BASE, X1, X2, X3, X4, X13), 'V15': U(BASE, X1, X2, X3, X4, X9, X10, X11, X13, X14), 'V15a': U(BASE, X1, X2, X3, X4, X14),
      'V16a': U(BASE, X1, X2, X3, X4, X13, X14, X15), 'V16b': U(BASE, X1, X2, X3, X4, X13, X14, X16), 'V16c': U(BASE, X1, X2, X3, X4, X13, X14, X17), 'V16d': U(BASE, X1, X2, X3, X4, X13, X14, X18),
      'V16': U(BASE, X1, X2, X3, X4, X9, X10, X11, X13, X14, X15, X16, X17, X18)}

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



PAIR_BASE = ['e_m4', 'e_ewm2', 'e_l1', 'g_m4', 'es_m4', 'res_ewm', 'barrier', 'barfrac', 'lat_pred', 'jk_e', 'tk_e', 'dk_e', 'pair_e', 'lead_r4', 'e_dist', 'wt_rel', 'days', 'n_runs']
PAIR_CTX = ['nr', 'dnum_', 'rail_m', 'vcode', 'gs_']


def _pairs(df, sample, rng):
    """ordered pairs (i, j) of runners in the same race: all pairs when sample is None, else about `sample` partners per runner."""
    X = df.assign(dnum_=df.distance, gs_=df.gs)
    cols = [c for c in PAIR_BASE if c in X.columns]
    ctx = [c for c in PAIR_CTX if c in X.columns]
    A = X[cols].values.astype(np.float32)
    ctxv = X[ctx].values.astype(np.float32)
    rid = X.race_id.values
    starts = np.r_[0, np.flatnonzero(rid[1:] != rid[:-1]) + 1]
    ends = np.r_[starts[1:], len(rid)]
    ii, jj = [], []
    for a, b in zip(starts, ends):
        n = b - a
        if n < 2:
            continue
        idx = np.arange(a, b)
        i_, j_ = np.meshgrid(idx, idx, indexing='ij')
        m = i_ != j_
        i_, j_ = i_[m], j_[m]
        if sample is not None and len(i_) > sample * n:
            k = rng.choice(len(i_), sample * n, replace=False)
            i_, j_ = i_[k], j_[k]
        ii.append(i_); jj.append(j_)
    ii, jj = np.concatenate(ii), np.concatenate(jj)
    Xp = np.hstack([A[ii], A[jj], A[ii] - A[jj], ctxv[ii]])
    return ii, jj, Xp


def pair_fit_predict(feats, trn, blk, p):
    rng = np.random.default_rng(0)
    t = trn.sort_values(['race_id', 'horse_id']).reset_index(drop=True)
    t = t[t.pos800.notna()].reset_index(drop=True)
    t = t.groupby('race_id').filter(lambda g: len(g) >= 2).reset_index(drop=True)
    if len(t) > 350_000:
        keep = t.race_id.drop_duplicates().sample(n=int(350_000 / 9.5), random_state=1)
        t = t[t.race_id.isin(keep)].reset_index(drop=True)
    ii, jj, Xp = _pairs(t, 6, rng)
    y = (t.pos800.values[ii] < t.pos800.values[jj]).astype(float)
    tie = t.pos800.values[ii] == t.pos800.values[jj]
    m = lgb.train(dict(p, objective='binary', num_leaves=127, min_data_in_leaf=300), lgb.Dataset(Xp[~tie], y[~tie]), NR)
    b = blk.sort_values(['race_id', 'horse_id'])
    b_idx = b.index
    ib, jb, Xb = _pairs(b.reset_index(drop=True), None, rng)
    pr = m.predict(Xb)
    score = np.bincount(ib, weights=pr, minlength=len(b)) / np.maximum(np.bincount(ib, minlength=len(b)), 1)
    out = pd.Series(-score, index=b_idx)       # larger = further back
    return out.reindex(blk.index).values


def set_fit_predict(feats, trn, blk, p):
    """Set transformer over the runners of a race: every runner attends to every other runner in the field (no hand-made field features needed)."""
    import torch, torch.nn as nn
    torch.manual_seed(0); np.random.seed(0)
    torch.set_num_threads(os.cpu_count() or 2)
    cols = [c for c in feats if trn[c].notna().any()]
    mu = trn[cols].mean(); sd = trn[cols].std().replace(0, 1).fillna(1)
    def prep(df):
        X = ((df[cols] - mu) / sd).clip(-5, 5)
        M = X.isna().astype(np.float32).values
        return np.hstack([X.fillna(0).values.astype(np.float32), M[:, :min(40, M.shape[1])]]), df.race_id.values
    def batches(df, X, rid, y=None, bs=128, shuffle=False):
        order = pd.Series(np.arange(len(df))).groupby(rid).apply(list)
        keys = list(order.index)
        if shuffle:
            np.random.shuffle(keys)
        for i in range(0, len(keys), bs):
            ks = keys[i:i + bs]
            n = max(len(order[k]) for k in ks)
            d = X.shape[1]
            xb = np.zeros((len(ks), n, d), np.float32); mb = np.ones((len(ks), n), bool); yb = np.zeros((len(ks), n), np.float32); yk = np.zeros((len(ks), n), bool); ix = np.full((len(ks), n), -1)
            for j, k in enumerate(ks):
                r = order[k]; xb[j, :len(r)] = X[r]; mb[j, :len(r)] = False; ix[j, :len(r)] = r
                if y is not None:
                    yy = y[r]; yb[j, :len(r)] = np.nan_to_num(yy); yk[j, :len(r)] = ~np.isnan(yy)
            yield torch.from_numpy(xb), torch.from_numpy(mb), torch.from_numpy(yb), torch.from_numpy(yk), ix
    t = trn[trn.e0.notna()]
    keep = t.race_id.drop_duplicates()
    if len(keep) > 70_000:
        keep = keep.sample(70_000, random_state=1)
    t = t[t.race_id.isin(keep)].sort_values(['race_id', 'horse_id']).reset_index(drop=True)
    Xt, rt = prep(t); yt = t.e0.values.astype(np.float32)
    dm = Xt.shape[1]
    class Net(nn.Module):
        def __init__(s):
            super().__init__()
            s.inp = nn.Sequential(nn.Linear(dm, 128), nn.GELU(), nn.Linear(128, 96))
            s.enc = nn.TransformerEncoder(nn.TransformerEncoderLayer(96, 4, 192, 0.1, batch_first=True, norm_first=True), 2)
            s.out = nn.Linear(96, 1)
        def forward(s, x, m):
            h = s.enc(s.inp(x), src_key_padding_mask=m)
            return s.out(h).squeeze(-1)
    net = Net(); opt = torch.optim.AdamW(net.parameters(), lr=1e-3, weight_decay=1e-4)
    epochs = 1 if DEBUG else 4
    sched = torch.optim.lr_scheduler.OneCycleLR(opt, max_lr=2e-3, total_steps=epochs * (len(keep) // 128 + 2))
    for ep in range(epochs):
        net.train(); tot = 0; nb = 0
        for xb, mb, yb, yk, _ in batches(t, Xt, rt, yt, shuffle=True):
            pr = net(xb, mb)
            w = (yk & ~mb).float()
            loss = (((pr - yb) ** 2) * w).sum() / w.sum().clamp(min=1)
            opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_(net.parameters(), 1.0); opt.step(); sched.step()
            tot += loss.item(); nb += 1
        log(f'    set epoch {ep + 1}/{epochs} loss {tot / max(nb, 1):.5f}')
    net.eval()
    b = blk.sort_values(['race_id', 'horse_id']); Xb, rb = prep(b)
    out = np.full(len(b), np.nan)
    with torch.no_grad():
        for xb, mb, _, _, ix in batches(b, Xb, rb, None, bs=256):
            pr = net(xb, mb).numpy()
            ok = ix >= 0
            out[ix[ok]] = pr[ok]
    return pd.Series(out, index=b.index).reindex(blk.index).values


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
    if kind == 'pair':
        return pair_fit_predict(feats, trn, blk, p)
    if kind == 'set':
        return set_fit_predict(feats, trn, blk, p)
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


def export_oof():
    """Out-of-fold shape predictions for every half-year block from 2021 on (V12 features), for direct_shape_v5."""
    edges = list(pd.date_range('2021-01-01', '2026-07-01', freq='6MS')) + [pd.Timestamp('2027-01-01')]
    feats = FS['V12']
    out = pd.DataFrame(index=S.index, columns=['pe', 'pg', 'pl'], dtype=float)
    for a, b in zip(edges[:-1], edges[1:]):
        trn = S[(S.date < a) & S.e0.notna() & S.g0.notna()]
        if len(trn) > TRAIN_CAP:
            trn = trn[trn.race_id.isin(trn.race_id.drop_duplicates().sample(frac=TRAIN_CAP / len(trn), random_state=1))]
        blk = S[(S.date >= a) & (S.date < b)]
        if len(blk) == 0:
            continue
        for k, c in (('reg_e', 'pe'), ('reg_g', 'pg'), ('lead', 'pl')):
            out.loc[blk.index, c] = fit_predict(k, feats, trn, blk)
        log('export block', a.date(), len(trn), 'train rows', len(blk), 'predicted')
    res = S[['race_id', 'horse_id']].join(out)
    res = res[res.pe.notna() | res.pg.notna()]
    res.to_parquet(os.path.join(ARGS.out, 'shape_oof.parquet'))
    log('exported', len(res))


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
        elif v == 'V13':
            run_variant('V13', ['reg_e', 'rank', 'lead'], FS['V13'])
        elif v == 'V17':
            run_variant('V17', ['set'], FS['V15'])
        elif v == 'V15':
            run_variant('V15', ['reg_e', 'rank', 'lead'], FS['V15'])
        elif v in ('V16a', 'V16b', 'V16c', 'V16d'):
            run_variant(v, ['reg_e'], FS[v])
        elif v == 'V16':
            run_variant('V16', ['reg_e', 'rank', 'lead'], FS['V16'])
        elif v == 'V15a':
            run_variant('V15a', ['reg_e'], FS['V15a'])
        elif v == 'V14':
            run_variant('V14', ['pair'], FS['V13'])
        elif v == 'NOISE':
            for sd in range(ARGS.seeds):
                P0['seed'] = sd
                run_variant('V0', base_kinds, FS['V0'], tag=f'V0_seed{sd}')
                P0['seed'] = 0
        elif v == 'EXPORT':
            export_oof()
    log('done')
