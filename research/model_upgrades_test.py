"""Five model upgrades tested against the live-style direct model (6 Nov 2026, owner: "try 2, 3, 4, 5, 6 now").

Reuses the data build of research/direct_finish_v3.py (converted full-field history 2019-06 to 2025-12 with the Proj context block, the live complete fields in
data/direct_log) and its softmax-loss direct model with the V3a inputs (the live direct model, direct_model/V3a.txt) as CONTROL. Every variant uses the same fit
(2021-01 to 2024-06), early stopping (2024 H2) and test races, and is reported as a paired winner log-likelihood difference against the control:
  2  MARKET   control + the market's view (ln of the normalised implied chance from the price, and its rank). T1 uses the closing starting price, T2 the last logged
              fixed price. Also the market alone, for reference. Breaks the owner's no-price rule if shipped; tested on request.
  3  SEQUENCE a GRU over each horse's last 12 runs (ATW-converted rating, margin, finish share, distance, going, days, weight, class, field size) predicting the run's
              rating; its prediction and field-relative versions added to the control. Two horse folds, so a training row is never scored by a GRU that saw it.
  4  BAGGING  the control trained with 5 seeds, scores averaged.
  5  WEATHER  rain on the 1, 3 and 7 days before the race, race-day max temperature, wind and gusts at the venue (data/weather, Open-Meteo), plus wet x going.
  6  LIVE     the control trained with the labelled complete live fields (data/direct_log) added; tested on the NEWEST 7 days of those fields only (held out).
T1 = 2025 results-file races (full fields). T2 = the labelled complete live fields (real page-scale ratings).
Run: PYTHONPATH=.:projection:research python research/model_upgrades_test.py   (about 2 to 3 hours; use .github/workflows/model_upgrades.yml)"""
import glob, os, re, sys
import numpy as np, pandas as pd, lightgbm as lgb

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, 'direct_finish_v3.py')).read()
# --- data build of v3 (everything before its own model training) ---
exec(compile(SRC[:SRC.index('MODELS = {}')], 'direct_finish_v3_head', 'exec'))
# --- T2 frame build of v3 (live complete fields), without v3's own models ---
seg = SRC[SRC.index('# ---------------- T2'):SRC.index('P2, LL2 = {}, {}')]
seg = re.sub(r"print\(f'\\nT2: real page-scale fields.*\n", '', seg)
exec(compile(seg, 'direct_finish_v3_t2', 'exec'))
print(f'T2 live complete fields: {Lf.race_id.nunique()} races, {Lf.date.min().date()} to {Lf.date.max().date()}', flush=True)


def train(trd, vad, feats, seed=1, weight=None):
    P = dict(learning_rate=0.03, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
             objective=softmax_obj(trd), metric='None', seed=seed, bagging_seed=seed, feature_fraction_seed=seed)
    dtr = lgb.Dataset(trd[feats], label=trd.win.values, weight=weight)
    dva = lgb.Dataset(vad[feats], label=vad.win.values, reference=dtr)
    m = lgb.train(P, dtr, num_boost_round=3000, valid_sets=[dva], feval=softmax_eval(vad), callbacks=[lgb.early_stopping(80, verbose=False)])
    return m


def ll_by_race(df, p):
    w = df.win.values == 1
    return pd.Series(np.log(np.asarray(p)[w].clip(1e-9)), index=df.race_id.values[w])


def report(tag, df, ctrl, cand, label):
    a, b = ll_by_race(df, ctrl), ll_by_race(df, cand)
    dif = (b - a)
    mc = metrics(df, cand, f'  {tag} {label}', key='rk')
    print(f'     {label} minus control: {dif.mean():+.4f} (se {dif.std() / np.sqrt(len(dif)):.4f}) over {len(dif)} races', flush=True)


def scores(m, df, feats):
    return m.predict(df[feats])


def prob(df, s, T):
    return softmax(df, s, T, 'rk').values


BASEF = list(V3A)
res = {}
# ---------------- control ----------------
m0 = train(tr, va, BASEF)
T0 = fit_T(va, m0.predict(va[BASEF]))
p0_te, p0_L = prob(te, scores(m0, te, BASEF), T0), prob(Lf, scores(m0, Lf, BASEF), T0)
print(f'\ncontrol (V3a, softmax loss): {m0.best_iteration} trees', flush=True)
metrics(te, p0_te, '  T1 control', key='rk')
metrics(Lf, p0_L, '  T2 control', key='rk')

# ---------------- 4 bagging ----------------
print('\n=== 4 BAGGING: 5 seeds averaged ===', flush=True)
sv, st, sl = [m0.predict(va[BASEF])], [scores(m0, te, BASEF)], [scores(m0, Lf, BASEF)]
for sd in (2, 3, 4, 5):
    m = train(tr, va, BASEF, seed=sd)
    sv.append(m.predict(va[BASEF])); st.append(scores(m, te, BASEF)); sl.append(scores(m, Lf, BASEF))
Tb = fit_T(va, np.mean(sv, axis=0))
report('T1', te, p0_te, prob(te, np.mean(st, axis=0), Tb), 'bagged x5')
report('T2', Lf, p0_L, prob(Lf, np.mean(sl, axis=0), Tb), 'bagged x5')

# ---------------- 5 weather ----------------
print('\n=== 5 WEATHER ===', flush=True)
wf = []
for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'weather', 'daily_*.parquet'))):
    w = pd.read_parquet(f)
    w['date'] = pd.to_datetime(w['time']).astype('datetime64[ns]')
    w = w.sort_values('date')
    rain = w.precipitation_sum.fillna(0)
    w['rain1'] = rain.shift(1)
    w['rain3'] = rain.shift(1).rolling(3, min_periods=1).sum()
    w['rain7'] = rain.shift(1).rolling(7, min_periods=1).sum()
    w['tmax'] = w.temperature_2m_max
    w['wind'] = w.wind_speed_10m_max
    w['gust'] = w.wind_gusts_10m_max
    wf.append(w[['vk', 'date', 'rain1', 'rain3', 'rain7', 'tmax', 'wind', 'gust']])
WX = pd.concat(wf, ignore_index=True).drop_duplicates(['vk', 'date'])
WCOLS = ['rain1', 'rain3', 'rain7', 'tmax', 'wind', 'gust', 'wet_x_going']


def add_wx(df):
    if 'vk' not in df.columns or df.vk.isna().all():
        src = df['venue'] if 'venue' in df.columns else df.get('track')
        df = df.assign(vk=C.venue_key(pd.Series(src).astype(str)).values)
    df = df.drop(columns=[c for c in WCOLS if c in df.columns]).merge(WX, on=['vk', 'date'], how='left')
    df['wet_x_going'] = df.rain3 * df.gs if 'gs' in df.columns else np.nan
    return df


for nm in ('tr', 'va', 'te'):
    globals()[nm] = add_wx(globals()[nm].reset_index(drop=True))
Lf = add_wx(Lf.reset_index(drop=True))
p0_te, p0_L = prob(te, scores(m0, te, BASEF), T0), prob(Lf, scores(m0, Lf, BASEF), T0)
print(f'weather matched: T1 {te.rain3.notna().mean():.1%}, T2 {Lf.rain3.notna().mean():.1%}, train {tr.rain3.notna().mean():.1%}', flush=True)
FW = BASEF + WCOLS
mw = train(tr, va, FW)
Tw = fit_T(va, mw.predict(va[FW]))
report('T1', te, p0_te, prob(te, scores(mw, te, FW), Tw), '+weather')
report('T2', Lf, p0_L, prob(Lf, scores(mw, Lf, FW), Tw), '+weather')
wet = te.rain3.fillna(0) >= 10
if wet.any():
    sub = te[wet]
    report('T1 wet (3-day rain 10mm+)', sub, p0_te[wet.values], prob(te, scores(mw, te, FW), Tw)[wet.values], '+weather')

# ---------------- 2 market ----------------
print('\n=== 2 MARKET (breaks the no-price rule; tested on request) ===', flush=True)


def add_mkt(df, price):
    pr = pd.to_numeric(price, errors='coerce')
    ip = 1 / pr
    book = ip.groupby(df.race_id).transform('sum')
    ok = df.assign(_p=pr).groupby('race_id')._p.transform(lambda s: s.notna().all()) & book.between(1.05, 2.0)
    df = df.assign(lmk=np.log(ip / book), mk_rank=ip.groupby(df.race_id).rank(ascending=False), mk_ok=ok)
    return df


tr = add_mkt(tr, tr.priceStarting); va = add_mkt(va, va.priceStarting); te = add_mkt(te, te.priceStarting)
Lf = add_mkt(Lf, Lf.price)
FM = BASEF + ['lmk', 'mk_rank']
mm = train(tr, va, FM)
Tm = fit_T(va, mm.predict(va[FM]))
for tag, df, p0 in (('T1', te, p0_te), ('T2', Lf, p0_L)):
    ok = df.mk_ok.values
    sub = df[ok]
    print(f'  {tag}: {sub.race_id.nunique()} clean-book races', flush=True)
    Tmk = fit_T(va[va.mk_ok], va.loc[va.mk_ok, 'lmk'])
    metrics(sub, prob(sub, sub.lmk, Tmk), f'  {tag} market alone', key='rk')
    report(tag, sub, p0[ok], prob(df, scores(mm, df, FM), Tm)[ok], 'control+market')

# ---------------- 6 live complete fields in training ----------------
print('\n=== 6 LIVE COMPLETE FIELDS IN TRAINING (held out: newest 7 days) ===', flush=True)
cut = Lf.date.max() - pd.Timedelta(days=6)
Ltr, Lte = Lf[Lf.date < cut].copy(), Lf[Lf.date >= cut].copy()
print(f'  live training fields {Ltr.race_id.nunique()} races, held-out {Lte.race_id.nunique()} races ({cut.date()} to {Lf.date.max().date()})', flush=True)
if Lte.race_id.nunique() >= 50:
    p_ctrl = prob(Lte, scores(m0, Lte, BASEF), T0)
    for wgt in (1.0, 5.0):
        both = pd.concat([tr, Ltr], ignore_index=True).sort_values(['date', 'race_id']).reset_index(drop=True)
        wv = np.where(both.index >= 0, 1.0, 1.0)
        wv[both.race_id.isin(Ltr.race_id).values] = wgt
        ml = train(both, va, BASEF, weight=wv)
        Tl = fit_T(va, ml.predict(va[BASEF]))
        report('T2 held-out week', Lte, p_ctrl, prob(Lte, scores(ml, Lte, BASEF), Tl), f'+live fields (weight {wgt:g})')
else:
    print('  too few held-out live races, skipped')

# ---------------- 3 sequence model ----------------
print('\n=== 3 SEQUENCE MODEL (GRU over the last 12 runs) ===', flush=True)
try:
    import torch, torch.nn as nn
    torch.set_num_threads(max(1, os.cpu_count() or 1))
    K = 12
    rr = r.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
    rr['y'] = rr.wpr + rr.c_t.fillna(0)
    rr['gap'] = rr.groupby('horse_id').date.diff().dt.days.fillna(60).clip(0, 400) / 100
    rr['clsn'] = pd.Categorical(rr.clsc, categories=CLASSES).codes.astype(float) / max(1, len(CLASSES))
    STEP = ['y', 'mfin', 'finpct', 'distance', 'gs', 'gap', 'weightCarried', 'clsn', 'nr']
    Xs = rr[STEP].astype(float).copy()
    Xs['y'] = (Xs.y - 70) / 15; Xs['mfin'] = Xs.mfin / 10; Xs['distance'] = Xs.distance / 1000 - 1.5; Xs['gs'] = (Xs.gs - 5) / 3
    Xs['weightCarried'] = (Xs.weightCarried - 57) / 3; Xs['nr'] = Xs.nr / 10
    Xs = Xs.fillna(0.0).values.astype(np.float32)
    hid = rr.horse_id.values
    start = np.r_[0, np.flatnonzero(hid[1:] != hid[:-1]) + 1]
    first = np.repeat(start, np.diff(np.r_[start, len(rr)]))
    idx = np.arange(len(rr))
    # tensor of the K earlier runs (most recent last), zero padded; target-race context = today's distance, going, weight, field
    seq = np.zeros((len(rr), K, len(STEP) + 1), np.float32)
    for k in range(1, K + 1):
        j = idx - k
        okk = j >= first
        seq[okk, K - k, :len(STEP)] = Xs[j[okk]]
        seq[okk, K - k, -1] = 1.0
    ctxv = np.stack([rr.distance.fillna(1400).values / 1000 - 1.5, (rr.gs.fillna(5).values - 5) / 3, (rr.weightCarried.fillna(57).values - 57) / 3, rr.nr.fillna(10).values / 10,
                     rr.barfrac.fillna(0.5).values], 1).astype(np.float32)
    yv = rr.y.values.astype(np.float32)
    has = (seq[:, -1, -1] == 1) & np.isfinite(yv) & (rr.date < '2024-07-01').values

    class Net(nn.Module):
        def __init__(s):
            super().__init__()
            s.g = nn.GRU(len(STEP) + 1, 48, batch_first=True)
            s.h = nn.Sequential(nn.Linear(48 + 5, 48), nn.ReLU(), nn.Linear(48, 1))

        def forward(s, x, c):
            _, h = s.g(x)
            return s.h(torch.cat([h[-1], c], 1)).squeeze(1)

    def fit_gru(mask, epochs=4):
        net = Net(); opt = torch.optim.Adam(net.parameters(), 2e-3); lf = nn.HuberLoss(delta=4.0)
        ii = np.flatnonzero(mask)
        for ep in range(epochs):
            np.random.shuffle(ii)
            for b in range(0, len(ii), 2048):
                bi = ii[b:b + 2048]
                opt.zero_grad()
                loss = lf(net(torch.from_numpy(seq[bi]), torch.from_numpy(ctxv[bi])), torch.from_numpy(yv[bi]))
                loss.backward(); opt.step()
            print(f'    gru epoch {ep + 1} loss {loss.item():.3f}', flush=True)
        return net

    def pred(net, sel):
        out = np.full(len(rr), np.nan, np.float32)
        ii = np.flatnonzero(sel)
        with torch.no_grad():
            for b in range(0, len(ii), 8192):
                bi = ii[b:b + 8192]
                out[bi] = net(torch.from_numpy(seq[bi]), torch.from_numpy(ctxv[bi])).numpy()
        return out

    fold = (pd.util.hash_array(hid.astype(np.int64)) % 2).astype(int)
    seqp = np.full(len(rr), np.nan, np.float32)
    nets = []
    for f in (0, 1):
        net = fit_gru(has & (fold != f))
        nets.append(net)
        seqp = np.where(fold == f, pred(net, (seq[:, -1, -1] == 1) & (fold == f)), seqp)
    late = (rr.date >= '2024-07-01').values & (seq[:, -1, -1] == 1)
    seqp = np.where(late, (pred(nets[0], late) + pred(nets[1], late)) / 2, seqp)
    rr['seqp'] = seqp
    sp = rr[['race_id', 'horse_id', 'seqp']]
    for nm in ('tr', 'va', 'te'):
        globals()[nm] = globals()[nm].drop(columns=[c for c in ('seqp', 'r_seqp', 'k_seqp') if c in globals()[nm].columns]).merge(sp, on=['race_id', 'horse_id'], how='left')
        g_ = globals()[nm].groupby('rk').seqp
        globals()[nm]['r_seqp'] = globals()[nm].seqp - g_.transform('mean')
        globals()[nm]['k_seqp'] = g_.rank(pct=True)
    te_ok = te.seqp.notna()
    e = (te.wpr + te.c_t.fillna(0) - te.seqp)[te_ok & te.wpr.notna()]
    print(f'  GRU rating on 2025 runs: RMSE {np.sqrt((e ** 2).mean()):.3f} ({te_ok.mean():.1%} covered)', flush=True)
    p0_te = prob(te, scores(m0, te, BASEF), T0)
    FS = BASEF + ['seqp', 'r_seqp', 'k_seqp']
    ms = train(tr, va, FS)
    Ts = fit_T(va, ms.predict(va[FS]))
    report('T1', te, p0_te, prob(te, scores(ms, te, FS), Ts), '+sequence model')
    metrics(te, prob(te, te.seqp.fillna(te.seqp.mean()), fit_T(va, va.seqp.fillna(va.seqp.mean()))), '  T1 GRU rating alone', key='rk')
    print('  (T2 not scored for the sequence model: the live fields carry 12 page runs, not the results-file sequence the GRU reads)')
except Exception as ex:
    import traceback; traceback.print_exc()
    print('sequence model failed:', ex)
print('\ndone', flush=True)
