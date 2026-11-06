"""Direct model v4 (6 Nov 2026, owner: "do 4 & 3"): the live direct model (V3a inputs, softmax loss) with
  4  bagging: 5 seeds, raw scores averaged, one temperature fitted on the validation half-year
  3  a sequence model: a GRU over the horse's last 12 RATED runs (direct_seq.py) predicting the run's rating; its prediction and field-relative versions are inputs.
     Every earlier run is put on the TARGET race's page scale (plain wpr + the target's c_t), as a runner page struck for that race shows it, so the live input
     (the log's `hist`, page ratings) and the training input match. Two horse folds give out-of-fold predictions for the training rows.
Same data build, fit (2021-01 to 2024-06), early stopping (2024 H2) and tests as research/model_upgrades_test.py:
  T1 = 2025 results-file full fields, T2 = labelled complete live fields (data/direct_log, real page ratings; the GRU reads their `hist`).
Reports paired winner log-likelihood against a single-seed control, then saves direct_model/v4/ (seed1..5.txt, gru.npz, meta.json). direct_score.py uses v4 when it exists.
Run: PYTHONPATH=.:projection:research python research/train_direct_v4.py   (workflow .github/workflows/train_direct_v4.yml)"""
import json, os, re, sys
import numpy as np, pandas as pd, lightgbm as lgb

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, 'direct_finish_v3.py')).read()
exec(compile(SRC[:SRC.index('MODELS = {}')], 'direct_finish_v3_head', 'exec'))
seg = SRC[SRC.index('# ---------------- T2'):SRC.index('P2, LL2 = {}, {}')]
seg = re.sub(r"print\(f'\\nT2: real page-scale fields.*\n", '', seg)
exec(compile(seg, 'direct_finish_v3_t2', 'exec'))
sys.path.insert(0, ROOT)
import direct_seq as DS  # noqa: E402

OUT = os.path.join(ROOT, 'direct_model', 'v4')
print(f'T2 live complete fields: {Lf.race_id.nunique()} races, {Lf.date.min().date()} to {Lf.date.max().date()}', flush=True)


def train(trd, vad, feats, seed=1):
    P = dict(learning_rate=0.03, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
             objective=softmax_obj(trd), metric='None', seed=seed, bagging_seed=seed, feature_fraction_seed=seed)
    dtr = lgb.Dataset(trd[feats], label=trd.win.values)
    dva = lgb.Dataset(vad[feats], label=vad.win.values, reference=dtr)
    return lgb.train(P, dtr, num_boost_round=3000, valid_sets=[dva], feval=softmax_eval(vad), callbacks=[lgb.early_stopping(80, verbose=False)])


def ll_by_race(df, p):
    w = df.win.values == 1
    return pd.Series(np.log(np.asarray(p)[w].clip(1e-9)), index=df.race_id.values[w])


def compare(tag, df, a, b, label):
    d = ll_by_race(df, b) - ll_by_race(df, a)
    metrics(df, b, f'  {tag} {label}', key='rk')
    print(f'     {label}: {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}) over {len(d)} races', flush=True)


def prob(df, s, T):
    return softmax(df, s, T, 'rk').values


# ---------------- sequence model ----------------
import torch, torch.nn as nn  # noqa: E402
torch.manual_seed(7); np.random.seed(7)
torch.set_num_threads(max(1, os.cpu_count() or 1))
K = DS.K
rr = r.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
rated = rr.wpr.notna().values
R = rr[rated].reset_index().rename(columns={'index': 'row'})
R['gap'] = R.groupby('horse_id').date.diff().dt.days
R['clsn'] = pd.Categorical(R.clsc, categories=CLASSES).codes.astype(float) / max(1, len(CLASSES))
R['y'] = R.wpr
Splain = DS.step_matrix(R)                          # y column here is the plain rating, normalised; the target shift is added per row below
yi = DS.STEP.index('y')
nR = len(R)
pos_before = np.cumsum(np.r_[0, rated[:-1].astype(int)])          # number of rated rows before each rr row (global)
hid = rr.horse_id.values
start = np.r_[0, np.flatnonzero(hid[1:] != hid[:-1]) + 1]
first_row = np.repeat(start, np.diff(np.r_[start, len(rr)]))
first_rated = pos_before[first_row]                                   # rated-row index where this horse's rated runs begin
ct = rr.c_t.fillna(0).values.astype(np.float32)
seq = np.zeros((len(rr), K, DS.NS), np.float32)
nprev = np.minimum(pos_before - first_rated, K)
for k in range(1, K + 1):
    j = pos_before - k
    ok = j >= first_rated
    s = Splain[j[ok]].copy()
    s[:, yi] += ct[ok] / 15                                           # plain + target c_t, on the (y - 70) / 15 scale
    seq[ok, K - k, :len(DS.STEP)] = s
    seq[ok, K - k, -1] = 1.0
# live hist has no run before its oldest listed run: blank the oldest slot's gap, as live does
gi = DS.STEP.index('gap')
oldest = K - nprev
has_any = nprev > 0
seq[np.flatnonzero(has_any), oldest[has_any], gi] = 0.6               # gap unknown -> 60 days, normalised
ctxv = DS.ctx_matrix(rr)
yv = (rr.wpr + rr.c_t.fillna(0)).values.astype(np.float32)
has_seq = seq[:, -1, -1] == 1
fit_mask = has_seq & np.isfinite(yv) & (rr.date < '2024-07-01').values


class Net(nn.Module):
    def __init__(s):
        super().__init__()
        s.g = nn.GRU(DS.NS, 48, batch_first=True)
        s.h = nn.Sequential(nn.Linear(48 + DS.NC, 48), nn.ReLU(), nn.Linear(48, 1))

    def forward(s, x, c):
        _, h = s.g(x)
        return s.h(torch.cat([h[-1], c], 1)).squeeze(1)


def fit_gru(mask, epochs=5):
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
    return {k: v.detach().numpy().astype(np.float32) for k, v in net.state_dict().items()}


def gpred(W, sq, cx):
    out = np.empty(len(sq), np.float32)
    for b in range(0, len(sq), 20000):
        out[b:b + 20000] = DS.gru_forward(W, sq[b:b + 20000], cx[b:b + 20000])
    return out


fold = (pd.util.hash_array(hid.astype(np.int64)) % 2).astype(int)
Ws = [fit_gru(fit_mask & (fold != f)) for f in (0, 1)]
# numpy forward must equal torch
net = Net(); net.load_state_dict({k: torch.from_numpy(v) for k, v in Ws[0].items()})
smp = np.flatnonzero(has_seq)[:2000]
with torch.no_grad():
    tp = net(torch.from_numpy(seq[smp]), torch.from_numpy(ctxv[smp])).numpy()
print(f'  numpy GRU vs torch: max diff {np.abs(gpred(Ws[0], seq[smp], ctxv[smp]) - tp).max():.2e}', flush=True)
seqp = np.full(len(rr), np.nan, np.float32)
early = (rr.date < '2024-07-01').values
for f in (0, 1):
    sel = has_seq & early & (fold == f)
    seqp[sel] = gpred(Ws[f], seq[sel], ctxv[sel])
sel = has_seq & ~early
seqp[sel] = (gpred(Ws[0], seq[sel], ctxv[sel]) + gpred(Ws[1], seq[sel], ctxv[sel])) / 2
rr['seqp'] = seqp
e = (yv - seqp)[(rr.date >= '2025-01-01').values & has_seq & np.isfinite(yv)]
print(f'  GRU rating, 2025 runs: RMSE {np.sqrt((e ** 2).mean()):.3f}', flush=True)
SP = rr[['race_id', 'horse_id', 'seqp']]


def add_seq(df):
    df = df.drop(columns=[c for c in ('seqp', 'r_seqp', 'k_seqp') if c in df.columns])
    if 'hist' in df.columns:
        sq = DS.live_sequences(df, CLASSES, C.class_code)
        hs = sq[:, -1, -1] == 1
        v = np.full(len(df), np.nan, np.float32)
        cx = DS.ctx_matrix(df)
        v[hs] = (gpred(Ws[0], sq[hs], cx[hs]) + gpred(Ws[1], sq[hs], cx[hs])) / 2
        df = df.assign(seqp=v)
    else:
        df = df.merge(SP, on=['race_id', 'horse_id'], how='left')
    g = df.groupby('rk').seqp
    df['r_seqp'] = df.seqp - g.transform('mean')
    df['k_seqp'] = g.rank(pct=True)
    return df


tr, va, te = (add_seq(x.reset_index(drop=True)) for x in (tr, va, te))
Lf = add_seq(Lf.reset_index(drop=True))
print(f'  seqp coverage: T1 {te.seqp.notna().mean():.1%} (mean {te.seqp.mean():.1f} sd {te.seqp.std():.1f}), '
      f'T2 {Lf.seqp.notna().mean():.1%} (mean {Lf.seqp.mean():.1f} sd {Lf.seqp.std():.1f})', flush=True)
# live check: the GRU's rating against the run's actual page rating is not in the log; compare with the live Proj as a sanity check
if 'proj' in Lf.columns:
    pj = pd.to_numeric(Lf.proj, errors='coerce')
    okp = pj.notna() & Lf.seqp.notna()
    print(f'  T2 GRU rating vs live Proj: corr {np.corrcoef(pj[okp], Lf.seqp[okp])[0, 1]:.3f}, mean diff {(Lf.seqp[okp] - pj[okp]).mean():+.2f}', flush=True)

# ---------------- direct models ----------------
BASEF = list(V3A)
FS = BASEF + ['seqp', 'r_seqp', 'k_seqp']
m0 = train(tr, va, BASEF)
T0 = fit_T(va, m0.predict(va[BASEF]))
c_te, c_L = prob(te, m0.predict(te[BASEF]), T0), prob(Lf, m0.predict(Lf[BASEF]), T0)
print(f'\ncontrol (V3a, one seed): {m0.best_iteration} trees')
metrics(te, c_te, '  T1 control', key='rk')
metrics(Lf, c_L, '  T2 control', key='rk')
res = {}
for nm, fl in (('bagged', BASEF), ('bagged+seq', FS)):
    ms = [m0] if fl is BASEF else []
    for sd in range(1, 6):
        if fl is BASEF and sd == 1:
            continue
        ms.append(train(tr, va, fl, seed=sd))
    T = fit_T(va, np.mean([m.predict(va[fl]) for m in ms], axis=0))
    pt = prob(te, np.mean([m.predict(te[fl]) for m in ms], axis=0), T)
    pl = prob(Lf, np.mean([m.predict(Lf[fl]) for m in ms], axis=0), T)
    res[nm] = (ms, T, fl, pt, pl)
    print(f'\n=== {nm} (5 seeds, trees {[m.best_iteration for m in ms]}, T {T:.3f}) ===', flush=True)
    compare('T1', te, c_te, pt, f'{nm} minus control')
    compare('T2', Lf, c_L, pl, f'{nm} minus control')
print('\n=== sequence on top of bagging ===')
compare('T1', te, res['bagged'][3], res['bagged+seq'][3], 'bagged+seq minus bagged')
compare('T2', Lf, res['bagged'][4], res['bagged+seq'][4], 'bagged+seq minus bagged')

# ---------------- save both shippable variants ----------------
os.makedirs(OUT, exist_ok=True)
for nm, key in (('bagged', 'bag'), ('bagged+seq', 'bagseq')):
    ms, T, fl, _, _ = res[nm]
    for i, m in enumerate(ms, 1):
        m.save_model(os.path.join(OUT, f'{key}_seed{i}.txt'))
np.savez(os.path.join(OUT, 'gru.npz'), **{f'f{f}.{k}': v for f in (0, 1) for k, v in Ws[f].items()})
meta = {nm_key: {'feats': res[nm][2], 'T': float(res[nm][1]), 'n_models': len(res[nm][0])} for nm, nm_key in (('bagged', 'bag'), ('bagged+seq', 'bagseq'))}
meta['classes'] = list(CLASSES)
json.dump(meta, open(os.path.join(OUT, 'meta.json'), 'w'), indent=1)
print('saved', OUT, flush=True)
