"""Oracle gap, follow-up tests (26 Oct 2026): can TRAFFIC be predicted (point 2), do INTERACTIONS between runners add (point 4), is it MODEL CAPACITY (point 5)?
Control BASE = V3a + predicted shape (F1), field pressure (F2), conditions (F3), as in direct_shape_v5.
  traffic oracle: realised crowding at 400m (runners within 2 lengths ahead, abreast) and the steward/video trouble flag (post-race, not usable)
  traffic predicted: out-of-fold LightGBM for the trouble flag and the crowding, from the predicted field shape, draw and the horse/jockey history; AUC / corr reported
  interactions: inside / outside drawn neighbours' predicted settle, boxed-in flag, plus a listwise set transformer over the whole field
  capacity: 5 seed bag, deeper trees
Run: PYTHONPATH=.:projection:research python research/oracle_more.py   (needs /tmp/direct_ctx_feats.pkl and the shape-oof artifact like oracle_decomp)"""
import os, re, sys
import numpy as np, pandas as pd, lightgbm as lgb
from sklearn.metrics import roc_auc_score

HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, 'oracle_decomp.py')).read()
cut = src.index('# ------------------------------------------------------------------ models')
head = src[:cut].replace("'raceShapeEarly', 'sect_i_early']", "'raceShapeEarly', 'sect_i_early', 'margin400m', 'margin200m', 'position400m', 'comments_steward', 'comments_video']")
assert 'margin400m' in head
exec(compile(head, 'oracle_head', 'exec'))

# ------------------------------------------------------------------ traffic: realised
TROUBLE = re.compile(r'checked|blocked|held up|no clear run|denied a run|restricted|crowded|bumped|buffeted|inconvenienc|taken in|shifted in|interfer|tightened|steadied|hampered|no room|shuffled|raced wide|without cover', re.I)
txt = (S.comments_steward.fillna('') + ' ' + S.comments_video.fillna('')).str.lower()
S['trouble'] = txt.map(lambda t: 1.0 if TROUBLE.search(t) else 0.0).where(txt.str.len() > 1)
m4 = pd.to_numeric(S.margin400m, errors='coerce')
S['m4'] = m4
def crowd(g):
    m = g.values
    out = np.full((len(m), 2), np.nan)
    if np.isfinite(m).sum() < 2:
        return pd.DataFrame(out, index=g.index, columns=['crowd400', 'abreast400'])
    d = m[None, :] - m[:, None]            # other minus me, positive = other is behind
    ahead2 = ((d < 0) & (d >= -2)).sum(1)
    abre = (np.abs(d) <= 0.5).sum(1) - 1
    out[:, 0], out[:, 1] = ahead2, abre
    out[~np.isfinite(m)] = np.nan
    return pd.DataFrame(out, index=g.index, columns=['crowd400', 'abreast400'])
CR = pd.concat([crowd(g) for _, g in S.groupby('race_id', sort=False).m4])
S = S.join(CR)
log('traffic labels', 'trouble rate %.3f' % S.trouble.mean(), 'coverage', S.trouble.notna().mean())

# ------------------------------------------------------------------ traffic: predicted (out-of-fold by half-year block, time-forward)
S['h_trouble'] = asof_rate(S, 'horse_id', 'trouble', prior=0.15, k=8)
S['jk_trouble'] = asof_rate(S, 'jk', 'trouble', prior=0.15, k=100)
S['tk_trouble'] = asof_rate(S, 'tk', 'trouble', prior=0.15, k=100)
TF = ['pg', 'pe', 'pg_rank', 'pe_rank', 'n_near', 'in_ahead', 'out_ahead', 'n_behind_in', 'n_lead2', 'hot', 'my_share', 'barfrac', 'barrier', 'nr', 'distance', 'gs', 'rail_m', 'vcode',
      'wide_fwd', 'back_in', 'lone', 'jk_e', 'tk_e', 'h_trouble', 'jk_trouble', 'tk_trouble', 'e_m4', 'g_m4']
PT = dict(objective='binary', learning_rate=0.06, num_leaves=31, min_data_in_leaf=200, feature_fraction=0.8, bagging_fraction=0.7, bagging_freq=1, lambda_l2=5, verbose=-1, num_threads=0)
PR_ = dict(PT, objective='regression')
S['ptrouble'] = np.nan; S['pcrowd'] = np.nan
for a, b in zip(edges[:-1], edges[1:]):
    trn = S[(S.date < a) & S.trouble.notna() & S.pg.notna() & (S.nr >= 5)]
    blk = ((S.date >= a) & (S.date < b)).values
    if len(trn) < 5000:
        continue
    m1 = lgb.train(PT, lgb.Dataset(trn[TF], trn.trouble, categorical_feature=['vcode']), 60 if DEBUG else 250)
    S.loc[blk, 'ptrouble'] = m1.predict(S.loc[blk, TF])
    t2 = trn[trn.crowd400.notna()]
    m2 = lgb.train(PR_, lgb.Dataset(t2[TF], t2.crowd400, categorical_feature=['vcode']), 60 if DEBUG else 250)
    S.loc[blk, 'pcrowd'] = m2.predict(S.loc[blk, TF])
t = S[(S.date >= '2025-01-01') & S.trouble.notna() & S.ptrouble.notna()]
log(f'PREDICTING TRAFFIC 2025: trouble flag AUC {roc_auc_score(t.trouble, t.ptrouble):.3f} (base rate {t.trouble.mean():.3f}); '
    f'horse own history alone AUC {roc_auc_score(t.trouble, t.h_trouble.fillna(t.trouble.mean())):.3f}')
t = t[t.crowd400.notna() & t.pcrowd.notna()]
dm = lambda c: t[c] - t.groupby('race_id')[c].transform('mean')
log(f'crowding at 400m within-race corr with prediction {np.corrcoef(dm("crowd400"), dm("pcrowd"))[0, 1]:.3f} (raw corr {np.corrcoef(t.crowd400, t.pcrowd)[0, 1]:.3f})')
# how much of realised crowding / trouble is explained by the draw and the predicted field alone vs the post-race 800m position
for c in ('trouble', 'crowd400'):
    z = S[(S.date >= '2025-01-01') & S[c].notna() & S.e0.notna()]
    log(f'  {c}: corr with realised 800m position {z[c].corr(z.e0):+.3f}, with predicted pe {z[c].corr(z.pe):+.3f}')

# ------------------------------------------------------------------ interactions: neighbours in the barrier order
Ss = S.sort_values(['race_id', 'barrier'])
g = Ss.groupby('race_id', sort=False)
NB = pd.DataFrame({'nb_in_pg': g.pg.shift(1), 'nb_out_pg': g.pg.shift(-1), 'nb_in_pe': g.pe.shift(1), 'nb_out_pe': g.pe.shift(-1),
                   'nb_in_es': g.es_m4.shift(1), 'nb_out_es': g.es_m4.shift(-1)}, index=Ss.index).reindex(S.index)
NB['boxed'] = ((NB.nb_in_pg < S.pg) & (NB.nb_out_pg < S.pg)).astype(float).where(NB.nb_in_pg.notna() & NB.nb_out_pg.notna())
NB['d_in'] = S.pg - NB.nb_in_pg; NB['d_out'] = S.pg - NB.nb_out_pg
NB['cover'] = ((S.pg - S.groupby('race_id').pg.transform('min') > 1.5) & (NB[['nb_in_pg', 'nb_out_pg']].min(1) < S.pg)).astype(float)
INT = list(NB.columns)
S = S.join(NB)

NEW2 = ['crowd400', 'abreast400', 'trouble', 'ptrouble', 'pcrowd'] + INT
N2 = S[['race_id', 'horse_id'] + NEW2].copy()
for c in NEW2:
    N2[c] = N2[c].astype('float32')
tr, va, te = [d.merge(N2, on=['race_id', 'horse_id'], how='left') for d in (tr, va, te)]
for d in (tr, va, te):
    d['rk'] = d.race_id

BASE = V3A + FAM['F1 predicted settle'] + FAM['F2 field pressure'] + FAM['F3 conditions/bias']
BASE = [c for c in dict.fromkeys(BASE) if c in tr.columns]
log('BASE inputs', len(BASE))

# ------------------------------------------------------------------ models
def train_p(feats, seed=0, **over):
    P3 = dict(learning_rate=0.03, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.5, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
              objective=softmax_obj(tr), metric='None', seed=seed)
    P3.update(over)
    dtr = lgb.Dataset(tr[feats], label=tr.win.values)
    dva = lgb.Dataset(va[feats], label=va.win.values, reference=dtr)
    return lgb.train(P3, dtr, num_boost_round=3000, valid_sets=[dva], feval=softmax_eval(va), callbacks=[lgb.early_stopping(80, verbose=False)])

RUNS = {'A0 BASE (V3a + F1 F2 F3)': BASE,
        'T1 + realised crowding at 400m (post-race)': BASE + ['crowd400', 'abreast400'],
        'T2 + steward/video trouble flag (post-race)': BASE + ['trouble'],
        'T3 + both traffic oracles': BASE + ['crowd400', 'abreast400', 'trouble'],
        'T4 + PREDICTED traffic (ptrouble, pcrowd)': BASE + ['ptrouble', 'pcrowd'],
        'I1 + neighbour interactions (barrier order)': BASE + INT}
if DEBUG:
    RUNS = {k: RUNS[k] for k in list(RUNS)[:2]}
LLs, PR, SC = {}, {}, {}
for name, fl in RUNS.items():
    fl = [c for c in dict.fromkeys(fl) if c in tr.columns]
    m = train_p(fl)
    T = fit_T(va, m.predict(va[fl]))
    SC[name] = (m.predict(te[fl]), T)
    PR[name] = softmax(te, SC[name][0], T, 'rk')
    LLs[name] = metrics(te, PR[name], name)
    log(f'{name}: {len(fl)} inputs, {m.best_iteration} trees')

# capacity: seed bag and deeper trees on BASE
if not DEBUG:
    bag_te, bag_va = 0, 0
    for sd_ in range(5):
        m = train_p(BASE, seed=sd_, feature_fraction=0.4 + 0.05 * sd_)
        bag_te = bag_te + m.predict(te[BASE]) / 5
        bag_va = bag_va + m.predict(va[BASE]) / 5
    Tb = fit_T(va, bag_va)
    PR['C1 BASE 5-seed bag'] = softmax(te, bag_te, Tb, 'rk'); LLs['C1 BASE 5-seed bag'] = metrics(te, PR['C1 BASE 5-seed bag'], 'C1 BASE 5-seed bag')
    m = train_p(BASE, num_leaves=255, learning_rate=0.02, min_data_in_leaf=100, feature_fraction=0.35)
    Td = fit_T(va, m.predict(va[BASE]))
    PR['C2 BASE deeper trees'] = softmax(te, m.predict(te[BASE]), Td, 'rk'); LLs['C2 BASE deeper trees'] = metrics(te, PR['C2 BASE deeper trees'], 'C2 BASE deeper trees')
    log('capacity done')

# set transformer over the field (interactions learned, not hand built)
def set_model(fl, epochs=8, max_races=40000, L=20, seed=0):
    import torch, torch.nn as nn
    torch.manual_seed(seed); np.random.seed(seed); torch.set_num_threads(4)
    mu, sd = tr[fl].mean(), tr[fl].std().replace(0, 1)
    def pack(df, with_y=True):
        X = ((df[fl] - mu) / sd).fillna(0).clip(-5, 5).values.astype('float32')
        sizes, starts = group_info(df)
        R = len(sizes)
        Xp = np.zeros((R, L, len(fl)), 'float32'); M = np.zeros((R, L), bool); Y = np.full(R, -1)
        win = df.win.values
        for i, (s, n) in enumerate(zip(starts, sizes)):
            k = min(n, L)
            Xp[i, :k] = X[s:s + k]; M[i, :k] = True
            w = np.where(win[s:s + k] == 1)[0]
            if len(w): Y[i] = w[0]
        return Xp, M, Y, starts, sizes
    Xt, Mt, Yt, _, _ = pack(tr)
    keep_ = np.where(Yt >= 0)[0]
    if len(keep_) > max_races:
        keep_ = np.random.choice(keep_, max_races, replace=False)
    Xt, Mt, Yt = torch.tensor(Xt[keep_]), torch.tensor(Mt[keep_]), torch.tensor(Yt[keep_])
    class Net(nn.Module):
        def __init__(s):
            super().__init__()
            s.i = nn.Linear(len(fl), 96)
            s.e = nn.TransformerEncoder(nn.TransformerEncoderLayer(96, 4, 192, 0.1, batch_first=True), 2)
            s.o = nn.Linear(96, 1)
        def forward(s, x, m):
            h = s.e(s.i(x), src_key_padding_mask=~m)
            return s.o(h).squeeze(-1).masked_fill(~m, -1e9)
    net = Net(); opt = torch.optim.AdamW(net.parameters(), 1e-3, weight_decay=1e-2)
    for ep in range(epochs):
        net.train(); perm = torch.randperm(len(Yt)); tot = 0
        for b in range(0, len(perm), 64):
            ix = perm[b:b + 64]
            lo = net(Xt[ix], Mt[ix])
            loss = nn.functional.cross_entropy(lo, Yt[ix])
            opt.zero_grad(); loss.backward(); opt.step(); tot += loss.item() * len(ix)
        log(f'    set epoch {ep + 1}/{epochs} loss {tot / len(perm):.4f}')
    def predict(df):
        net.eval(); Xp, Mp, _, starts, sizes = pack(df)
        with torch.no_grad():
            lo = torch.cat([net(torch.tensor(Xp[b:b + 512]), torch.tensor(Mp[b:b + 512])) for b in range(0, len(Xp), 512)]).numpy()
        out = np.full(len(df), -50.0)
        for i, (s, n) in enumerate(zip(starts, sizes)):
            k = min(n, L); out[s:s + k] = lo[i, :k]
        return out
    return predict
try:
    sp = set_model(BASE, epochs=2 if DEBUG else 8)
    Ts = fit_T(va, sp(va))
    nm = 'S1 BASE set transformer (listwise)'
    PR[nm] = softmax(te, sp(te), Ts, 'rk'); LLs[nm] = metrics(te, PR[nm], nm)
except Exception as e:                      # torch missing etc.
    log('set transformer skipped:', repr(e))

base = LLs['A0 BASE (V3a + F1 F2 F3)']
print('\nPaired winner log-lik gain over BASE (2025 test):')
for name in LLs:
    if name.startswith('A0'):
        continue
    df = LLs[name] - base
    print(f'   {name:50s} {df.mean():+.4f} (se {df.std() / np.sqrt(len(df)):.4f})')
price_gain(te, PR, te.priceStarting, 'T1 2025 closing price (oracle_more)')
log('done')
