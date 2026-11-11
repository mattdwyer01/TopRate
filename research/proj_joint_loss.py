"""Proj trained to pick winners BY predicting ratings: one model, joint loss (10 Nov 2026).

The score is the rating (ATW scale). Loss per race = Huber(rating miss, 4 points) + lam x winner log-loss, where the win
chances are softmax(BETA x rating) over the field (BETA 0.20, the dashboard's price sharpness). lam = 0 is the Proj
stand-in (rating only); larger lam pays more for getting the winner right. Reported for each lam: how well it still
predicts the rating (RMSE, MAE, median miss, within 3, slope of actual on predicted inside a race) and how well it
picks winners (winner log-lik at BETA, top pick, winner in the top 3, the 2 / 4 point lines).
For comparison: the direct winner model, and the after-the-fact blend of the rating model with the direct model.

Data and inputs come from research/proj_top3_retrain.py (its feature build is run as is): results-file history
converted to the page ATW scale per target race, fit 2021 to mid 2024, early stop 2024 H2, T1 = 2025 full fields,
T2 = the daily log's complete real fields with the dashboard Proj.
  PYTHONPATH=.:projection:research python research/proj_joint_loss.py   (needs /tmp/direct_ctx_feats.pkl, artifact direct-v3)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, 'proj_top3_retrain.py')).read()
A_END = SRC.index('# ===================== Plackett-Luce')
B_START = SRC.index('# ---------------- T2:')
B_END = SRC.index("for nm, (m, fl) in MODELS.items():\n    S2[")
exec(compile(SRC[:A_END], 'proj_top3_retrain.py[features]', 'exec'))      # noqa: defines d, tr, va, te, V3A, XC, BASE2, helpers
L0 = SRC.index('def lines(df, rating, name')
exec(compile(SRC[L0:SRC.index('# ---------- scale choice')], 'proj_top3_retrain.py[lines]', 'exec'))
DRY = os.environ.get('JOINT_DRY') == '1'          # quick end-to-end pass on a small sample, to catch errors before the long run
ROUNDS = 20 if DRY else 3000
if DRY:
    tr = tr[tr.race_id.isin(tr.race_id.unique()[:3000])]

BETA = 0.20
DELTA = 4.0
LAMS = [float(x) for x in os.environ.get('JOINT_LAMS', '0,15,40,100').split(',')]
AFE = list(dict.fromkeys([c for c in BASE2 if c not in ('jw', 'jw90', 'tw', 'tw90')] + XC))
SETS = {'Proj inputs': AFE, 'all inputs': V3A}
for df in (tr, va, te):
    df['fin'] = df.groupby('race_id').pos.rank(method='first')
BASE = float(tr.tgt.median())


def joint_parts(df, preds, lam):
    sizes, starts = group_info(df)
    y = df.win.values.astype(float)
    t = df.tgt.values
    ok = np.isfinite(t)
    res = np.where(ok, preds - np.where(ok, t, 0.0), 0.0)
    g = np.clip(res, -DELTA, DELTA)
    h = ok.astype(float)
    a = np.abs(res)
    hub = np.where(a <= DELTA, 0.5 * res ** 2, DELTA * (a - 0.5 * DELTA))[ok].mean()
    z = BETA * preds
    z = z - np.repeat(np.maximum.reduceat(z, starts), sizes)
    e = np.exp(z)
    p = e / np.repeat(np.add.reduceat(e, starts), sizes)
    nll = -np.log(np.clip(p[y == 1], 1e-12, None)).mean()
    g = g + lam * BETA * (p - y)
    h = h + lam * BETA * BETA * p * (1 - p)
    return g, np.maximum(h, 1e-3), hub, nll


def train_joint(feats, lam):
    def fobj(preds, ds):
        g, h, _, _ = joint_parts(tr, preds, lam)
        return g, h

    def feval(preds, ds):
        _, _, hub, nll = joint_parts(va, preds, lam)
        # per-runner scale: the winner term is one row in about ten
        return 'joint', hub + lam * nll / (len(va) / va.race_id.nunique()), False
    P = dict(learning_rate=0.06, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.6, bagging_fraction=0.7, bagging_freq=1, lambda_l2=10, verbose=-1,
             objective=fobj, metric='None')
    dtr = lgb.Dataset(tr[feats], label=tr.win.values, init_score=np.full(len(tr), BASE))
    dva = lgb.Dataset(va[feats], label=va.win.values, init_score=np.full(len(va), BASE), reference=dtr)
    m = lgb.train(P, dtr, num_boost_round=ROUNDS, valid_sets=[dva], feval=feval, callbacks=[lgb.early_stopping(80, verbose=False)])
    return m


def rating_stats(df, r):
    x = df.assign(r=np.asarray(r))
    x = x[x.tgt.notna() & x.r.notna()]
    miss = x.tgt - x.r
    dm_t = x.tgt - x.groupby('race_id').tgt.transform('mean')
    dm_r = x.r - x.groupby('race_id').r.transform('mean')
    slope = float((dm_t * dm_r).sum() / (dm_r ** 2).sum())
    wr = float(np.sqrt(((dm_t - dm_r) ** 2).mean()))
    top = x[x.r == x.groupby('race_id').r.transform('max')]
    lead_p = float((top.r - top.groupby('race_id').r.transform('mean')).mean()) if len(top) else np.nan
    lead_a = float((top.tgt - x.groupby('race_id').tgt.transform('mean').loc[top.index]).mean())
    pl = float(dm_r.loc[top.index].mean())
    return dict(rmse=float(np.sqrt((miss ** 2).mean())), mae=float(miss.abs().mean()), med=float(miss.median()), w3=float((miss.abs() <= 3).mean()),
                slope=slope, wrmse=wr, sd=float(dm_r.std()), lead_p=pl, lead_a=lead_a)


def win_ll(df, r, beta=BETA):
    p = softmax(df, np.asarray(r), beta)
    return np.log(p[df.win == 1].clip(1e-9)).set_axis(df.race_id[df.win == 1])


def best_beta(df, r):
    bs = np.linspace(0.08, 0.40, 33)
    return bs[int(np.argmax([win_ll(df, r, b).mean() for b in bs]))]


def pick(df, r):
    x = df.assign(r=np.asarray(r))
    rk = x.groupby('race_id').r.rank(ascending=False, method='first')
    return float(x.loc[rk == 1, 'win'].mean()), float((rk[x.win == 1] <= 3).mean())


def report(df, name, r, ref=None, beta_fit=None, rate=True):
    ll = win_ll(df, r)
    t1, t3 = pick(df, r)
    ln = lines(df, r, name, quiet=True)
    s = f'{name:40s} winner LL@0.20 {ll.mean():8.4f}'
    if beta_fit is not None:
        s += f' (best beta {beta_fit:.2f}: {win_ll(df, r, beta_fit).mean():8.4f})'
    if ref is not None:
        dgain = (ll - ref.reindex(ll.index)).dropna()
        s += f'  vs ref {dgain.mean():+.4f} (se {dgain.std() / np.sqrt(len(dgain)):.4f})'
    s += f'  top pick {t1:5.1%}  winner top3 {t3:5.1%}  within 2: {ln[2][0]:.2f} runners {ln[2][1]:5.1%}  within 4: {ln[4][0]:.2f} runners {ln[4][1]:5.1%}'
    print(s, flush=True)
    if rate:
        q = rating_stats(df, r)
        print(f'{"":40s} rating: RMSE {q["rmse"]:.3f}  MAE {q["mae"]:.3f}  median miss {q["med"]:+.2f}  within 3 {q["w3"]:5.1%}  in-race RMSE {q["wrmse"]:.3f}  '
              f'slope actual/predicted {q["slope"]:.3f}  in-race sd {q["sd"]:.2f}  top rated: predicted {q["lead_p"]:+.2f} above its field, ran {q["lead_a"]:+.2f}', flush=True)
    return ll


M = {}
for sname, feats in SETS.items():
    for lam in LAMS:
        m = train_joint(feats, lam)
        M[(sname, lam)] = (m, feats)
        for df in (va, te):
            df[f'j_{sname}_{lam}'] = BASE + m.predict(df[feats])
        print(f'trained {sname} lam {lam:g}: {m.best_iteration} trees', flush=True)
if DRY:
    SRC = SRC.replace('num_boost_round=3000', 'num_boost_round=20')
    exec(compile(SRC[SRC.index('def train_b3'):SRC.index('def metrics(')], 'b3', 'exec'))
mD, TD = train_b3(V3A)
for df in (va, te):
    df['s_direct'] = mD.predict(df[V3A]) * TD            # ln chance up to a race constant


def blend(df, rcol, w):
    """after-the-fact blend: rating model's race mean, (1 - w) of its spread, w of the direct model's chances at 5 points per ln chance"""
    mu = df[rcol].groupby(df.race_id).transform('mean')
    c = df.s_direct - df.s_direct.groupby(df.race_id).transform('mean')
    return mu + (1 - w) * (df[rcol] - mu) + w * c / BETA


print('\n\n===== T1 (2025, %d full fields). lam 0 = rating only (the Proj stand-in) =====' % te.race_id.nunique())
for sname in SETS:
    print(f'\n--- {sname} ({len(SETS[sname])}) ---')
    ref = None
    for lam in LAMS:
        col = f'j_{sname}_{lam}'
        ll = report(te, f'joint lam {lam:g}', te[col], ref=ref, beta_fit=best_beta(va, va[col]))
        if lam == LAMS[0]:
            ref = ll
    for w in (0.3, 0.5, 0.8):
        report(te, f'blend of lam 0 with direct, share {w:.0%}', blend(te, f'j_{sname}_{LAMS[0]}', w), ref=ref)
p = softmax(te, te.s_direct, 1.0)
print('\ndirect winner model (all inputs): winner LL %.4f, top pick %.1f%%' % (np.log(p[te.win == 1].clip(1e-9)).mean(), 100 * pick(te, te.s_direct)[0]))

# by experience: does the joint loss help or hurt particular runners' ratings
print('\nrating RMSE on T1 by earlier runs (all inputs): ' + ' | '.join(
    f'lam {lam:g}: ' + ', '.join(f'{lab} {rating_stats(te[msk], te.loc[msk, f"j_all inputs_{lam}"])["rmse"]:.2f}'
                                 for lab, msk in (('1-2', te.n_runs.between(1, 2)), ('3-5', te.n_runs.between(3, 5)), ('6+', te.n_runs >= 6)))
    for lam in LAMS))

# ---------------- T2: real complete fields with the dashboard Proj ----------------
MODELS = {}
B_START = SRC.index('# ---------------- T2:')          # recomputed: the dry run edits SRC
B_END = SRC.index("for nm, (m, fl) in MODELS.items():\n    S2[")
exec(compile(SRC[B_START:B_END], 'proj_top3_retrain.py[T2]', 'exec'))
S2['s_direct'] = mD.predict(S2[V3A]) * TD
print('\n\n===== T2: %d real complete fields (%s to %s) with the dashboard Proj =====' % (S2.race_id.nunique(), S2.date.min().date(), S2.date.max().date()))
S2['tgt'] = np.nan
ref2 = report(S2, 'dashboard Proj', S2.pj, rate=False)
for sname in SETS:
    print(f'--- {sname} ---')
    for lam in LAMS:
        m, feats = M[(sname, lam)]
        S2['j'] = BASE + m.predict(S2[feats])
        dd = S2.j - S2.pj
        dm = (S2.j - S2.j.groupby(S2.race_id).transform('mean')), (S2.pj - S2.pj.groupby(S2.race_id).transform('mean'))
        report(S2, f'joint lam {lam:g}', S2.j, ref=ref2, rate=False)
        print(f'{"":40s} vs dashboard Proj: mean diff {dd.mean():+.2f}, in-race corr {np.corrcoef(dm[0], dm[1])[0, 1]:.3f}, in-race sd {dm[0].std():.2f} (Proj {dm[1].std():.2f})')
for w in (0.5, 0.8):
    S2['sA'] = S2.pj
    report(S2, f'dashboard Proj blended with direct {w:.0%}', blend(S2, 'pj', w), ref=ref2, rate=False)
