"""GPS / settle / contention features inside the context Proj training (Huber alpha 4), then winners. Same folds and params as projection/train_ctx.py
(fold 2025: fit before 2025, fold 2026: fit before 2026). Compares the shipped feature set with the shipped set + GPS-derived pre-race features, per run
(miss against the actual ATW rating) and per race (winner log-likelihood, with and without the starting price). Research only: does not write models."""
import os, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'projection'))
import build_trip_map as B
import ctx as C
import gps_feats as GF
OUT = '/tmp/train_ctx_gps_oos.parquet'
if not os.path.exists(OUT):
    rr, FL, HIST, CONT = GF.build()
    rp = C.training_frame_rel(); pg = rp[rp.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
    pg['hn'] = B.clean_name(pg.horse); pg['date'] = pd.to_datetime(pg.date).dt.normalize()
    GPSF = HIST + CONT
    pg = pg.merge(rr[['hn', 'date', 'rid', 'half', 'rank_prior'] + GPSF], on=['hn', 'date'], how='left')
    params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
    for c in ('c0', 'c1'): pg[c] = np.nan
    for cut_, es_, hi_ in (('2025-01-01', '2024-10-01', '2026-01-01'), ('2026-01-01', '2025-10-01', '2099-01-01')):
        cut, es, hi = map(pd.Timestamp, (cut_, es_, hi_))
        tr, va = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)]; te = pg[(pg.date >= cut) & (pg.date < hi)]
        rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
        def fit(feats, a, b):
            m = lgb.LGBMRegressor(**params); m.fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m
        use = (te.n >= C.REL_MIN_RUNS).values
        for tag, extra in (('c0', []), ('c1', GPSF)):
            m0 = fit(F0 + extra, tr, va); m1 = fit(F1 + extra, rel(tr), rel(va))
            c = m0.predict(te[F0 + extra]); c[use] = m1.predict(te.loc[use, F1 + extra])
            pg.loc[te.index, tag] = c
            print('fold', cut_, tag, 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
    pg = pg[pg.c0.notna()].copy()
    pg['proj0'] = pg.f + pg.c0; pg['proj1'] = pg.f + pg.c1
    pg.to_parquet(OUT)
pg = pd.read_parquet(OUT)
pg['miss0'] = pg.wpr - pg.proj0; pg['miss1'] = pg.wpr - pg.proj1
te = pg[pg.date >= '2026-01-01']
def st(e): return f'MAE {e.abs().mean():.3f} within3 {100 * (e.abs() <= 3).mean():.1f}% rmse {np.sqrt((e ** 2).mean()):.3f} median {e.median():+.2f}'
def pair(e0, e1):
    d = e0.abs() - e1.abs(); ds = e0 ** 2 - e1 ** 2
    return f'abs gain {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}), sq gain {ds.mean():+.4f} (se {ds.std() / np.sqrt(len(ds)):.4f})'
print('\nPER RUN (2026 held out; 2025 fold models fit before 2025, 2026 fold before 2026)')
for lab, d in (('all runs', te), ('top half by prior', te[te.half == True]), ('top 4 by prior', te[te.rank_prior <= 4]), ('runs with earlier GPS', te[te.n_gps > 0]), ('top 4 with earlier GPS', te[(te.rank_prior <= 4) & (te.n_gps > 0)])):
    print(f'  {lab:26s} n={len(d):6d}  shipped: {st(d.miss0)}\n  {"":26s} {"":8s}  +GPS:    {st(d.miss1)}\n  {"":37s} {pair(d.miss0, d.miss1)}')
# ---------------- winners
print('\nWINNERS (partial fields: only runners with a Proj in the page store; races with >= 6 such runners and the winner among them)')
w = pg[pg.rid.notna() & pg.priceStarting.notna() & (pg.priceStarting > 1)].copy()
w['lp'] = -np.log(w.priceStarting)       # log implied price (market strength); softmax over the available runners
w['win'] = (w.positionFinish == 1).astype(int)
g = w.groupby('rid')
w = w[(g.win.transform('sum') == 1) & (g.win.transform('size') >= 6)]
print('races', w.rid.nunique(), 'runners', len(w))
import scipy.optimize as O
def nll(par, d, cols):
    s = sum(p * d[c].values for p, c in zip(par, cols)); d = d.assign(s=s)
    mx = d.groupby('rid').s.transform('max'); ex = np.exp(d.s - mx); den = ex.groupby(d.rid).transform('sum')
    ll = np.log(ex / den)[d.win == 1]
    return -ll.sum(), ll
def fitll(tr, te, cols):
    r = O.minimize(lambda p: nll(p, tr, cols)[0], x0=np.full(len(cols), 0.1), method='Nelder-Mead')
    return r.x, nll(r.x, te, cols)[1].reset_index(drop=True)
w['m0'] = w.proj0 - w.groupby('rid').proj0.transform('mean'); w['m1'] = w.proj1 - w.groupby('rid').proj1.transform('mean')
w['top0'] = w.groupby('rid').proj0.rank(ascending=False, method='first') == 1; w['top1'] = w.groupby('rid').proj1.rank(ascending=False, method='first') == 1
trw, tew = w[w.date < '2026-01-01'], w[w.date >= '2026-01-01']
print('train (2025 OOS) races', trw.rid.nunique(), '| test (2026) races', tew.rid.nunique())
for lab, mask_fn in (('all races', lambda d: d), ('races with earlier GPS for most runners', lambda d: d[d.groupby('rid').n_gps.transform(lambda s: (s > 0).mean()) >= .5]), ('hard to separate: top 2 Proj within 3 pts', None)):
    if mask_fn is None: continue
    tw = mask_fn(tew); trr = mask_fn(trw)
    res_ = {}
    for tag, cols in (('Proj shipped', ['m0']), ('Proj + GPS', ['m1']), ('market', ['lp']), ('market + Proj shipped', ['lp', 'm0']), ('market + Proj + GPS', ['lp', 'm1'])):
        par, ll = fitll(trr, tw, cols); res_[tag] = ll
        tp = tw[tw.win == 1]
        extra = ''
        if tag == 'Proj shipped': extra = f' top pick wins {100 * tw[tw.top0 & (tw.win == 1)].shape[0] / tw.rid.nunique():.1f}%'
        if tag == 'Proj + GPS': extra = f' top pick wins {100 * tw[tw.top1 & (tw.win == 1)].shape[0] / tw.rid.nunique():.1f}%'
        print(f'  [{lab}] {tag:24s} races={len(ll):5d} winner LL {ll.mean():.4f} weights {np.round(par, 3).tolist()}{extra}')
    for a_, b_ in (('Proj shipped', 'Proj + GPS'), ('market + Proj shipped', 'market + Proj + GPS')):
        d = res_[b_] - res_[a_]; print(f'    {b_} minus {a_}: {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})')
# top-4 capture: among actual top-4 finishers in the available runners, share the model ranks in its own top 4
print('\nTOP 4 (races with >= 8 Proj runners): of the 4 best finishers, how many does each Proj put in its top 4 of the available runners')
t4 = tew[tew.groupby('rid').rid.transform('size') >= 8].copy()
t4['fin'] = t4.positionFinish
for tag, c in (('shipped', 'proj0'), ('+GPS', 'proj1')):
    rk = t4.groupby('rid')[c].rank(ascending=False, method='first'); fr = t4.groupby('rid').fin.rank(method='first')
    hit = ((rk <= 4) & (fr <= 4)).groupby(t4.rid).sum()
    print(f'  {tag:8s} races {len(hit)} mean overlap {hit.mean():.4f} of 4')
    if tag == 'shipped': h0 = hit
    else:
        d = hit - h0; print(f'  difference {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f})')
