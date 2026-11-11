"""Scores the predictions written by research/proj_improve5.py (10 Nov 2026). For each test set ('pg' = 2026 runner-page runs, 'cv' = 2026 complete converted fields) and
each prediction column: rating error (RMSE, MAE, within 3 points, median miss, bias), winner log-likelihood in races of 4+ predicted runners with one winner among them
(softmax scale cross-fitted on date halves), top pick, winner in the top 3, and the paired gain against two references (base_s1 = live settings, lr06_s1 = longer training).
Derived columns: bag_<name> (mean of the seeds present), rdmc (lr06's race level with rdm's within-race differences), cat+lr06 (average of the two learners), and for a few
columns the correction for 3+ run horses stretched by 1.1 / 1.2 / 1.3 (run.py applies 1.2 live).
Run: python research/proj_improve5_combine.py pi5 --out research/proj_improve5.json"""
import glob, json, sys
import numpy as np, pandas as pd

d = sys.argv[1]; outp = sys.argv[3] if len(sys.argv) > 3 and sys.argv[2] == '--out' else 'research/proj_improve5.json'
KEYS = ['horse_id', 'date']
res = {'info': {}}
for f in sorted(set(glob.glob(f'{d}/**/*_info.json', recursive=True) + glob.glob(f'{d}/*_info.json'))):
    res['info'].update(json.load(open(f)))
is_pred = lambda c: '_s' in c and c.split('_s')[-1].isdigit()
for test in ('pg', 'cv'):
    files = sorted(set(glob.glob(f'{d}/**/*_{test}.pkl', recursive=True) + glob.glob(f'{d}/*_{test}.pkl')))
    T, extra = None, {}
    for f in files:
        x = pd.read_pickle(f)
        pc = [c for c in x.columns if is_pred(c)]
        if any(c.startswith('h16_') for c in pc):       # other history window: rows can differ, keep apart and join on the keys
            extra[f] = x[KEYS + pc]; continue
        T = x if T is None else T.merge(x[KEYS + [c for c in pc if c not in T.columns]], on=KEYS, how='inner')
    if T is None:
        continue
    for f, x in extra.items():
        T = T.merge(x[KEYS + [c for c in x.columns if is_pred(c) and c not in T.columns]], on=KEYS, how='left')
    pc = [c for c in T.columns if is_pred(c)]
    T['rk'] = T.date.astype(str) + '|' + T.vn.astype(str) + '|' + T.distance.astype(str) + '|' + T.field_size.astype(str) + '|' + T.cls.astype(str)
    names = sorted({c.rsplit('_s', 1)[0] for c in pc})
    for nm in [x for x in names if '.R' not in x]:
        cs = [c for c in pc if c.rsplit('_s', 1)[0] == nm]
        if len(cs) > 1:
            T['bag_' + nm] = T[cs].mean(axis=1); pc.append('bag_' + nm)
    dm = lambda c: T[c] - T.groupby('rk')[c].transform('mean')
    if 'rdm_s1' in T and 'lr06_s1' in T:
        T['rdmc'] = T.lr06_s1 - dm('lr06_s1') + dm('rdm_s1'); pc.append('rdmc')
        pc.remove('rdm_s1')
    if 'cat_s1' in T and 'lr06_s1' in T:
        T['cat+lr06'] = (T.cat_s1 + T.lr06_s1) / 2; pc.append('cat+lr06')
    # stacks: X = usual target, X.R = within-race target, X.C / X.RC = the CatBoost twins
    for X in sorted({c[:-3] for c in pc if c.endswith('_s1') and '.' not in c}):
        have = lambda sfx: f'{X}{sfx}_s1' in T
        col = lambda sfx: f'{X}{sfx}_s1'
        if have('.R'):
            T[f'{X}|rdm'] = T[col('')] - dm(col('')) + dm(col('.R')); pc.append(f'{X}|rdm')
        if have('.C'):
            T[f'{X}|+cat'] = (T[col('')] + T[col('.C')]) / 2; pc.append(f'{X}|+cat')
        if have('.R') and have('.C') and have('.RC'):
            T['_L'] = (T[col('')] + T[col('.C')]) / 2; T['_D'] = (T[col('.R')] + T[col('.RC')]) / 2
            T[f'{X}|rdm+cat'] = T._L - dm('_L') + dm('_D'); pc.append(f'{X}|rdm+cat')
        if f'{X}.R_s2' in T and have('.R'):
            T['_D'] = (T[col('.R')] + T[f'{X}.R_s2']) / 2
            T[f'{X}|rdm 2 seeds'] = T[col('')] - dm(col('')) + dm('_D'); pc.append(f'{X}|rdm 2 seeds')
    if 'nocap_s1' in T:
        for cap in (3, 4, 6, 8, 10):
            T[f'few-run cap {cap}'] = np.where(T.n < 3, T.f + np.clip(T.nocap_s1 - T.f, -cap, cap), T.nocap_s1); pc.append(f'few-run cap {cap}')
    pc = [c for c in pc if not (is_pred(c) and '.R' in c.rsplit('_s', 1)[0])]      # a within-race model alone has no level
    for c in ('base_s1', 'lr06_s1', 'allx_s1', 'lr06|rdm', 'allx|rdm', 'allx|rdm+cat', 'allz|rdm'):
        if c in T:
            for s in (1.1, 1.2, 1.3):
                T[f'{c}*{s}'] = np.where(T.n >= 3, T.f + s * (T[c] - T.f), T[c]); pc.append(f'{c}*{s}')

    w = T[T.positionFinish.notna()].copy()
    w = w[w.groupby('rk').f.transform('size') >= 4]
    w = w[w.groupby('rk').positionFinish.transform(lambda s: (s == 1).sum()) == 1].reset_index(drop=True)
    code = pd.factorize(w.rk)[0]; nr = code.max() + 1
    win = (w.positionFinish == 1).values
    rdate = pd.Series(w.date.values).groupby(code).first().values
    half_r = (rdate >= w.date.median().to_datetime64()).astype(int)
    BS = np.arange(0.05, 0.6, 0.005)

    def race_ll(x, b):
        mx = np.full(nr, -np.inf); np.maximum.at(mx, code, x)
        z = b * (x - mx[code])
        s = np.bincount(code, weights=np.exp(z), minlength=nr)
        out = np.full(nr, np.nan); out[code[win]] = z[win] - np.log(s[code[win]])
        return out

    def wll(col):
        x = w[col].values
        ok_r = np.bincount(code, weights=np.isnan(x), minlength=nr) == 0
        x = np.nan_to_num(x)
        L = np.array([race_ll(x, b) for b in BS])
        out = np.full(nr, np.nan)
        for h in (0, 1):
            fit = ok_r & (half_r != h); b = np.argmax(L[:, fit].mean(axis=1)); out[ok_r & (half_r == h)] = L[b, ok_r & (half_r == h)]
        return out

    rmse = lambda e: float(np.sqrt(np.nanmean(e ** 2)))
    few = (T.n < 3).values; fu = (T.d_last > 60).values
    refs = [r for r in ('base_s1', 'lr06_s1') if r in pc] or [pc[0]]
    E = {r: (T.wpr - T[r]).values for r in refs}; SL = {r: wll(r) for r in refs}
    R = {'runs': int(len(T)), 'races': int(nr), 'runners_per_race': round(float(len(w) / nr), 2), 'references': refs}
    for c in pc:
        e = (T.wpr - T[c]).values; s = wll(c)
        x = w[c].values
        order = np.lexsort((-np.nan_to_num(x, nan=-1e9), code))
        rank = np.empty(len(w)); first = np.r_[0, np.cumsum(np.bincount(code, minlength=nr))[:-1]]
        rank[order] = np.arange(len(w)) - first[code[order]] + 1
        have = ~np.isnan(s)
        r = dict(n=int((~np.isnan(e)).sum()), rmse=round(rmse(e), 4), mae=round(float(np.nanmean(np.abs(e))), 4), within3=round(float(np.nanmean(np.abs(e[~np.isnan(e)]) <= 3)), 4),
                 median_miss=round(float(np.nanmedian(np.abs(e))), 4), bias=round(float(np.nanmean(e)), 3),
                 win_ll=round(float(np.nanmean(s)), 5), races=int(have.sum()),
                 top_pick=round(float((win & (rank == 1)).sum() / nr), 4), winner_top3=round(float((win & (rank <= 3)).sum() / nr), 4))
        for ref in refs:
            dq = E[ref] ** 2 - e ** 2; dq = dq[~np.isnan(dq)]; ds = (s - SL[ref]); ds = ds[~np.isnan(ds)]
            r['vs_' + ref] = dict(sq_gain=round(float(dq.mean()), 4), sq_se=round(float(dq.std() / np.sqrt(len(dq))), 4),
                                  win_ll_gain=round(float(ds.mean()), 5), win_ll_se=round(float(ds.std() / np.sqrt(len(ds))), 5) if len(ds) > 1 else 0.0)
            hd = (s - SL[ref])
            r['vs_' + ref]['win_ll_gain_halves'] = [round(float(np.nanmean(hd[half_r == h])), 5) for h in (0, 1)]
        ref = refs[-1]
        for lab, m in (('1-2 runs', few), ('first-up', fu)):
            dq = (E[ref] ** 2 - e ** 2)[m]; dq = dq[~np.isnan(dq)]
            r[lab] = dict(n=int(m.sum()), rmse=round(rmse(e[m]), 3), rmse_ref=round(rmse(E[ref][m]), 3), sq_gain=round(float(dq.mean()), 4) if len(dq) else None,
                          se=round(float(dq.std() / np.sqrt(max(len(dq), 1))), 4) if len(dq) else None)
        R[c] = r
        g = r['vs_' + refs[-1]]
        print(f"{test} {c:14s} rmse {r['rmse']:.4f} mae {r['mae']:.4f} w3 {r['within3']:.4f} med {r['median_miss']:.3f} | win_ll {r['win_ll']:.5f} top {r['top_pick']:.4f} top3 {r['winner_top3']:.4f}"
              f" | vs {refs[-1]}: sq {g['sq_gain']:+.4f} ({g['sq_se']:.4f}) ll {g['win_ll_gain']:+.5f} ({g['win_ll_se']:.5f}) halves {g['win_ll_gain_halves']}", flush=True)
    res[test] = R
json.dump(res, open(outp, 'w'), indent=1)
print('wrote', outp)
