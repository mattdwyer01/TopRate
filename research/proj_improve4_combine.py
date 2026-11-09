"""Scores the predictions written by research/proj_improve4.py (9 Nov 2026). For each test set ('pg' = 2026 runner-page runs, the races as the page store holds them;
'cv' = 2026 complete fields from the results files on the page scale) and each prediction column, plus 'bag_base' / 'bag_all' (mean of the seeds present): rating error
(RMSE, MAE, share within 3 points, median miss), winner log-likelihood in races with 4+ predicted runners and the winner among them (softmax scale cross-fitted on date
halves), top pick, winner in the top 3, and the paired gain against base_s1 (squared error and winner log-lik with standard errors), overall and for horses with 1 to 2
earlier runs and first-up runners.
Run: python research/proj_improve4_combine.py research/pi4 [--out research/proj_improve4.json]"""
import glob, json, sys
import numpy as np, pandas as pd

d = sys.argv[1]; outp = sys.argv[3] if len(sys.argv) > 3 and sys.argv[2] == '--out' else 'research/proj_improve4.json'
KEYS = ['horse_id', 'date']
res = {'info': {}}
for f in glob.glob(f'{d}/**/*_info.json', recursive=True) + glob.glob(f'{d}/*_info.json'):
    res['info'].update(json.load(open(f)))
for test in ('pg', 'cv'):
    files = sorted(set(glob.glob(f'{d}/**/*_{test}.pkl', recursive=True) + glob.glob(f'{d}/*_{test}.pkl')))
    if not files:
        continue
    T = None
    for f in files:
        x = pd.read_pickle(f)
        pc = [c for c in x.columns if '_s' in c and c.split('_s')[-1].isdigit()]
        if T is None:
            T = x
        else:
            T = T.merge(x[KEYS + [c for c in pc if c not in T.columns]], on=KEYS, how='inner')
    pc = [c for c in T.columns if '_s' in c and c.split('_s')[-1].isdigit()]
    for grp in ('base', 'all'):
        cs = [c for c in pc if c.startswith(grp + '_s')]
        if len(cs) > 1:
            T['bag_' + grp] = T[cs].mean(axis=1); pc.append('bag_' + grp)
    T['rk'] = T.date.astype(str) + '|' + T.vn.astype(str) + '|' + T.distance.astype(str) + '|' + T.field_size.astype(str) + '|' + T.cls.astype(str)
    w = T[T.positionFinish.notna()].copy()
    w = w[w.groupby('rk').f.transform('size') >= 4]
    w = w[w.groupby('rk').positionFinish.transform(lambda s: (s == 1).sum()) == 1]
    w['half'] = (w.date >= w.date.median()).astype(int)

    def wll(col):
        def ll(df, b):
            z = b * (df[col] - df.groupby('rk')[col].transform('max'))
            return (z - np.log(np.exp(z).groupby(df.rk).transform('sum')))[df.positionFinish == 1]
        out = []
        for h in (0, 1):
            bs = np.arange(0.05, 0.6, 0.005); b = bs[np.argmax([ll(w[w.half != h], b).mean() for b in bs])]; out.append(ll(w[w.half == h], b))
        return pd.concat(out).sort_index()
    rmse = lambda e: float(np.sqrt((e ** 2).mean()))
    few = (T.n < 3).values; fu = (T.d_last > 60).values
    base = 'base_s1' if 'base_s1' in pc else pc[0]
    eb = T.wpr - T[base]; sb = wll(base)
    R = {'runs': int(len(T)), 'races': int(w.rk.nunique()), 'runners_per_race': round(float(w.groupby('rk').size().mean()), 2), 'reference': base}
    for c in pc:
        e = T.wpr - T[c]; s = wll(c)
        top = w.loc[w.groupby('rk')[c].idxmax()]
        rank = w.groupby('rk')[c].rank(ascending=False, method='first')
        dq = eb ** 2 - e ** 2; ds = (s - sb).dropna()
        r = dict(rmse=round(rmse(e), 4), mae=round(float(e.abs().mean()), 4), within3=round(float((e.abs() <= 3).mean()), 4), median_miss=round(float(e.abs().median()), 4),
                 win_ll=round(float(s.mean()), 5), top_pick=round(float((top.positionFinish == 1).mean()), 4),
                 winner_top3=round(float(((rank <= 3) & (w.positionFinish == 1)).sum() / w.rk.nunique()), 4),
                 sq_gain=round(float(dq.mean()), 4), sq_se=round(float(dq.std() / np.sqrt(len(dq))), 4),
                 win_ll_gain=round(float(ds.mean()), 5), win_ll_se=round(float(ds.std() / np.sqrt(len(ds))), 5) if len(ds) > 1 else 0.0)
        for lab, m in (('1-2 runs', few), ('first-up', fu)):
            r[lab] = dict(n=int(m.sum()), rmse=round(rmse(e[m]), 3), rmse_ref=round(rmse(eb[m]), 3), sq_gain=round(float(dq[m].mean()), 4),
                          se=round(float(dq[m].std() / np.sqrt(max(m.sum(), 1))), 4))
        R[c] = r
        print(test, c, {k: v for k, v in r.items() if not isinstance(v, dict)}, flush=True)
    res[test] = R
json.dump(res, open(outp, 'w'), indent=1)
print('wrote', outp)
