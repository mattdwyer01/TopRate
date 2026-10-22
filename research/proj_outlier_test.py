"""Should clear outlier runs be dropped or pulled in before the Proj formula (22 Oct 2026)? Runner-page ATW ratings only (data/tr_form, owner rule).
Baseline = the shipped formula form (intercept + weights on the last 8 runs, one set per count of earlier runs), fitted before 2026-01-01, scored 2026-01+.
Variants clip each earlier run to the horse's median of its last 6 earlier runs +- T (low side only, or both sides); weights are REFITTED on the clipped inputs.
Also: residual of the baseline by how far the last run sits below / above the median of the runs before it. Run with PYTHONPATH=."""
import numpy as np
import pandas as pd
from projection import features as F

K = 8
rp = F.runner_page_runs().sort_values(['horse_id', 'date']).reset_index(drop=True)
g = rp.groupby('horse_id')
for k in range(1, K + 1):
    rp[f'r{k}'] = g.wpr.shift(k)
rp['n'] = g.cumcount()
R = rp[[f'r{k}' for k in range(1, K + 1)]].values
med = np.nanmedian(R[:, :6], axis=1)
rp['med'] = med
train = rp.date < '2026-01-01'
test = rp.date >= '2026-01-01'


def fit_eval(cols_fn, label, mask_eval=None):
    se, cnt, se_sub, cnt_sub = 0.0, 0, 0.0, 0
    for n in range(2, K + 1):
        m = rp.n.clip(upper=K) == n
        Xall = cols_fn(n)
        ok = m & ~np.isnan(Xall).any(axis=1) & rp.wpr.notna()
        tr = ok & train
        te = ok & test
        A = np.c_[np.ones(tr.sum()), Xall[tr.values]]
        w = np.linalg.lstsq(A, rp.wpr[tr].values, rcond=None)[0]
        pred = np.c_[np.ones(te.sum()), Xall[te.values]] @ w
        err = rp.wpr[te].values - pred
        se += (err ** 2).sum(); cnt += len(err)
        if mask_eval is not None:
            sub = mask_eval[te.values]
            se_sub += (err[sub] ** 2).sum(); cnt_sub += sub.sum()
    out = f'{label:46s} RMSE {np.sqrt(se / cnt):.4f} (n {cnt})'
    if cnt_sub:
        out += f'   flagged-subset RMSE {np.sqrt(se_sub / cnt_sub):.4f} (n {cnt_sub})'
    print(out)


def base(n):
    return R[:, :n]


def clip(T, both):
    def f(n):
        X = R[:, :n].copy()
        lo = med[:, None] - T
        X = np.where(X < lo, lo, X)
        if both:
            hi = med[:, None] + T
            X = np.where(X > hi, hi, X)
        return X
    return f


def drop_to_med(T):
    def f(n):
        X = R[:, :n].copy()
        return np.where(X < med[:, None] - T, med[:, None], X)
    return f


# flagged = any of the last 8 earlier runs more than 10 below the median of the last 6
flag10 = (R < (med[:, None] - 10)).any(axis=1)
print('runs with a flagged low earlier run (10 below median):', f'{flag10[test.values & (rp.n >= 3).values].mean():.1%}')
fit_eval(base, 'baseline (as shipped)', flag10)
for T in (8, 10, 15):
    fit_eval(clip(T, False), f'clip low runs to median-{T}', flag10)
    fit_eval(clip(T, True), f'clip both sides to median+-{T}', flag10)
fit_eval(drop_to_med(10), 'replace runs >10 below median with the median', flag10)

# rebound: baseline residual by last-run deviation from the median of the runs before it
base_w = {}
res = pd.Series(np.nan, index=rp.index)
for n in range(2, K + 1):
    m = (rp.n.clip(upper=K) == n) & ~np.isnan(R[:, :n]).any(axis=1) & rp.wpr.notna()
    A = np.c_[np.ones((m & train).sum()), R[(m & train).values, :n]]
    w = np.linalg.lstsq(A, rp.wpr[m & train].values, rcond=None)[0]
    idx = m & test
    res[idx] = rp.wpr[idx].values - np.c_[np.ones(idx.sum()), R[idx.values, :n]] @ w
prev_med = np.nanmedian(R[:, 1:7], axis=1)  # median of the runs before the last one
dev = R[:, 0] - prev_med
d = pd.DataFrame({'dev': dev, 'res': res, 'n': rp.n}).dropna()
d = d[d.n >= 4]
bins = [-99, -20, -15, -10, -5, 5, 10, 15, 99]
d['b'] = pd.cut(d.dev, bins)
print('\nBaseline residual (actual minus formula) by how far the LAST run sat from the median of the runs before it (2026 holdout, 4+ earlier runs):')
print(d.groupby('b', observed=True).res.agg(['count', 'mean', lambda x: x.std() / np.sqrt(len(x))]).rename(columns={'<lambda_0>': 'se'}).round(2))
