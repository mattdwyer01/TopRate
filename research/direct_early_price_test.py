"""Direct model v2 against EARLY fixed prices (26 Oct 2026). T2 = complete real page-scale fields from data/direct_log scored by the saved v2 models
(/tmp/direct_v2_T2.pkl, written by direct_finish_v2.py); prices = bet_signal_log.csv.gz (every pass within 90 min of the jump), per runner the last
pass made at least MINS minutes before the jump. Clean-book races only (every runner priced, book 1.05 to 2.0). Reports price-only vs price+model
winner log-lik (conditional logit cross-fitted on date halves), flat ROI by model rank and by EV (blended chance x price) with robustness."""
import numpy as np, pandas as pd
from scipy.optimize import minimize

T = pd.read_pickle('/tmp/direct_v2_T2.pkl')
T = T[T.logged.notna()] if 'logged' in T else T
B = pd.read_csv('bet_signal_log.csv.gz')
import runners_io
_r = runners_io.read_runners()[['run_id', 'race_id', 'horse_id']].drop_duplicates('run_id')
B = B.merge(_r[['run_id', 'horse_id']], on='run_id', how='inner')


def cond_logit(df, cols_, key):
    sizes = df.groupby(key, sort=False).size().values
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    X = df[cols_].values; y = df.win.values

    def nll(b):
        s = X @ b
        m = np.repeat(np.maximum.reduceat(s, starts), sizes)
        lse = np.log(np.add.reduceat(np.exp(s - m), starts))
        return -(s[y == 1] - m[y == 1] - lse).mean()
    return minimize(nll, np.ones(len(cols_)) * 0.5, method='BFGS').x


def apply_cl(df, cols_, b, key):
    s = pd.Series(df[cols_].values @ b, index=df.index)
    e = np.exp(s - s.groupby(df[key]).transform('max'))
    return e / e.groupby(df[key]).transform('sum')


def run(mins, model):
    b = B[B.mins >= mins].sort_values('mins').groupby('run_id').head(1)[['race_id', 'horse_id', 'price', 'mins']].rename(columns={'price': 'pr'})
    d = T.merge(b, on=['race_id', 'horse_id'], how='inner')
    key = 'race_id'
    d['pr'] = pd.to_numeric(d.pr, errors='coerce')
    ok = d.groupby(key).pr.transform(lambda s: s.notna().all() and 1.05 <= (1 / s).sum() <= 2.0)
    n_all = d[key].nunique()
    d = d[ok].reset_index(drop=True)
    d['win'] = d.won.astype(int)
    d = d[d.groupby(key).win.transform('sum') == 1].reset_index(drop=True)
    # require the model prob to exist for the whole race
    d['pm'] = d[model] / d.groupby(key)[model].transform('sum')
    ip = 1 / d.pr
    d['mk'] = ip / ip.groupby(d[key]).transform('sum')
    d['lmk'] = np.log(d.mk); d['lm'] = np.log(d.pm.clip(1e-9))
    half = (d.date >= d.date.median()).values
    out = pd.Series(np.nan, index=d.index); co = []
    for a_, b_ in ((~half, half), (half, ~half)):
        bc = cond_logit(d[a_], ['lmk', 'lm'], key); co.append(bc)
        out[b_] = apply_cl(d[b_], ['lmk', 'lm'], bc, key)
    w = d.win == 1
    gain = np.log(out[w].clip(1e-9)) - np.log(d.mk[w].clip(1e-9))
    nr = d[key].nunique()
    print(f'\n== early price: last pass >= {mins} min before the jump, model {model}: {nr} clean-book races (of {n_all} overlapping), mean {d.mins.mean():.0f} min out')
    print(f'  price only LL {np.log(d.mk[w]).mean():.4f}  price+model {np.log(out[w].clip(1e-9)).mean():.4f}  gain {gain.mean():+.4f} (se {gain.std() / np.sqrt(len(gain)):.4f})  weights price {np.mean([c[0] for c in co]):.2f} model {np.mean([c[1] for c in co]):.2f}')
    d['pb'] = out; d['ev'] = d.pb * d.pr; d['ret'] = np.where(d.win == 1, d.pr - 1, -1.0)
    d['rk'] = d.groupby(key).pm.rank(ascending=False, method='first')
    print('  rank (model): n, win%, avg price, flat ROI')
    for r in (1, 2, 3, 4):
        s = d[d.rk == r]; print(f'    {r}: {len(s)}  {s.win.mean():.1%}  ${s.pr.mean():.2f}  {s.ret.mean():+.1%}')
    print('  model chance vs price-implied chance for rank 1: model', f'{d[d.rk == 1].pm.mean():.3f}', 'market', f'{d[d.rk == 1].mk.mean():.3f}', 'actual', f'{d[d.rk == 1].win.mean():.3f}')
    print('  overlays on the blended chance (EV = blended p x early price):')
    for thr in (1.0, 1.05, 1.10, 1.20):
        s = d[d.ev > thr]
        if len(s):
            h = s.date >= d.date.median()
            ex = s.ret.drop(s.ret.nlargest(3).index).mean() if len(s) > 3 else np.nan
            print(f'    EV>{thr:.2f}: n={len(s)} win {s.win.mean():.1%} avg ${s.pr.mean():.2f} ROI {s.ret.mean():+.1%} halves {s[~h].ret.mean():+.1%}/{s[h].ret.mean():+.1%} ex3 {ex:+.1%}')
    # model-only overlays: model chance vs market at the early price (unblended)
    d['ev_m'] = d.pm * d.pr
    for thr in (1.2, 1.5):
        s = d[(d.ev_m > thr) & (d.rk <= 4)]
        if len(s):
            ex = s.ret.drop(s.ret.nlargest(3).index).mean() if len(s) > 3 else np.nan
            print(f'    raw model EV>{thr:.1f} within model top 4: n={len(s)} win {s.win.mean():.1%} avg ${s.pr.mean():.2f} ROI {s.ret.mean():+.1%} ex3 {ex:+.1%}')


for m in (5, 30):
    for model in ('p_B3', 'p_avg'):
        run(m, model)
