"""Per-runner Proj breakdown (6 Nov 2026, owner's request: "when I do the form by hand I can't get close to the Proj").

Splits a runner's Proj into steps a person can follow, all on the runner-page ATW scale (data/tr_form, as TopRate gives the ratings):

  l3     clean last-3 average (the by-hand start; a run more than 12 below the median of the last six is dropped as junk)
  wt     recency weighting: weighted average of the last six clean runs minus l3
  reg    regression to the typical level (the weights sum to about 0.94 and there is an intercept)
  days   days since the last run
  dg     distance and going: change since last run, plus the horse's own record at this distance (+-200m) and this wet/dry going
  wgt    weight carried against last start
  cls    class: prize money against the horse's usual
  trend  trend and last run: last run against the run before, a big beating (8+ lengths) last start, few clean runs
  mc     everything else the Proj model adds (jockey, trainer, field strength, venue, similar-run weighting, calibration): Proj minus the formula

l3 + wt + reg + days + dg + wgt + cls + trend = the transparent formula `tf`; tf + mc = Proj exactly.
The formula is a Huber linear fit (models_tr/transparent.json). Held out (fit before 2026, 64,610 runs of 2026): RMSE 8.69 against 8.93 for
the clean last-3 average and 8.38 for the model, so the model step `mc` is usually small but not always (mean |mc| 1.6, 14% of runners above 3).
One row builder (`row_features`) serves training and the live path, so they cannot drift apart.

Train:  PYTHONPATH=. python projection/breakdown.py --train [--holdout]   (--holdout fits before 2026-01-01 and prints the 2026 scores, writes nothing)
"""
import json, os, re, sys
import numpy as np, pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
MODEL = os.path.join(HERE, 'models_tr', 'transparent.json')
LAGS = [f'c{k}' for k in range(1, 7)]
FE = LAGS + ['dlog', 'dist_chg', 'dist_chg_abs', 'wt_chg', 'gn_chg', 'lp_vs_usual', 'dist_rec', 'going_rec', 'trend', 'big_beat', 'few']
GROUPS = {
    'days': ['dlog'],
    'dg': ['dist_chg', 'dist_chg_abs', 'gn_chg', 'dist_rec', 'going_rec'],
    'wgt': ['wt_chg'],
    'cls': ['lp_vs_usual'],
    'trend': ['trend', 'big_beat', 'few'],
}
JUNK_GAP = 12.0


def going_num(s):
    m = re.search(r'(\d+)', str(s))
    return float(m.group(1)) if m else np.nan


def _day(x):
    return int(np.datetime64(str(x)[:10], 'D').astype('int64'))


def row_features(h, t):
    """h: dict of arrays (oldest first, all strictly before the race): w, day, dist, gn, lp, wt, mar. t: dict day, dist, gn, lp, wt. Needs 3+ earlier runs."""
    w = h['w']
    lag = w[-6:][::-1]
    med = float(np.median(lag))
    clean = lag[lag >= med - JUNK_GAP]
    c = np.full(6, np.nan)
    c[:min(6, len(clean))] = clean[:6]
    c = np.where(np.isnan(c), clean.mean(), c)
    last = len(w) - 1
    f = {f'c{k + 1}': c[k] for k in range(6)}
    f['dlog'] = float(np.log1p(np.clip(t['day'] - h['day'][-1], 0, 400)))
    dc = np.clip((t['dist'] - h['dist'][-1]) / 100.0, -8, 8) if np.isfinite(t['dist']) else 0.0
    f['dist_chg'] = float(dc)
    f['dist_chg_abs'] = float(abs(dc))
    d = t['wt'] - h['wt'][-1]
    f['wt_chg'] = float(np.clip(d, -6, 6)) if np.isfinite(d) else 0.0
    d = t['gn'] - h['gn'][-1]
    f['gn_chg'] = float(np.clip(d, -4, 4)) if np.isfinite(d) else 0.0
    lp6 = h['lp'][-6:]
    usual = np.nanmean(lp6) if np.isfinite(lp6).any() else np.nan
    d = t['lp'] - usual
    f['lp_vs_usual'] = float(np.clip(d, -2, 2)) if np.isfinite(d) else 0.0
    ww = w[-12:]
    base = float(np.median(ww))
    sd = np.abs(h['dist'][-12:] - t['dist']) <= 200
    wet_t = 1.0 if (np.isfinite(t['gn']) and t['gn'] >= 5) else 0.0
    sw = (h['gn'][-12:] >= 5).astype(float) == wet_t
    f['dist_rec'] = float((ww[sd] - base).sum() / (sd.sum() + 3))
    f['going_rec'] = float((ww[sw] - base).sum() / (sw.sum() + 3))
    f['trend'] = float(np.clip(w[-1] - w[-6:-1].mean(), -25, 25)) if len(w) >= 2 else 0.0
    m = h['mar'][-1]
    f['big_beat'] = 1.0 if (np.isfinite(m) and np.clip(m, 0, 20) >= 8) else 0.0
    f['few'] = 1.0 if len(clean) < 4 else 0.0
    f['_l3'] = float(clean[:3].mean())
    f['_junk'] = [round(float(x), 1) for x in lag if x < med - JUNK_GAP]
    return f


def _page_arrays():
    sys.path.insert(0, HERE)
    import features as Fe
    r = Fe.runner_page_runs().sort_values(['horse_id', 'date']).reset_index(drop=True)
    r['gn'] = r.going.map(going_num)
    r['lp'] = np.log(pd.to_numeric(r.prize, errors='coerce').clip(lower=1000))
    r['dayn'] = r.date.values.astype('datetime64[D]').astype('int64')
    out = {}
    for hid, g in r.groupby('horse_id', sort=False):
        out[int(hid)] = dict(w=g.wpr.values.astype(float), day=g.dayn.values, dist=g.distance.values.astype(float), gn=g.gn.values,
                             lp=g.lp.values, wt=pd.to_numeric(g.weightCarried, errors='coerce').values, mar=pd.to_numeric(g.marginFinish, errors='coerce').values,
                             date=g.date.values)
    return out


def _slice(h, i):
    return {k: v[:i] for k, v in h.items()}


def training_frame(arrays=None):
    arrays = arrays or _page_arrays()
    rows = []
    for hid, h in arrays.items():
        for i in range(3, len(h['w'])):
            t = dict(day=h['day'][i], dist=h['dist'][i], gn=h['gn'][i], lp=h['lp'][i], wt=h['wt'][i])
            f = row_features(_slice(h, i), t)
            f['y'] = h['w'][i]; f['date'] = h['date'][i]; f['horse_id'] = hid
            rows.append(f)
    return pd.DataFrame(rows)


def train(holdout=False):
    from sklearn.linear_model import HuberRegressor
    X = training_frame()
    cut = pd.Timestamp('2026-01-01')
    tr = X[X.date < cut] if holdout else X
    m = HuberRegressor(epsilon=1.35, alpha=1e-4, max_iter=800).fit(tr[FE], tr.y)
    meta = dict(intercept=float(m.intercept_), coef={f: float(c) for f, c in zip(FE, m.coef_)}, n_train=int(len(tr)), trained_to=str(pd.Timestamp(tr.date.max()).date()))
    if holdout:
        te = X[X.date >= cut].copy(); te['tf'] = m.predict(te[FE]); e = te.y - te.tf; e3 = te.y - te._l3
        print(f'2026 held-out {len(te):,} runs: formula RMSE {np.sqrt((e**2).mean()):.3f} MAE {e.abs().mean():.3f} | clean last-3 RMSE {np.sqrt((e3**2).mean()):.3f} MAE {e3.abs().mean():.3f}')
    else:
        json.dump(meta, open(MODEL, 'w'), indent=1); print('wrote', MODEL, meta['n_train'], 'runs to', meta['trained_to'])
    for f, c in meta['coef'].items(): print(f'  {f:13s}{c:+.3f}')
    print(f'  intercept    {meta["intercept"]:+.2f}')


_CACHE = {}


def compute(rows, proj_col='wprp_proj'):
    """rows: DataFrame with run_id, horse_id, date, distance, going, weight_carried, prize_money and the Proj. Returns {run_id: breakdown dict} for rows with 3+ earlier page runs."""
    if not os.path.exists(MODEL):
        return {}
    if 'arr' not in _CACHE:
        _CACHE['arr'] = _page_arrays(); _CACHE['m'] = json.load(open(MODEL))
    arr, mdl = _CACHE['arr'], _CACHE['m']
    co = np.array([mdl['coef'][f] for f in FE]); b0 = mdl['intercept']
    out = {}
    for r in rows.itertuples(index=False):
        try:
            h = arr.get(int(float(r.horse_id)))
            proj = float(getattr(r, proj_col))
            if h is None or not np.isfinite(proj):
                continue
            day = _day(r.date)
            n = int(np.searchsorted(h['day'], day, side='left'))     # runs strictly before the race day
            if n < 3:
                continue
            t = dict(day=day, dist=float(r.distance), gn=going_num(r.going), lp=float(np.log(max(float(r.prize_money), 1000))) if pd.notna(r.prize_money) else np.nan,
                     wt=float(r.weight_carried) if pd.notna(r.weight_carried) else np.nan)
            f = row_features(_slice(h, n), t)
            x = np.array([f[k] for k in FE])
            lag_part = float((co[:6] * x[:6]).sum()); wsum = float(co[:6].sum())
            wa = lag_part / wsum
            parts = {g: float(sum(mdl['coef'][k] * f[k] for k in ks)) for g, ks in GROUPS.items()}
            tf = b0 + float((co * x).sum())
            l3 = f['_l3']
            out[int(float(r.run_id))] = dict(l3=round(l3, 1), wt=round(wa - l3, 1), reg=round(lag_part + b0 - wa, 1), **{k: round(v, 1) for k, v in parts.items()},
                                           tf=round(tf, 1), mc=round(proj - tf, 1), junk=f['_junk'], n=n)
        except Exception:
            continue
    return out


if __name__ == '__main__':
    if '--train' in sys.argv:
        train(holdout='--holdout' in sys.argv)
    else:
        print(__doc__)
