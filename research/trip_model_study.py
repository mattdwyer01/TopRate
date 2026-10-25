"""Richer trip (early position) model, tested on contenders and the full field (24 Oct 2026 idea, see CLAUDE.md).

Question: does a better pre-race forecast of where each runner will be at 800m from home add to winner prediction beyond
the rating and the price? Built from the results files only (all tracks, 2016 to 8 Oct 2026), no GPS.

  python research/trip_model_study.py            # builds features, trains base and rich models, prints accuracy and winner tests

Two feature sets:
  base : track, distance, barrier, field size, rail, going + the horse's own last 3 / 8 early positions (what trip_map used)
  rich : base + track x distance x barrier-fraction cell, horse's history at this distance band and track, run-style spread,
         last run, rivals' early-speed profile (leaders in the field, field tempo, own rank among them), jockey early
         tendency (day-lagged), days since run, weight, class, age/sex.
Everything is strictly pre-race (history shifted, jockey effect lagged a day, rivals use their own prior runs).
Winner test: conditional logit inside each race on log price + stand-in rating (mean of last 3 earlier wpr) + trip terms.
"""
import glob
import os
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from scipy.optimize import minimize

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
TRAIN_END = pd.Timestamp('2025-01-01')
TEST_FROM = pd.Timestamp('2025-07-01')
PARAMS = dict(objective='regression', learning_rate=0.05, num_leaves=63, min_data_in_leaf=200, feature_fraction=0.8,
              bagging_fraction=0.8, bagging_freq=1, verbose=-1, num_threads=4)
ROUNDS = int(os.environ.get('TRIP_ROUNDS', 500))


def load():
    cols = ['race_id', 'horse_id', 'date', 'track', 'distance', 'going', 'barrier', 'field_size', 'position800m', 'margin800m',
            'rail_position', 'wpr', 'isBarrierTrial', 'is_jumpout', 'positionFinish', 'priceStarting', 'jockey', 'weightCarried',
            'race_class', 'horse_age', 'horse_sex', 'raceNumber']
    fs = [f for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20*.csv.gz'))) if not f.endswith('_rc.csv.gz')]
    d = pd.concat([pd.read_csv(f, usecols=lambda c: c in set(cols), low_memory=False) for f in fs], ignore_index=True)
    d = d[(~d.isBarrierTrial.astype(bool)) & (~d.is_jumpout.fillna(False).astype(bool))].copy()
    d = d[~d.race_class.astype(str).str.contains('Hurdle|Steeple', case=False, na=False)]
    d = d.drop_duplicates(['race_id', 'horse_id'])
    d['date'] = pd.to_datetime(d.date)
    d = d[(d.field_size >= 5) & (d.barrier > 0)].copy()
    d['fs'] = d.field_size
    d['barfrac'] = (d.barrier - 1) / (d.fs - 1).clip(lower=1)
    d['settle'] = (d.position800m - 1) / (d.fs - 1).clip(lower=1)
    d['gap800'] = d.margin800m.clip(0, 30)
    s = d.rail_position.astype(str)
    d['rail_m'] = np.where(s.str.contains('True'), 0.0, pd.to_numeric(s.str.extract(r'(\d+)\s*m')[0], errors='coerce'))
    d['going_s'] = pd.to_numeric(d.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    d['band'] = pd.cut(d.distance, [0, 1150, 1450, 1850, 2300, 9999], labels=False)
    d['trk'] = d.track.astype('category')
    d['cell'] = (d.track.astype(str) + '|' + d.distance.astype(str)).astype('category')
    d['cls'] = d.race_class.astype('category')
    d['sex'] = d.horse_sex.astype('category')
    d['jock'] = d.jockey.astype(str)
    return d.sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)


def lagmean(g, col, k_max, min_n, k_min=1):
    """Mean of the previous k_min..k_max values of col within horse (NaN skipped)."""
    arr = np.column_stack([g[col].shift(k) for k in range(k_min, k_max + 1)])
    n = np.isfinite(arr).sum(1)
    with np.errstate(all='ignore'):
        m = np.nanmean(arr, 1)
    m[n < min_n] = np.nan
    return m


def add_features(d):
    g = d.groupby('horse_id')
    for t in ('settle', 'gap800'):
        d[t + '_l1'] = g[t].shift(1)
        d[t + '_h3'] = lagmean(g, t, 3, 1)
        d[t + '_h8'] = lagmean(g, t, 8, 2)
    arr = np.column_stack([g['settle'].shift(k) for k in range(1, 9)])
    with np.errstate(all='ignore'):
        d['settle_sd8'] = np.where(np.isfinite(arr).sum(1) >= 3, np.nanstd(arr, 1), np.nan)
    d['n_hist'] = g.cumcount()
    d['days'] = (d.date - g.date.shift(1)).dt.days
    # horse's earlier runs at this distance band, and at this track (expanding, excludes the run itself)
    for key, nm in (('band', 'band'), ('track', 'trk')):
        gg = d.groupby(['horse_id', key])
        x = d.settle
        ok = x.notna()
        cs = x.fillna(0).groupby([d.horse_id, d[key]]).cumsum() - x.fillna(0)
        cn = ok.groupby([d.horse_id, d[key]]).cumsum() - ok.astype(int)
        d['settle_' + nm + '_h'] = np.where(cn >= 1, cs / cn.replace(0, np.nan), np.nan)
        d['n_' + nm + '_h'] = cn
    d['wpr_l1'] = g.wpr.shift(1)
    d['r3'] = lagmean(g, 'wpr', 3, 2)
    d['wt_chg'] = d.weightCarried - g.weightCarried.shift(1)
    # jockey early tendency: how far the jockey's mounts settle ahead of their own horses' usual position, lagged one day
    resid = (d.settle - d.settle_h8)
    jd = pd.DataFrame({'jock': d.jock, 'date': d.date, 'r': resid}).dropna()
    ja = jd.groupby(['jock', 'date']).r.agg(['sum', 'count']).reset_index().sort_values(['jock', 'date'])
    ja['cs'] = ja.groupby('jock')['sum'].cumsum() - ja['sum']
    ja['cn'] = ja.groupby('jock')['count'].cumsum() - ja['count']
    ja['jock_early'] = ja.cs / (ja.cn + 30)
    d = d.merge(ja[['jock', 'date', 'jock_early', 'cn']].rename(columns={'cn': 'jock_n'}), on=['jock', 'date'], how='left')
    # rivals: leaders in the field, field tempo, own rank
    r = d.groupby('race_id')
    d['own_rel'] = d.settle_h3 - r.settle_h3.transform('mean')
    d['n_lead3'] = (d.settle_h3 <= 0.25).groupby(d.race_id).transform('sum')
    d['n_lead8'] = (d.settle_h8 <= 0.25).groupby(d.race_id).transform('sum')
    d['tempo_gap'] = r.gap800_h3.transform('mean')
    d['tempo_set'] = r.settle_h3.transform('mean')
    d['own_rank'] = r.settle_h3.rank(method='min')
    d['rank_frac'] = d.own_rank / r.settle_h3.transform('count').clip(lower=1)
    d['field_known'] = r.settle_h3.transform('count') / d.fs
    d['bar_x_lead'] = d.barfrac * d.n_lead3
    d['wt_rel'] = d.weightCarried - r.weightCarried.transform('mean')
    d['r3_rel'] = d.r3 - r.r3.transform('mean')
    return d


BASE = ['trk', 'distance', 'barrier', 'barfrac', 'fs', 'rail_m', 'going_s',
        'settle_h3', 'settle_h8', 'gap800_h3', 'gap800_h8', 'own_rel', 'n_lead3']
RICH = BASE + ['cell', 'band', 'settle_l1', 'gap800_l1', 'settle_sd8', 'n_hist', 'days', 'settle_band_h', 'n_band_h', 'settle_trk_h', 'n_trk_h',
               'jock_early', 'jock_n', 'n_lead8', 'tempo_gap', 'tempo_set', 'own_rank', 'rank_frac', 'field_known', 'bar_x_lead',
               'weightCarried', 'wt_chg', 'wt_rel', 'cls', 'horse_age', 'sex', 'wpr_l1', 'r3_rel']


def fit(train, valid, feats, target):
    ok = train[target].notna()
    va = valid[target].notna()
    ds = lgb.Dataset(train.loc[ok, feats], train.loc[ok, target])
    dv = lgb.Dataset(valid.loc[va, feats], valid.loc[va, target])
    return lgb.train(PARAMS, ds, ROUNDS, valid_sets=[dv], callbacks=[lgb.early_stopping(40, verbose=False)])


def within_corr(df, pred, target):
    x = pd.DataFrame({'race_id': df.race_id.values, 'p': pred.values, 'y': df[target].values}).dropna()
    x['p'] -= x.groupby('race_id').p.transform('mean')
    x['y'] -= x.groupby('race_id').y.transform('mean')
    return float(np.corrcoef(x.p, x.y)[0, 1]), float(np.sqrt(((x.p - x.y) ** 2).mean())), len(x)


# ---------------------------------------------------------------- winner test (conditional logit inside race)
def clogit(blocks, cols):
    """blocks: list of (X [n,k], win index). Maximise sum log softmax at the winner."""
    k = len(cols)

    def f(b):
        ll = 0.0
        gr = np.zeros(k)
        for X, w in blocks:
            u = X @ b
            m = u.max()
            e = np.exp(u - m)
            s = e.sum()
            ll += u[w] - m - np.log(s)
            gr += X[w] - (e[:, None] * X).sum(0) / s
        return -ll, -gr

    res = minimize(f, np.zeros(k), jac=True, method='BFGS')
    return res.x, -res.fun


def make_blocks(df, cols):
    blocks = []
    for _, z in df.groupby('race_id', sort=False):
        w = np.flatnonzero(z.win.values == 1)
        if len(w) != 1:
            continue
        blocks.append((z[cols].values.astype(float), int(w[0])))
    return blocks


def winner_test(te, label_sets, contenders=None):
    """te has per-runner: lnp, r3_rel, and trip columns. contenders=None for the full field else top-N by r3."""
    z = te.copy()
    if contenders:
        z = z[z.r3_rank <= contenders]
    out = {}
    for name, cols in label_sets.items():
        blocks = make_blocks(z, cols)
        # races where the winner is in the set only (blocks built from rows present; winner missing => skipped)
        b, ll = clogit(blocks, cols)
        out[name] = (b, ll / len(blocks), len(blocks))
    return out


def main():
    print('loading ...', flush=True)
    d = add_features(load())
    print('runs', len(d), flush=True)
    tr = d[(d.date >= '2018-01-01') & (d.date < '2024-07-01')]
    va = d[(d.date >= '2024-07-01') & (d.date < TRAIN_END)]
    te = d[(d.date >= TEST_FROM)].copy()
    models = {}
    for tgt in ('gap800', 'settle'):
        for nm, feats in (('base', BASE), ('rich', RICH)):
            models[(nm, tgt)] = fit(tr, va, feats, tgt)
            te[f'{nm}_{tgt}'] = models[(nm, tgt)].predict(te[feats])
            print(nm, tgt, 'trees', models[(nm, tgt)].best_iteration, flush=True)
    print('\n=== early-position accuracy, held out 2025-07 on, fields of 8+ (within-race corr / RMSE / n) ===')
    t8 = te[te.fs >= 8]
    for tgt in ('gap800', 'settle'):
        for nm in ('base', 'rich'):
            c, r, n = within_corr(t8, t8[f'{nm}_{tgt}'], tgt)
            print(f'{tgt:7s} {nm:5s} corr {c:.3f}  rmse {r:.3f}  n {n}')
    print('\nby distance band (settle corr base -> rich):')
    for b, z in t8.groupby('band'):
        print(int(b), round(within_corr(z, z.base_settle, 'settle')[0], 3), '->', round(within_corr(z, z.rich_settle, 'settle')[0], 3), len(z))
    print('top tracks (settle corr base -> rich):')
    for trk, z in t8.groupby('track'):
        if len(z) > 3000:
            print(f'{trk:20s}', round(within_corr(z, z.base_settle, 'settle')[0], 3), '->', round(within_corr(z, z.rich_settle, 'settle')[0], 3), len(z))

    print('\n=== by track x distance cell (settle, held out 2025-07 on, fields of 8+) ===')
    rows = []
    for cell, z in t8.groupby('cell', observed=True):
        if len(z) >= 300:
            cb = within_corr(z, z.base_settle, 'settle')[0]
            cr = within_corr(z, z.rich_settle, 'settle')[0]
            rows.append((str(cell), len(z), cb, cr))
    cdf = pd.DataFrame(rows, columns=['cell', 'n', 'base', 'rich'])
    cdf['gain'] = cdf.rich - cdf.base
    print(f'cells with 300+ test runs: {len(cdf)}; rich better in {(cdf.gain > 0).sum()}, worse in {(cdf.gain < 0).sum()}; '
          f'median corr base {cdf.base.median():.3f} rich {cdf.rich.median():.3f}; mean gain {cdf.gain.mean():+.3f}')
    print('weakest cells for the rich model:'); print(cdf.sort_values('rich').head(12).round(3).to_string(index=False))
    print('strongest cells:'); print(cdf.sort_values('rich').tail(8).round(3).to_string(index=False))
    print('biggest gains:'); print(cdf.sort_values('gain').tail(8).round(3).to_string(index=False))
    print('biggest losses:'); print(cdf.sort_values('gain').head(8).round(3).to_string(index=False))
    cdf.to_csv(os.environ.get('TRIP_CELLS', '/tmp/trip_cells.csv'), index=False)
    if os.environ.get('TRIP_CELLS_ONLY'):
        return

    # ---- winner tests
    te = te[te.positionFinish.notna()].copy()
    te['win'] = (te.positionFinish == 1).astype(int)
    te['sp'] = pd.to_numeric(te.priceStarting, errors='coerce')
    g = te.groupby('race_id')
    te['book'] = g.sp.transform(lambda s: (1 / s).sum())
    te['nsp'] = g.sp.transform('count')
    te = te[(te.nsp == g.race_id.transform('size')) & te.book.between(1.05, 2.0)]
    te = te[te.groupby('race_id').win.transform('sum') == 1]
    te = te[te.groupby('race_id').r3.transform('count') / te.fs >= 0.8].copy()
    te['r3_rel'] = (te.r3 - te.groupby('race_id').r3.transform('mean')).fillna(0.0)
    te['lnp'] = np.log(te.sp)
    for nm in ('base', 'rich'):
        for tgt in ('gap800', 'settle'):
            c = f'{nm}_{tgt}'
            te[c + '_rel'] = te[c] - te.groupby('race_id')[c].transform('mean')
    te['r3_rank'] = te.groupby('race_id').r3.rank(ascending=False, method='first')
    print(f'\nwinner test races: {te.race_id.nunique()}, runners {len(te)}')
    sets = {'price': ['lnp'], 'price+rating': ['lnp', 'r3_rel']}
    for nm in ('base', 'rich'):
        sets[f'price+rating+{nm}_gap'] = ['lnp', 'r3_rel', f'{nm}_gap800_rel']
        sets[f'price+rating+{nm}_settle'] = ['lnp', 'r3_rel', f'{nm}_settle_rel']
        sets[f'price+rating+{nm}_both'] = ['lnp', 'r3_rel', f'{nm}_gap800_rel', f'{nm}_settle_rel']
    for label, n in (('FULL FIELD', None), ('TOP 5 BY RATING', 5)):
        print(f'\n=== {label} (log-lik per race, higher is better) ===')
        res = winner_test(te, sets, n)
        base_ll = res['price+rating'][1]
        for k, (b, ll, nb) in res.items():
            print(f'{k:28s} ll {ll:.4f}  vs price+rating {ll - base_ll:+.4f}  coefs {np.round(b, 3)}  races {nb}')
    # bootstrap gain of rich_both vs base_both and vs none (full field)
    rng = np.random.default_rng(0)
    ids = te.race_id.unique()
    print('\nbootstrap (full field), gain over price+rating:')
    gains = {k: [] for k in ('base_both', 'rich_both')}
    parts = {i: z for i, z in te.groupby('race_id')}
    for _ in range(20):
        pick = rng.choice(ids, len(ids), replace=True)
        s = pd.concat([parts[i].assign(race_id=j) for j, i in enumerate(pick)])
        r = winner_test(s, {'p': sets['price+rating'], 'base_both': sets['price+rating+base_both'], 'rich_both': sets['price+rating+rich_both']})
        for k in gains:
            gains[k].append(r[k][1] - r['p'][1])
    for k, v in gains.items():
        print(k, f'mean {np.mean(v):+.4f}  sd {np.std(v):.4f}')
    te[['race_id', 'horse_id', 'win', 'sp', 'lnp', 'r3_rel', 'base_gap800_rel', 'rich_gap800_rel', 'base_settle_rel', 'rich_settle_rel', 'band', 'track', 'fs']].to_pickle(
        os.environ.get('TRIP_OUT', '/tmp/trip_study_test.pkl'))


if __name__ == '__main__':
    sys.exit(main())
