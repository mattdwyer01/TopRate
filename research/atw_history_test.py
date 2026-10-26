"""Can 10 years of PLAIN results-file ratings stand in for the thin runner-page (ATW) history? Run with PYTHONPATH=.
Finding behind it (atw_convert_explore.py): runner-page rating minus plain wpr is a constant per horse (within-horse sd 0.008) set by the conditions
of the horse's next race, so a page-scale rating = plain rating + c(next race). Test: same features and model on (A) runner-page history, fit before 2026 on
about 49k runs; (B) plain results history 2020-2025 (about 1M runs), target shifted by the measured offset c_h; (C) plain history limited to the same
number of runs as A. Held-out: 2026 runs of horses with 3+ earlier runs in BOTH sources, scored against the page rating of the run (RMSE, MAE, within-race RMSE)."""
import glob, gzip, json
import numpy as np, pandas as pd, lightgbm as lgb

K = 8
def going_num(s):
    s = s.astype(str)
    n = pd.to_numeric(s.str.extract(r"(\d+)")[0], errors="coerce")
    return n.where(n.notna(), np.where(s.str.contains("Synth|Dirt|Poly|Tapeta", case=False), 4, np.nan))

def load_pages():
    rows = []
    for f in sorted(glob.glob('data/tr_form/*.json.gz')):
        for r in json.load(gzip.open(f, 'rt'))['runs'].values():
            if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
            rows.append(dict(horse_id=r['horse_id'], date=r['date'], rating=r['wpr'], distance=r.get('distance'), going=r.get('going'), weight=r.get('weightCarried'),
                             margin=r.get('marginFinish'), pos=r.get('positionFinish'), fs=r.get('starters'), barrier=r.get('barrier'), cls=r.get('class'),
                             track=r.get('track')))
    return pd.DataFrame(rows)

def load_plain():
    out = []
    for f in sorted(glob.glob('race_results_20[12]*.csv.gz')):
        if '_rc' in f: continue
        d = pd.read_csv(f, usecols=['horse_id', 'date', 'wpr', 'distance', 'going', 'weightCarried', 'marginFinish', 'positionFinish', 'field_size', 'barrier',
                                    'race_class', 'isBarrierTrial', 'is_jumpout', 'track', 'wprStatus'], low_memory=False)
        out.append(d)
    d = pd.concat(out)
    d = d[(d.isBarrierTrial.astype(str) != 'True') & (d.is_jumpout.astype(str) != 'True')].dropna(subset=['wpr', 'horse_id'])
    d = d[~d.race_class.astype(str).str.contains('Hurdle|Steeple', case=False)]
    return d.rename(columns=dict(wpr='rating', weightCarried='weight', marginFinish='margin', positionFinish='pos', field_size='fs', race_class='cls'))

def feats(d):
    d = d.copy()
    d['horse_id'] = pd.to_numeric(d.horse_id, errors='coerce'); d['date'] = pd.to_datetime(d.date)
    for c in ('rating', 'distance', 'weight', 'margin', 'pos', 'fs', 'barrier'): d[c] = pd.to_numeric(d[c], errors='coerce')
    d['going_n'] = going_num(d.going)
    d = d.dropna(subset=['horse_id', 'date', 'rating']).drop_duplicates(['horse_id', 'date']).sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = d.groupby('horse_id')
    for k in range(1, K + 1): d[f'r{k}'] = g.rating.shift(k)
    d['n'] = g.cumcount()
    R = d[[f'r{k}' for k in range(1, K + 1)]]
    d['mean3'] = R.iloc[:, :3].mean(axis=1); d['mean8'] = R.mean(axis=1); d['max8'] = R.max(axis=1); d['std4'] = R.iloc[:, :4].std(axis=1)
    d['days'] = (d.date - g.date.shift(1)).dt.days
    d['l_wt'] = g.weight.shift(1); d['wt_chg'] = d.weight - d.l_wt
    d['l_dist'] = g.distance.shift(1); d['dist_chg'] = d.distance - d.l_dist
    d['l_going'] = g.going_n.shift(1); d['going_chg'] = d.going_n - d.l_going
    d['l_mgn'] = g.margin.shift(1); d['l_posf'] = (g.pos.shift(1) / g.fs.shift(1))
    d['barr_f'] = d.barrier / d.fs
    return d

FE = [f'r{k}' for k in range(1, K + 1)] + ['n', 'mean3', 'mean8', 'max8', 'std4', 'days', 'weight', 'l_wt', 'wt_chg', 'distance', 'l_dist', 'dist_chg', 'going_n', 'l_going',
                                          'going_chg', 'fs', 'barr_f', 'l_mgn', 'l_posf', 'cls_c']

def fit(tr, va, y='rating'):
    m = lgb.LGBMRegressor(objective='huber', alpha=4.0, n_estimators=3000, learning_rate=0.03, num_leaves=63, min_child_samples=40, subsample=0.8, subsample_freq=1,
                          colsample_bytree=0.7, verbose=-1)
    m.fit(tr[FE], tr[y], eval_set=[(va[FE], va[y])], callbacks=[lgb.early_stopping(100, verbose=False)])
    return m

def main():
    P = feats(load_pages()); Q = feats(load_plain())
    top = pd.concat([P.cls, Q.cls]).value_counts().index[:80]
    cmap = {c: i for i, c in enumerate(top)}
    for d in (P, Q): d['cls_c'] = d.cls.map(cmap).fillna(-1)
    M = pd.read_pickle('/tmp/atw_explore.pkl')[['horse_id', 'date']].copy()
    off = pd.read_pickle('/tmp/atw_explore.pkl').groupby('horse_id').off.median().rename('c')
    Q = Q.merge(off, on='horse_id', how='left')
    cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
    # held-out: 2026 page runs with 3+ earlier runs in both sources
    Pt = P[(P.date >= cut) & (P.n >= 3)]
    Qk = Q[(Q.date >= cut)][['horse_id', 'date', 'n', 'rating', 'c']].rename(columns={'n': 'nq', 'rating': 'plain', 'c': 'c'})
    H = Pt.merge(Qk, on=['horse_id', 'date']).query('nq >= 3').dropna(subset=['c']).copy()
    keyH = set(zip(H.horse_id, H.date))
    print('held-out runs', len(H), 'horses', H.horse_id.nunique())
    res = {}
    # A: page history
    trA = P[(P.date < es) & (P.n >= 3)]; vaA = P[(P.date >= es) & (P.date < cut) & (P.n >= 3)]
    mA = fit(trA, vaA); H['A'] = mA.predict(H[FE]); print('A fit', len(trA), mA.best_iteration_)
    # features of the held-out run built from plain history
    Hq = Q.merge(H[['horse_id', 'date']], on=['horse_id', 'date'])
    Hq = Hq.set_index(['horse_id', 'date']).loc[list(zip(H.horse_id, H.date))]
    # B: plain history 2020-2025 (target = plain rating), then + measured offset
    trB = Q[(Q.date >= '2020-01-01') & (Q.date < es) & (Q.n >= 3)]; vaB = Q[(Q.date >= es) & (Q.date < cut) & (Q.n >= 3)]
    mB = fit(trB, vaB); H['B'] = mB.predict(Hq[FE]) + H.c.values; print('B fit', len(trB), mB.best_iteration_)
    # C: plain history, same size as A
    trC = trB.sample(len(trA), random_state=0)
    mC = fit(trC, vaB); H['C'] = mC.predict(Hq[FE]) + H.c.values
    # D: blend A and B
    H['D'] = (H.A + H.B) / 2
    # race key
    H['race'] = H.date.astype(str) + '|' + H.track.astype(str) + '|' + H.distance.astype(str) + '|' + H.fs.astype(str)
    print('model            RMSE   MAE   within-race RMSE  bias')
    for k, nm in (('A', 'A page history (49k runs)'), ('B', 'B plain 2020-25 + offset'), ('C', 'C plain, same size as A'), ('D', 'D average of A and B')):
        e = H.rating - H[k]; ew = e - e.groupby(H.race).transform('mean')
        print(f'{nm:30s} {np.sqrt((e**2).mean()):.3f} {e.abs().mean():.3f} {np.sqrt((ew**2).mean()):.3f} {e.mean():+.2f}')
    for lo, hi in ((3, 5), (5, 9), (9, 99)):
        s = (H.n >= lo) & (H.n < hi)
        print('page runs', lo, hi, s.sum(), {k: round(float(np.sqrt(((H.rating - H[k])[s] ** 2).mean())), 3) for k in 'ABCD'})
    H.to_pickle('/tmp/atw_hist_test.pkl')

main()
