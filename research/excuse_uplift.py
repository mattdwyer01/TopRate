"""Excuse-comment uplift (23 Oct 2026). A past run rated low because of a stated excuse (vet issue, eased, slow away, hampered, ...) understates the horse.
Step 1: learn how many rating points each excuse flag costs: dev = run rating minus the mean of the horse's 2 runs before and 2 after, regressed on the flags
(fit on runs before 2025-07-01). Step 2: add the learned uplift back to those runs in the history the Proj reads (runner-page ATW ratings only; the TARGET stays the
actual rating). Step 3: retrain the Huber alpha 4 context models on the uplifted history (same folds and params as projection/train_ctx.py) and compare held-out
2026 misses with the current Proj. Run: PYTHONPATH=. python research/excuse_uplift.py"""
import glob, gzip, json, os, re, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import features as F
import ctx as C
ROOT = F.ROOT
FL = {
    'vet': r'(?:vet\b|veterinar|lame|bled|bleed|arrhythm|cardiac|sore|injur|distress|respirat|fractur|tied up|heat|lost a plate|lost a shoe|lost its|bleeding)',
    'eased': r'(?:eased|not persevered|not knocked|dropped out|tailed off|weak|no response|failed to (?:respond|fire|handle)|did not handle|failed to)',
    'slow_away': r'(?:slow(?:ly)? (?:away|into stride|out)|began awkward|missed the start|fumbled|dwelt|stumbled|reared|lost ground at the start|slowly)',
    'blocked': r'(?:held up|blocked|checked|hampered|bumped|interfer|steadied|crowded|squeezed|shut in|not clear|no clear|denied a|awkward|tightened|shifted (?:in|out)|clipped heels|inconvenienced|taken ?up|eased to avoid)',
    'wide': r'(?:\b(?:three|four|five|six|3|4|5)\s?-?wide|wide (?:throughout|all the way|on the bend|in the straight)|without cover|exposed|no cover|raced wide|caught wide|held wide|forced wide|3w|4w)',
    'keen': r'(?:resented|over ?raced|raced keenly|pulled hard|fought|laid (?:in|out)|hung|rolled|raced greenly|ungenuine|unsettled)',
    'unsuited': r'(?:did not (?:handle|appreciate)|failed to handle|unsuited|not (?:handle|suited))',
}
CAP = 12.0


def load_comments():
    rows = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'tr_form', '*.json.gz'))):
        for r in json.load(gzip.open(f)).get('runs', {}).values():
            if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None:
                continue
            rows.append((r['horse_id'], r['date'], r.get('commentsSteward') or '', r.get('commentsVideo') or ''))
    t = pd.DataFrame(rows, columns=['horse_id', 'date', 'cs', 'cv'])
    t['horse_id'] = pd.to_numeric(t.horse_id, errors='coerce'); t['date'] = pd.to_datetime(t.date)
    t = t.dropna(subset=['horse_id']).drop_duplicates(['horse_id', 'date'], keep='last')
    txt = (t.cs + ' ' + t.cv).str.lower()
    for k, p in FL.items():
        t[k] = txt.str.contains(p, regex=True).astype(int)
    return t


def main():
    runs = F.runner_page_runs().copy()
    cm = load_comments()
    runs = runs.merge(cm[['horse_id', 'date'] + list(FL)], on=['horse_id', 'date'], how='left').fillna({k: 0 for k in FL})
    runs = runs.sort_values(['horse_id', 'date']).reset_index(drop=True)
    g = runs.groupby('horse_id').wpr
    runs['prior2'] = g.transform(lambda s: s.shift(1).rolling(2, min_periods=2).mean())
    runs['next2'] = g.transform(lambda s: s[::-1].shift(1).rolling(2, min_periods=2).mean()[::-1])
    runs['dev'] = runs.wpr - 0.5 * (runs.prior2 + runs.next2)
    fit = runs[(runs.date < '2025-07-01') & runs.dev.notna()]
    X = np.c_[np.ones(len(fit)), fit[list(FL)].values]
    lam = np.diag([0] + [20.0] * len(FL))            # light ridge: flags overlap
    coef = np.linalg.solve(X.T @ X + lam, X.T @ fit.dev.values)
    print('runs with dev (fit window)', len(fit), '| baseline dev mean %.2f' % coef[0])
    print('flag      n_fit   share   coef (rating points vs the horse\'s own level)')
    for k, c in zip(FL, coef[1:]):
        n = int(fit[k].sum()); print(f'  {k:10s} {n:6d}  {100 * n / len(fit):5.1f}%  {c:+.2f}')
    cvec = pd.Series(coef[1:], index=list(FL))
    runs['uplift'] = (-(runs[list(FL)] * cvec).sum(axis=1)).clip(lower=0, upper=CAP)
    print('share of runs uplifted %.1f%%, mean uplift when applied %.2f, p90 %.2f' % (100 * (runs.uplift > 0.5).mean(), runs.uplift[runs.uplift > 0.5].mean(), runs.uplift[runs.uplift > 0.5].quantile(.9)))
    # does the uplift predict the horse's NEXT rating (rebound) beyond its form? simple check on 2026 held-out runs
    runs['next_dev'] = runs.groupby('horse_id').wpr.shift(-1) - runs.wpr
    t = runs[(runs.date >= '2025-07-01') & runs.next_dev.notna()]
    sl = np.polyfit(t.uplift, t.next_dev, 1)[0]
    print('rebound: next rating minus this rating, slope on uplift %.2f (1.0 would mean the uplift is fully recovered next start)' % sl)
    # adjusted history table
    raw = F.runner_page_runs().copy()
    adj = raw.merge(runs[['horse_id', 'date', 'uplift']], on=['horse_id', 'date'], how='left')
    adj['uplift'] = adj.uplift.fillna(0)
    adj['wpr_raw'] = adj.wpr
    adj['wpr'] = adj.wpr + adj.uplift
    F._TR_CACHE['rows'] = adj.drop(columns=['uplift', 'wpr_raw'])
    fa = C.training_frame_rel()
    F._TR_CACHE['rows'] = raw
    rawr = raw[['horse_id', 'date', 'wpr']].rename(columns={'wpr': 'wpr_raw'})
    fa = fa.merge(rawr, on=['horse_id', 'date'], how='left').merge(runs[['horse_id', 'date', 'uplift']], on=['horse_id', 'date'], how='left')
    fa['wpr'] = fa.wpr_raw; fa['resid'] = fa.wpr_raw - fa.f
    # how many of the last 3 runs were uplifted
    fa = fa.sort_values(['horse_id', 'date']).reset_index(drop=True)
    gg = fa.groupby('horse_id').uplift
    fa['n_up3'] = sum((gg.shift(k) > 0.5).astype(float) for k in (1, 2, 3))
    fa['up_sum3'] = sum(gg.shift(k).fillna(0) for k in (1, 2, 3))
    fa.to_parquet('/tmp/excuse_frame.parquet')
    pg = fa[fa.f.notna()].copy()
    classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
    params = dict(n_estimators=4000, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0)
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
    cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
    tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
    rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
    def fit_m(feats, a, b):
        m = lgb.LGBMRegressor(**params); m.fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)]); return m
    m0 = fit_m(F0, tr, va); m1 = fit_m(F1, rel(tr), rel(va))
    c = m0.predict(te[F0]); use = (te.n >= C.REL_MIN_RUNS).values; c[use] = m1.predict(te.loc[use, F1])
    te['projA'] = te.f + c
    print('trees', m0.best_iteration_, m1.best_iteration_, flush=True)
    te[['horse_id', 'date', 'projA', 'wpr', 'n', 'n_up3', 'up_sum3', 'uplift']].to_parquet('/tmp/excuse_te.parquet')
    print('saved /tmp/excuse_te.parquet')


if __name__ == '__main__':
    main()
