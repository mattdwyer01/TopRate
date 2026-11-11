"""Price sharpness and the 2 / 4 point lines on the Proj merged 11 Nov 2026 (trainer patterns, cap 8 for under-3-run horses), against the Proj before it
(live inputs, cap 2). Reads the predictions saved by research/proj_live_ext_test.py (models fitted before 9 Oct 2026, every race in data/tr_results since, complete
fields as they ran, projected through ctx.predict) and applies the live post-model steps (stretch 1.2, formula anchor 5, the first-starter rule).
For each Proj: the softmax beta that maximises the winner log-likelihood (all races and each date half), the log-likelihood at 0.20 and 0.30 against the best,
and the runners and winners inside 2 and 4 points of the top rated runner (first starters neither set the top nor count inside a line, as on the dashboard).
Run: python research/proj_lines_live_check.py <folder with the plx pickles>   (writes research/proj_lines_live_check.json)"""
import glob, json, os, sys
import numpy as np, pandas as pd

folder = sys.argv[1]
D = None
for f in sorted(glob.glob(os.path.join(folder, '**', '*.pkl'), recursive=True)):
    x = pd.read_pickle(f)
    cc = [c for c in x.columns if c.startswith('corr_')]
    D = x if D is None else D.merge(x[['run_id'] + [c for c in cc if c not in D.columns]], on='run_id', how='inner')
db = json.load(open('projection/models_tr/formula.json'))['debut']
D['date'] = pd.to_datetime(D.date)
D = D[D.pos.notna()].reset_index(drop=True)
D['lsp'] = np.log(pd.to_numeric(D.sp, errors='coerce').where(lambda s: s > 1))
D['relp'] = D.lsp - D.groupby('rid').lsp.transform('mean')
few = (D.n < 3).values


def build(corr, cap):
    c = np.where(few, np.clip(corr, -cap, cap), corr * 1.2)
    p = D.f.values + c
    ok = ~np.isnan(D.tf.values) & ~few
    p = np.where(ok, D.tf.values + np.clip(p - D.tf.values, -5.0, 5.0), p)
    P = pd.Series(p, index=D.index)
    lev = P.where(D.n >= 3).groupby(D.rid).transform('mean'); cnt = P.where(D.n >= 3).groupby(D.rid).transform('count')
    lev = lev.where(cnt >= db['min_experienced'], P.groupby(D.rid).transform('mean'))
    deb = P.isna() & D.relp.notna() & lev.notna()
    P[deb] = lev[deb] + db['a'] + db['b'] * D.relp[deb]
    return P.values


D['old'] = build(D.corr_base.values, 2.0)
D['new'] = build(D.corr_tfu.values, 8.0)
D['debut'] = D.f.isna()
g = D.groupby('rid')
keep = (g.pos.transform(lambda s: (s == 1).sum()) == 1) & (g.pos.transform('size') >= 4) & g.old.transform(lambda s: s.notna().all()) & g.new.transform(lambda s: s.notna().all())
T = D[keep].copy()
T['half'] = (T.date >= T.date.median()).astype(int)
nr = T.rid.nunique()
BS = np.round(np.arange(0.08, 0.45, 0.005), 3)


def ll(df, col, b):
    z = b * (df[col] - df.groupby('rid')[col].transform('max'))
    return (z - np.log(np.exp(z).groupby(df.rid).transform('sum')))[df.pos == 1]


res = {'races': int(nr), 'runners': int(len(T)), 'runners_per_race': round(len(T) / nr, 2), 'from': str(T.date.min().date()), 'to': str(T.date.max().date()),
       'first_starters': int(T.debut.sum())}
for col in ('old', 'new'):
    cur = {b: float(ll(T, col, b).mean()) for b in BS}
    best = max(cur, key=cur.get)
    hb = []
    for h in (0, 1):
        ch = {b: float(ll(T[T.half == h], col, b).mean()) for b in BS}; hb.append(max(ch, key=ch.get))
    top = T[col].where(~T.debut).groupby(T.rid).transform('max')
    gap = top - T[col]
    r = dict(best_beta=best, best_beta_halves=hb, ll_best=round(cur[best], 5), ll_at_020=round(cur[0.2], 5), ll_at_030=round(cur[0.3], 5),
             within_race_sd=round(float(T.groupby('rid')[col].std().mean()), 2),
             top_pick=round(float(((T[col] == T.groupby('rid')[col].transform('max')) & (T.pos == 1)).sum() / nr), 4))
    for line in (2, 4):
        ins = (gap <= line) & ~T.debut
        r[f'inside_{line}'] = dict(runners=round(float(ins.sum() / nr), 2), winners=round(float((ins & (T.pos == 1)).sum() / nr), 4),
                                   winners_halves=[round(float((ins & (T.pos == 1) & (T.half == h)).sum() / T[T.half == h].rid.nunique()), 4) for h in (0, 1)])
    # how the top pick's softmax chance at 0.20 and 0.30 compares with how often it wins
    for b in (0.2, 0.3):
        z = b * (T[col] - T.groupby('rid')[col].transform('max')); p = np.exp(z) / np.exp(z).groupby(T.rid).transform('sum')
        istop = T[col] == T.groupby('rid')[col].transform('max')
        r[f'top_pick_rated_at_{b}'] = round(float(p[istop].mean()), 4)
    res[col] = r
    print(col, r, flush=True)
json.dump(res, open('research/proj_lines_live_check.json', 'w'), indent=1)
print(res['races'], 'races', res['runners_per_race'], 'runners a race')
