"""Live complete-fields test of the extra Proj inputs built by projection/ctx_ext.py (10 Nov 2026). Same idea as research/proj_live_fields_test.py: every race in
data/tr_results from 2026-10-09 (complete fields as they ran), projected through the LIVE path (ctx.predict on the runner-page store) with models fitted only on runs
before that day. Here the training rows and the live runners get the extra inputs from the same builder (ctx_ext.add_all), reading the complete-field table as of the day
before each race. Variants: base (live inputs), ext (all four blocks), ped, dirf, tfu, frk (one block each).
  fit:   PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/proj_live_ext_test.py --variants base,ext --out plx/j1.pkl
  score: python research/proj_live_ext_test.py --score plx   (every *.pkl in the folder; writes research/proj_live_ext_test.json)
Scoring applies the live post-model steps to every variant alike (stretch 1.2 for 3+ runs, cap 8 for under 3, formula anchor +-5), and also reports the raw model step."""
import argparse, glob, gzip, json, os, sys, time
import numpy as np, pandas as pd
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
ap = argparse.ArgumentParser(); ap.add_argument('--variants', default='base,ext'); ap.add_argument('--out', default='plx/live.pkl'); ap.add_argument('--score')
ap.add_argument('--frac', type=float, default=1.0); ap.add_argument('--trees', type=int, default=2200); ap.add_argument('--lr', type=float, default=0.06); ap.add_argument('--from', dest='d0', default='2026-10-09')
a = ap.parse_args()
T0 = time.time(); log = lambda *x: print(f'[{(time.time() - T0) / 60:5.1f}m]', *x, flush=True)


def score(folder):
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
    code = pd.factorize(D.rid)[0]; nr = code.max() + 1
    win = (D.pos == 1).values
    onew = np.bincount(code, weights=win, minlength=nr) == 1
    rdate = pd.Series(D.date.values).groupby(code).first().values
    half = (rdate >= D.date.median().to_datetime64()).astype(int)
    few = (D.n < 3).values

    def build(corr, live=True):
        s, cap, anchor = (1.2, 8.0, 5.0) if live else (1.0, 8.0, None)
        c = np.where(few, np.clip(corr, -cap, cap), corr * s)
        p = D.f.values + c
        if anchor:
            ok = ~np.isnan(D.tf.values) & ~few
            p = np.where(ok, D.tf.values + np.clip(p - D.tf.values, -anchor, anchor), p)
        P = pd.Series(p, index=D.index)
        lev = P.where(D.n >= 3).groupby(D.rid).transform('mean'); cnt = P.where(D.n >= 3).groupby(D.rid).transform('count')
        lev = lev.where(cnt >= db['min_experienced'], P.groupby(D.rid).transform('mean'))
        deb = P.isna() & D.relp.notna() & lev.notna()
        P[deb] = lev[deb] + db['a'] + db['b'] * D.relp[deb]
        return P.values

    BS = np.arange(0.06, 0.6, 0.005)

    def wll(x):
        okr = onew & (np.bincount(code, weights=np.isnan(x), minlength=nr) == 0) & (np.bincount(code, minlength=nr) >= 4)
        xx = np.nan_to_num(x); mx = np.full(nr, -np.inf); np.maximum.at(mx, code, xx)
        L = []
        for b in BS:
            z = b * (xx - mx[code]); s = np.bincount(code, weights=np.exp(z), minlength=nr); o = np.full(nr, np.nan); o[code[win]] = z[win] - np.log(s[code[win]]); L.append(o)
        L = np.array(L); out = np.full(nr, np.nan)
        for h in (0, 1):
            fit = okr & (half != h); b = int(np.argmax(np.nanmean(L[:, fit], axis=1))); out[okr & (half == h)] = L[b, okr & (half == h)]
        order = np.lexsort((-xx, code)); first = np.r_[0, np.cumsum(np.bincount(code, minlength=nr))[:-1]]; rank = np.empty(len(xx)); rank[order] = np.arange(len(xx)) - first[code[order]] + 1
        top = np.bincount(code, weights=win & (rank == 1), minlength=nr); t3 = np.bincount(code, weights=win & (rank <= 3), minlength=nr)
        return out, float(np.nanmean(top[okr])), float(np.nanmean(t3[okr]))

    act = D.atw.where(D.final)
    res = {}
    variants = [c[5:] for c in D.columns if c.startswith('corr_')]
    print(f'runners {len(D)}, races {nr}, {D.date.min().date()} to {D.date.max().date()}; no page run {int(D.f.isna().sum())}; variants {variants}')
    for live in (True, False):
        ref, _, _ = wll(build(D.corr_base.values, live))
        for v in variants:
            x = build(D['corr_' + v].values, live)
            s, top, t3 = wll(x)
            d = s - ref; dd = d[~np.isnan(d)]
            e = (act - x)[D.f.notna()]
            k = f"{v} ({'live steps' if live else 'raw step'})"
            res[k] = dict(races=int((~np.isnan(s)).sum()), win_ll=round(float(np.nanmean(s)), 5), top_pick=round(top, 4), winner_top3=round(t3, 4), gain=round(float(dd.mean()), 5),
                          se=round(float(dd.std() / np.sqrt(len(dd))), 5), halves=[round(float(np.nanmean(d[half == h])), 5) for h in (0, 1)],
                          rmse=round(float(np.sqrt((e ** 2).mean())), 3), mae=round(float(e.abs().mean()), 3), within3=round(float((e.abs() <= 3).mean()), 4))
            print(f'{k:22s}', res[k], flush=True)
    json.dump(res, open('research/proj_live_ext_test.json', 'w'), indent=1)


if a.score:
    score(a.score); sys.exit()

import lightgbm as lgb
import ctx as C, ctx_ext as EXT, features as FT, breakdown as BK
D0 = pd.Timestamp(a.d0)
VAR = [v for v in a.variants.split(',') if v]
ADD = {'base': [], 'ext': EXT.EXT_FEATS, **EXT.BLOCKS}
real = FT.runner_page_runs().copy()
FT._TR_CACHE['rows'] = EXT.complete_history(2020, None, a.frac)
cvfull = C.training_frame_rel(True)
FT._TR_CACHE['rows'] = real
src = EXT.src_from_frame(cvfull)
log('complete-field table', len(src), 'rows to', src.date.max().date())
cv = EXT.add_all(cvfull[cvfull.f.notna()].copy(), cvfull, src); log('extra inputs on converted rows')
pgfull = C.training_frame_rel(True)
pg = EXT.add_all(pgfull[pgfull.f.notna()].copy(), pgfull, src); log('extra inputs on page rows')
for nm, d in (('converted', cv), ('page', pg)):
    print(nm, 'coverage:', {c: round(float(d[c].notna().mean()), 3) for c in ('age', 'sire_eff', 'dam_eff', 'trn_eff', 'win8', 'rl1', 'fk1', 'rl3')}, flush=True)
classes = sorted(pg.cls.dropna().unique().tolist())
for d in (cv, pg):
    d['cls_c'] = C._cls(d.cls, classes)
tr = pd.concat([cv[cv.date < D0], pg[pg.date < D0]], ignore_index=True)
log('training rows', len(tr), 'to', tr.date.max().date())
F0 = C.FEATS2 + C.TRIAL_FEATS; F1 = C.FEATS2 + C.REL_FEATS2 + C.FIT_FEATS + C.TRIAL_FEATS
P = dict(n_estimators=a.trees, learning_rate=a.lr, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0, random_state=1)
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]

rows = []
for f in sorted(glob.glob('data/tr_results/*.json.gz')):
    d = os.path.basename(f)[:10]
    if pd.Timestamp(d) < D0:
        continue
    for rid, race in json.load(gzip.open(f, 'rt')).get('races', {}).items():
        rr = race.get('runners') or []
        for ru in rr:
            rows.append(dict(date=d, rid=f'{d}|{rid}', venue=race.get('venue'), distance=race.get('distance'), race_class=race.get('class'), going=race.get('going'), trackGrading=race.get('grading'),
                             final=race.get('wprStatus') == 'Final', field_size=len(rr), run_id=ru.get('runId'), horse_id=ru.get('horseId'), jockey=ru.get('jockey'), trainer=ru.get('trainer'),
                             barrier=ru.get('barrier'), weightCarried=ru.get('weightCarried'), pos=ru.get('positionFinish'), sp=ru.get('priceStarting'), atw=ru.get('atw')))
L = pd.DataFrame(rows).drop_duplicates('run_id')
R = pd.read_csv('runners.csv', usecols=['run_id', 'prize_money'], low_memory=False).drop_duplicates('run_id')
L = L.merge(R, on='run_id', how='left').rename(columns={'prize_money': 'prize'})
log('live rows', len(L), 'races', L.rid.nunique())
info = {}
for v in VAR:
    A, B = F0 + ADD[v], F1 + ADD[v]
    m0 = lgb.LGBMRegressor(**P).fit(tr[A], tr.resid); m1 = lgb.LGBMRegressor(**P).fit(rel(tr)[B], rel(tr).resid); log('fitted', v)
    meta = {'feats': A, 'rel_feats': B, 'classes': classes, 'rel_min_runs': C.REL_MIN_RUNS}
    f, corr = C.predict(L, meta=meta, booster=m0.booster_, rel_booster=m1.booster_, src=src)
    L['f'], L['corr_' + v] = f, corr
    if ADD[v]:
        imp = pd.Series(m1.booster_.feature_importance('gain'), index=B)
        info[v] = {'new_share': round(float(imp[ADD[v]].sum() / imp.sum()), 4), 'top_new': {x: round(float(y), 4) for x, y in (imp[ADD[v]] / imp.sum()).sort_values(ascending=False).head(10).items()}}
        print(v, info[v], flush=True)
        if v == 'ext':
            # the live path must give the training frame's figures: recent page rows (whole stored races) as upcoming targets against the same models
            sub = pgfull[pgfull.date > pgfull.date.max() - pd.Timedelta(days=12)].copy()
            has = sub.f.notna().values
            se = pg.reindex(sub.index[has])
            use = (se.n >= C.REL_MIN_RUNS).values
            tc = m0.predict(se[A]); tc[use] = m1.predict(se.loc[use, B])
            Tt = sub[['horse_id', 'date', 'jockey', 'trainer', 'vn', 'distance', 'going', 'weightCarried', 'barrier', 'field_size', 'race_class', 'trackGrading', 'prize']].rename(columns={'vn': 'venue'}).reset_index(drop=True)
            _, lc = C.predict(Tt, meta=meta, booster=m0.booster_, rel_booster=m1.booster_, src=src)
            dd = np.abs(lc[has] - tc)
            print(f'live path against training frame (ext): rows {int(has.sum())}, max diff {np.nanmax(dd):.5f}, mean {np.nanmean(dd):.5f}, share over 0.01 {np.nanmean(dd > 0.01):.4f}', flush=True)
rp = C.page_frame()
byh = {h: x.date.values for h, x in rp.groupby('horse_id')}
L['n'] = [0 if byh.get(h) is None else int(np.searchsorted(byh[h], np.datetime64(d), side='left')) for h, d in zip(pd.to_numeric(L.horse_id, errors='coerce'), L.date)]
L['tf'] = BK.tf_array(pd.DataFrame({'horse_id': L.horse_id.values, 'date': pd.to_datetime(L.date).values, 'distance': L.distance.values, 'going': L.going.values, 'weight_carried': np.nan, 'prize_money': L.prize.values}))
os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
L.to_pickle(a.out)
json.dump(info, open(a.out.replace('.pkl', '_info.json'), 'w'), indent=1)
log('wrote', a.out)
