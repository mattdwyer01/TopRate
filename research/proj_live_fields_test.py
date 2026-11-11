"""Live complete fields test (10 Nov 2026). The 'pg' test (runner-page runs, part of each field) and the 'cv' test (complete converted fields) disagree on the stretch of the
context step (1.2 helps on pg, hurts on cv) and on the new inputs. This test uses the real thing: every race in data/tr_results from 2026-10-09 (complete fields as they ran,
TopRate's published ATW as the actual), projected through the LIVE path (ctx.predict on the runner-page store, history strictly before the race) with models fitted only on
runs before 2026-10-09 (live settings: converted history to 8 Oct plus page rows, 4,000 trees at 0.03, no early stopping). Fits two pairs: the usual target, and the residual
minus its race mean ('rdm'). Writes per-runner figures; --score prints winner log-likelihood (softmax scale cross-fitted on date halves), top pick and rating error for:
stretch 1.0 to 1.3, the formula anchor at +-3 / +-5 / off, the +-2 cap for horses with under 3 runs, and the usual level with the within-race order of the rdm pair.
First starters (no page run) get the live rule (race level + a + b x relative ln starting price) in every variant.
Run: PYTHONPATH=.:projection:research PROJECTION_RATINGS=toprate python research/proj_live_fields_test.py --out plf/live.pkl ; then --score plf/live.pkl"""
import argparse, glob, gzip, json, os, sys, time
import numpy as np, pandas as pd
sys.path.insert(0, 'projection'); sys.path.insert(0, 'research')
ap = argparse.ArgumentParser(); ap.add_argument('--out', default='plf/live.pkl'); ap.add_argument('--score'); ap.add_argument('--frac', type=float, default=1.0); ap.add_argument('--trees', type=int, default=4000)
ap.add_argument('--from', dest='d0', default='2026-10-09')
a = ap.parse_args()
T0 = time.time(); log = lambda *x: print(f'[{(time.time() - T0) / 60:5.1f}m]', *x, flush=True)


def score(path):
    D = pd.read_pickle(path)
    db = json.load(open('projection/models_tr/formula.json'))['debut']
    D['date'] = pd.to_datetime(D.date)
    D = D[D.pos.notna()].copy()
    D['lsp'] = np.log(pd.to_numeric(D.sp, errors='coerce').where(lambda s: s > 1))
    D['relp'] = D.lsp - D.groupby('rid').lsp.transform('mean')
    code = pd.factorize(D.rid)[0]; nr = code.max() + 1
    win = (D.pos == 1).values
    onew = np.bincount(code, weights=win, minlength=nr) == 1
    rdate = pd.Series(D.date.values).groupby(code).first().values
    half = (rdate >= D.date.median().to_datetime64()).astype(int)
    few = (D.n < 3).values

    def build(corr, s=1.0, cap_few=2.0, anchor=None):
        c = np.where(few, np.clip(corr, -cap_few, cap_few) if cap_few else corr, corr * s)
        p = D.f.values + c
        if anchor:
            ok = ~np.isnan(D.tf.values) & ~few
            p = np.where(ok, D.tf.values + np.clip(p - D.tf.values, -anchor, anchor), p)
        P = pd.Series(p, index=D.index)
        lev = P.where(D.n >= 3).groupby(D.rid).transform('mean'); cnt = P.where(D.n >= 3).groupby(D.rid).transform('count')
        lev2 = P.groupby(D.rid).transform('mean')
        lev = lev.where(cnt >= db['min_experienced'], lev2)
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
        L = np.array(L); out = np.full(nr, np.nan); bb = []
        for h in (0, 1):
            fit = okr & (half != h); b = int(np.argmax(np.nanmean(L[:, fit], axis=1))); out[okr & (half == h)] = L[b, okr & (half == h)]; bb.append(round(float(BS[b]), 3))
        order = np.lexsort((-xx, code)); first = np.r_[0, np.cumsum(np.bincount(code, minlength=nr))[:-1]]; rank = np.empty(len(xx)); rank[order] = np.arange(len(xx)) - first[code[order]] + 1
        top = np.bincount(code, weights=win & (rank == 1), minlength=nr)
        return out, float(np.nanmean(top[okr])), bb

    act = D.atw.where(D.final)
    V = {'formula only': build(np.zeros(len(D)), cap_few=0)}
    for s in (1.0, 1.1, 1.2, 1.3):
        V[f'stretch {s}, no anchor'] = build(D['corr'].values, s)
    for s in (1.0, 1.2):
        for an in (3, 5, 8):
            V[f'stretch {s}, anchor {an}'] = build(D['corr'].values, s, anchor=an)
    V['stretch 1.0, no cap for under 3 runs'] = build(D['corr'].values, 1.0, cap_few=0)
    V['stretch 1.0, cap 4 for under 3 runs'] = build(D['corr'].values, 1.0, cap_few=4)
    if 'corr_r' in D:
        dm = lambda x: x - pd.Series(x).groupby(code).transform('mean').values
        for s in (1.0, 1.2):
            base = build(D['corr'].values, s); r = build(D.corr_r.values, s)
            ok = ~np.isnan(D.f.values)
            lvl = pd.Series(np.where(ok, base, np.nan)).groupby(code).transform('mean').values; dv = np.where(ok, r, np.nan); dv = dv - pd.Series(dv).groupby(code).transform('mean').values
            V[f'stretch {s}, within-race target (rdm)'] = np.where(ok, lvl + dv, base)
    if 'proj_live' in D:
        V['logged live Proj (as shown then)'] = D.proj_live.values
    ref = 'stretch 1.0, no anchor'
    sref, _, _ = wll(V[ref])
    print(f'runners {len(D)}, races {nr}, from {D.date.min().date()} to {D.date.max().date()}; first starters / no page run {int(D.f.isna().sum())}; reference = {ref}')
    res = {}
    for k, x in V.items():
        s, top, bb = wll(x)
        if k.startswith('logged'):
            okr = ~np.isnan(s) & ~np.isnan(sref)
            print(f'   (logged Proj covers {int(okr.sum())} races; reference on the same races {np.nanmean(sref[okr]):.5f})')
        d = (s - sref); d = d[~np.isnan(d)]
        e = (act - x)[D.f.notna()]
        res[k] = dict(races=int((~np.isnan(s)).sum()), win_ll=round(float(np.nanmean(s)), 5), top_pick=round(top, 4), gain=round(float(d.mean()), 5), se=round(float(d.std() / np.sqrt(len(d))), 5),
                      rmse=round(float(np.sqrt((e ** 2).mean())), 3), mae=round(float(e.abs().mean()), 3), within3=round(float((e.abs() <= 3).mean()), 4), median_miss=round(float(e.median()), 2), betas=bb)
        print(f'{k:42s}', res[k], flush=True)
    json.dump(res, open('research/proj_live_fields_test.json', 'w'), indent=1)


if a.score:
    score(a.score); sys.exit()

import lightgbm as lgb
import ctx as C, conv_history as CH, features as FT, breakdown as BK
D0 = pd.Timestamp(a.d0)
real = FT.runner_page_runs().copy()
FT._TR_CACHE['rows'] = CH.build(2020, str((D0 - pd.Timedelta(days=1)).date()), a.frac)
cv = C.training_frame_rel(True); cv = cv[cv.f.notna()].copy()
FT._TR_CACHE['rows'] = real
pg = C.training_frame_rel(True); pg = pg[pg.f.notna()].copy()
classes = sorted(pg.cls.dropna().unique().tolist())
for d in (cv, pg):
    d['cls_c'] = C._cls(d.cls, classes); d['rk'] = C._race_key(d)
tr = pd.concat([cv[cv.date < D0], pg[pg.date < D0]], ignore_index=True)
g = tr.groupby('rk').resid
tr['resid_dm'] = (tr.resid - g.transform('mean')).where(g.transform('size') >= 4)
log('training rows', len(tr), 'to', tr.date.max().date())
F0 = C.FEATS2 + C.TRIAL_FEATS; F1 = C.FEATS2 + C.REL_FEATS2 + C.FIT_FEATS + C.TRIAL_FEATS
P = dict(n_estimators=a.trees, learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, objective='huber', alpha=4.0, random_state=1)
rel = lambda d: d[d.n >= C.REL_MIN_RUNS]
M = {}
for y in ('resid', 'resid_dm'):
    t = tr[tr[y].notna()]
    M[y] = (lgb.LGBMRegressor(**P).fit(t[F0], t[y]).booster_, lgb.LGBMRegressor(**P).fit(rel(t)[F1], rel(t)[y]).booster_); log('fitted', y)
meta = {'feats': F0, 'rel_feats': F1, 'classes': classes, 'rel_min_runs': C.REL_MIN_RUNS}

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
L = pd.DataFrame(rows)
R = pd.read_csv('runners.csv', usecols=['run_id', 'prize_money'], low_memory=False).drop_duplicates('run_id')
L = L.merge(R, on='run_id', how='left').rename(columns={'prize_money': 'prize'})
log('live rows', len(L), 'races', L.rid.nunique(), L.date.min(), L.date.max())
f, corr = C.predict(L, meta=meta, booster=M['resid'][0], rel_booster=M['resid'][1])
_, corr_r = C.predict(L, meta=meta, booster=M['resid_dm'][0], rel_booster=M['resid_dm'][1])
L['f'], L['corr'], L['corr_r'] = f, corr, corr_r
rp = C.page_frame()
byh = {h: x.date.values for h, x in rp.groupby('horse_id')}
L['n'] = [0 if byh.get(h) is None else int(np.searchsorted(byh[h], np.datetime64(d), side='left')) for h, d in zip(pd.to_numeric(L.horse_id, errors='coerce'), L.date)]
L['tf'] = BK.tf_array(pd.DataFrame({'horse_id': L.horse_id.values, 'date': pd.to_datetime(L.date).values, 'distance': L.distance.values, 'going': L.going.values, 'weight_carried': np.nan, 'prize_money': L.prize.values}))
try:
    lg = pd.read_csv('wpr_projection_log.csv.gz', usecols=['run_id', 'proj', 'made'], low_memory=False).sort_values('made').drop_duplicates('run_id', keep='last')
    L = L.merge(lg.rename(columns={'proj': 'proj_live'})[['run_id', 'proj_live']], on='run_id', how='left')
except Exception as e:
    print('no live log join', e)
os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
L.to_pickle(a.out)
log('wrote', a.out, 'with a figure', int(L.f.notna().sum()), 'of', len(L))
score(a.out)
