"""Rebuilt Spd (formula + context + relevance, research/spd_formula_ctx.py) inside the blend (22 Oct 2026). Same dashboard-race sample and out-of-sample Proj versions as proj_vs_blend.py; the rebuilt Spd is
read from the pickle written by spd_formula_ctx.py (SPD_OUT) by horse name and date. Original docstring: Does a better Proj make the Rating blend unnecessary? (22 Oct 2026). Dashboard races 26 Apr to 17 Oct 2026 (runners.csv + archive; Nett from the TopRate files; Spd as computed before the race;
SP prices not used). Proj versions are scored OUT OF SAMPLE: models fit before 2026-01-01 (early stop 2025-10..12), history strictly before each race's date, runner-page ATW ratings only:
 plain context (the Proj before 21 Oct's relevance work), relevance (3+ earlier runs, shipped on claude/proj-relevance), relevance + Huber loss. Races kept: formula coverage of 80% or more of the field,
one winner, 5+ runners. Compared: each signal alone and blends, winner log-lik and top pick; weights cross-fitted on date halves (fixed weights shown for the live 50/30/20 and 65/25/10).
Run: ROBUST_FRAME=<cache from proj_robust.py> PYTHONPATH=. python research/proj_vs_blend.py"""
import os, re, sys, warnings
from datetime import date
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ctx as C
import speed_rating as sr

rp = pd.read_pickle(os.environ['ROBUST_FRAME'])
pg = rp[rp.f.notna()].copy(); classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
def fit(feats, a, b, **kw):
    return lgb.LGBMRegressor(n_estimators=4000, **{**P, **kw}).fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
sp = lambda d_: (d_[d_.date < es], d_[(d_.date >= es) & (d_.date < cut)])
tr0, va0 = sp(pg); tr3, va3 = sp(pg[pg.n >= C.REL_MIN_RUNS])
m0 = fit(F0, tr0, va0); m1 = fit(F1, tr3, va3); m1h = fit(F1, tr3, va3, objective='huber', alpha=8.0)
meta = dict(classes=classes, rel_feats=F1)
print('models fit before 2026: plain', m0.best_iteration_, 'relevance', m1.best_iteration_, 'relevance+Huber', m1h.best_iteration_, flush=True)

KEY = ['date', 'venue', 'race', 'horse']
cols = KEY + ['horse_id', 'wpr_nett', 'scratched', 'won', 'field_source', 'spd_fig', 'weight_carried', 'barrier', 'jockey', 'distance', 'going', 'race_class', 'track_grading', 'weight_carried']
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd('archive/toprate/toprate_runners_archive.csv.gz'), rd('archive/toprate/toprate_runners.csv')], ignore_index=True)
cur = pd.concat([rd('runners_archive.csv.gz'), rd('runners.csv')], ignore_index=True)
for x in (leg, cur):
    x['date'] = x['date'].astype(str).str[:10]; x['race'] = x['race'].astype(str)
d = leg.drop_duplicates(KEY, keep='last').set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep='last').set_index(KEY)).reset_index()
d = d[(d.date >= '2026-04-26') & (d.date <= '2026-10-17')]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains('not in toprate', na=False)].reset_index(drop=True)
d['spd_fig'] = sr.compute(d, today=date(2026, 8, 1)).where(lambda s: s.notna(), pd.to_numeric(d.spd_fig, errors='coerce'))
d['rk'] = d.venue.astype(str) + '|' + d.date + '|' + d.race
g = d.groupby('rk'); ok = (g.won.transform('sum') == 1) & g.won.transform(lambda s: s.notna().all()) & (g.won.transform('size') >= 5)
d = d[ok].copy(); d['won'] = d.won.astype(int)
T = pd.DataFrame(dict(horse_id=pd.to_numeric(d.horse_id, errors='coerce').values, date=pd.to_datetime(d.date).values, jockey=d.jockey.values, venue=d.venue.values, distance=d.distance.values, going=d.going.values,
                      weightCarried=d.weight_carried.values, barrier=d.barrier.values, field_size=g.won.transform('size')[d.index].values, race_class=d.race_class.values, trackGrading=d.track_grading.values))
ok_h = T.horse_id.notna().values
T = T[ok_h].reset_index(drop=True); d = d[ok_h].reset_index(drop=True)
f2, corr0 = C.predict(T, meta=meta, booster=m0.booster_, rp=rp, rel_booster=None)
_, corr1 = C.predict(T, meta=meta, booster=m0.booster_, rp=rp, rel_booster=m1.booster_)
_, corr1h = C.predict(T, meta=meta, booster=m0.booster_, rp=rp, rel_booster=m1h.booster_)
d['p_plain'], d['p_rel'], d['p_relh'] = f2 + corr0, f2 + corr1, f2 + corr1h
d['nett'] = pd.to_numeric(d.wpr_nett, errors='coerce'); d['spd'] = pd.to_numeric(d.spd_fig, errors='coerce')
nt = pd.read_pickle(os.environ['SPD_NEW'])[['key', 'date', 'p_rel', 'p_now']].rename(columns={'p_rel': 'spd2', 'p_now': 'spd_line'})
nt['date'] = pd.to_datetime(nt.date).dt.normalize()
d['key'] = d.horse.astype(str).str.lower().str.strip(); d['dkey'] = pd.to_datetime(d.date).dt.normalize()
d = d.merge(nt.drop_duplicates(['key', 'date']), left_on=['key', 'dkey'], right_on=['key', 'date'], how='left', suffixes=('', '_n'))
print('rebuilt Spd found for', round(100 * d.spd2.notna().mean(), 1), '% of dashboard runners', flush=True)
cov = d.groupby('rk').p_plain.transform(lambda s: s.notna().mean())
D = d[(cov >= 0.8) & (d.groupby('rk').spd2.transform(lambda s: s.notna().mean()) >= 0.8)].copy(); D['rid'] = D.rk.astype('category').cat.codes
for c in ('p_plain', 'p_rel', 'p_relh', 'nett', 'spd', 'spd2'):
    gm = D.groupby('rid')[c]; D['z_' + c] = ((D[c] - gm.transform('mean')) / gm.transform('std').replace(0, np.nan)).fillna(0.0)
for pv in ('p_plain', 'p_rel', 'p_relh'):
    D['z_b50_' + pv] = .5 * D['z_' + pv] + .3 * D.z_nett + .2 * D.z_spd
    D['z_b65_' + pv] = .65 * D['z_' + pv] + .25 * D.z_nett + .10 * D.z_spd
print(f"races kept {D.rid.nunique()} ({len(D)} runners), formula coverage 80%+, one winner, 5+ runners\n")
def ll(df, X, w):
    s = X @ w; mx = pd.Series(s).groupby(df.rid.values).transform('max').values; e = np.exp(s - mx)
    return (s - (np.log(pd.Series(e).groupby(df.rid.values).transform('sum').values) + mx))[df.won.values == 1]
def fitw(df, cs):
    X = df[['z_' + c for c in cs]].values
    return minimize(lambda w: -ll(df, X, w).mean(), np.full(len(cs), .2), method='L-BFGS-B').x
dates = sorted(D.date.unique()); half = dates[len(dates) // 2]; A, B = D[D.date < half], D[D.date >= half]
def run(cs, fixed=None):
    """cs: columns (z_ prefix added). One column = fit only its scale; several = fit their weights. Cross-fitted on the two date halves."""
    out, tops = [], []
    for a, b in ((A, B), (B, A)):
        w = fixed if fixed is not None else fitw(a, cs)
        X = b[['z_' + c for c in cs]].values; out.append(ll(b, X, w))
        t = b.assign(s=X @ w); tops.append(t.loc[t.groupby('rid').s.idxmax()].won.values)
    return np.concatenate(out), np.concatenate(tops)
rows = {}
rows['Proj alone (relevance)'] = run(['p_rel']); rows['Nett alone'] = run(['nett']); rows['Spd today alone'] = run(['spd']); rows['Spd rebuilt alone'] = run(['spd2'])
rows['Proj + Nett'] = run(['p_rel', 'nett'])
rows['Proj + Nett + Spd today (the blend)'] = run(['p_rel', 'nett', 'spd'])
rows['Proj + Nett + Spd rebuilt'] = run(['p_rel', 'nett', 'spd2'])
rows['Nett + Spd rebuilt (no Proj)'] = run(['nett', 'spd2'])
rows['Proj + Spd rebuilt (no Nett)'] = run(['p_rel', 'spd2'])
rows['Proj + Nett + both Spds'] = run(['p_rel', 'nett', 'spd', 'spd2'])
base = rows['Proj + Nett + Spd today (the blend)'][0]
print(f"{'score':36s} {'winner LL':>9s} {'top pick':>9s} {'vs today blend':>26s}")
for k, (l, t) in rows.items():
    dd = l - base; print(f"{k:36s} {l.mean():9.4f} {100*t.mean():8.1f}% {dd.mean():+14.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})")
for cs in (['p_rel', 'nett', 'spd'], ['p_rel', 'nett', 'spd2'], ['p_rel', 'nett', 'spd', 'spd2'], ['p_rel', 'spd2']):
    w = fitw(D, cs); print('full-sample fitted shares', cs, np.round(w / w.sum(), 2))
