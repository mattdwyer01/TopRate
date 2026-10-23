"""Final Rank blend refit with the shipped components (22 Oct 2026). Dashboard races 26 Apr to 17 Oct 2026; Proj = the relevance model as merged (PR 504: context models with venue effect, fit before 2026-01-01 so every race is
out of sample, history strictly before the race, runner-page ATW ratings only); Nett from the TopRate files; Spd = the rebuilt Spd (PR 505) out of sample from research/spd_formula_ctx.py's held-out predictions, falling back to
today's old rating where the rebuilt one is missing (as the live code does). Races kept: formula coverage 80%+, Nett coverage 80%+, one winner, 5+ runners. Weights cross-fitted on date halves; fixed candidate blends get a fitted scale.
Run: SPD_NEW=<spd_te.pkl from spd_formula_ctx.py> PYTHONPATH=. python research/blend_refit_final.py"""
import os, re, sys, warnings
from datetime import date
warnings.filterwarnings('ignore')
import lightgbm as lgb, numpy as np, pandas as pd
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ctx as C
import speed_rating as sr

rp = C.training_frame_rel()
classes = sorted(rp.cls.dropna().unique().tolist()); rp['cls_c'] = C._cls(rp.cls, classes)
pg = rp[rp.f.notna()].copy()
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1, n_jobs=4)
if os.environ.get('HUBER'): P.update(objective='huber', alpha=float(os.environ['HUBER']))   # the live context models are Huber alpha 4 since 22 Oct 2026
def fit(feats, a, b, **kw):
    return lgb.LGBMRegressor(n_estimators=4000, **{**P, **kw}).fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
sp = lambda d_: (d_[d_.date < es], d_[(d_.date >= es) & (d_.date < cut)])
tr0, va0 = sp(pg); tr3, va3 = sp(pg[pg.n >= C.REL_MIN_RUNS])
m0 = fit(F0, tr0, va0); m1 = fit(F1, tr3, va3); m1h = m1
meta = dict(classes=classes, rel_feats=F1)
print('models fit before 2026: plain', m0.best_iteration_, 'relevance', m1.best_iteration_, flush=True)

KEY = ['date', 'venue', 'race', 'horse']
cols = KEY + ['horse_id', 'wpr_nett', 'scratched', 'won', 'finish_position', 'field_source', 'spd_fig', 'weight_carried', 'barrier', 'jockey', 'distance', 'going', 'race_class', 'track_grading', 'weight_carried']
rd = lambda p: pd.read_csv(p, low_memory=False, usecols=lambda c: c in cols)
leg = pd.concat([rd('archive/toprate/toprate_runners_archive.csv.gz'), rd('archive/toprate/toprate_runners.csv')], ignore_index=True)
cur = pd.concat([rd('runners_archive.csv.gz'), rd('runners.csv')], ignore_index=True)
for x in (leg, cur):
    x['date'] = x['date'].astype(str).str[:10]; x['race'] = x['race'].astype(str)
d = leg.drop_duplicates(KEY, keep='last').set_index(KEY).combine_first(cur.drop_duplicates(KEY, keep='last').set_index(KEY)).reset_index()
d = d[(d.date >= '2026-04-26') & (d.date <= '2026-10-17')]
d = d[(d.scratched.fillna(0) != 1) & ~d.field_source.astype(str).str.contains('not in toprate', na=False)].reset_index(drop=True)
d['spd_fig'] = sr.compute(d, today=date(2026, 8, 1))  # run with SPD_MODEL=0: the shipped Spd model is refit on all data (in sample for these races).where(lambda s: s.notna(), pd.to_numeric(d.spd_fig, errors='coerce'))
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
print('rebuilt Spd found for', round(100 * d.spd2.notna().mean(), 1), '% of dashboard runners (rest fall back to today rating)', flush=True)
d['spd2_real'] = d.spd2.notna()
d['spd2'] = d.spd2.where(d.spd2.notna(), d.spd_line)
cov = d.groupby('rk').p_plain.transform(lambda s: s.notna().mean())
if os.environ.get('DUMP_D'):
    d.to_pickle(os.environ['DUMP_D']); print('dumped', len(d)); sys.exit(0)
SPD_COV = float(os.environ.get('SPD_COV', '0'))
D = d[(cov >= 0.8) & (d.groupby('rk').nett.transform(lambda s: s.notna().mean()) >= 0.8) & (d.groupby('rk').spd2_real.transform('mean') >= SPD_COV)].copy(); D['rid'] = D.rk.astype('category').cat.codes
for c in ('p_plain', 'p_rel', 'p_relh', 'nett', 'spd', 'spd2'):
    gm = D.groupby('rid')[c]; D['z_' + c] = ((D[c] - gm.transform('mean')) / gm.transform('std').replace(0, np.nan)).fillna(0.0)
for c in ('p_rel', 'nett', 'spd', 'spd2'):
    gm = D.groupby('rid')[c]; D['z_' + c] = ((D[c] - gm.transform('mean')) / gm.transform('std').replace(0, np.nan)).fillna(0.0)
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
rows['Proj alone'] = run(['p_rel']); rows['Nett alone'] = run(['nett']); rows['Spd rebuilt alone'] = run(['spd2']); rows['Spd old alone'] = run(['spd'])
rows['Proj + Nett'] = run(['p_rel', 'nett']); rows['Proj + Nett + Spd old (fitted)'] = run(['p_rel', 'nett', 'spd']); rows['Proj + Nett + Spd rebuilt (fitted)'] = run(['p_rel', 'nett', 'spd2'])
def fixed_blend(wp, wn, ws, spd='spd2'):
    D['z_fx'] = wp * D.z_p_rel + wn * D.z_nett + ws * D['z_' + spd]
    A_, B_ = D[D.date < half], D[D.date >= half]
    out, tops = [], []
    for a, b in ((A_, B_), (B_, A_)):
        w = fitw_col(a, 'z_fx'); X = b[['z_fx']].values; out.append(ll(b, X, w)); t = b.assign(s=X @ w); tops.append(t.loc[t.groupby('rid').s.idxmax()].won.values)
    return np.concatenate(out), np.concatenate(tops)
def fitw_col(df, c):
    X = df[[c]].values; return minimize(lambda w: -ll(df, X, w).mean(), np.full(1, .2), method='L-BFGS-B').x
cands = [(1, 0, 0), (.8, 0, .2), (.7, 0, .3), (.6, 0, .4), (.7, .3, 0), (.5, .5, 0), (.5, .3, .2), (.45, .3, .25), (.4, .3, .3), (.4, .35, .25), (.35, .3, .35), (.5, .25, .25), (.45, .25, .3), (.55, .25, .2), (.6, .25, .15), (.65, .25, .1), (.34, .33, .33)]
for c in cands: rows[f'fixed {int(c[0]*100)}/{int(c[1]*100)}/{int(c[2]*100)} (Spd rebuilt)'] = fixed_blend(*c)
rows['fixed 50/30/20 (Spd old, as before)'] = fixed_blend(.5, .3, .2, 'spd')
base = rows['fixed 50/30/20 (Spd rebuilt)'][0]
print(f"{'score':40s} {'winner LL':>9s} {'top pick':>9s} {'vs live 50/30/20 rebuilt':>28s}")
for k_, (l, t) in rows.items():
    dd = l - base; print(f"{k_:40s} {l.mean():9.4f} {100*t.mean():8.1f}% {dd.mean():+14.4f} (se {dd.std()/np.sqrt(len(dd)):.4f})")
for cs in (['p_rel', 'nett', 'spd'], ['p_rel', 'nett', 'spd2']):
    w = fitw(D, cs); print('full-sample fitted shares', cs, np.round(w / w.sum(), 3))
# bootstrap of the fitted shares (races resampled)
rng = np.random.default_rng(1); ids = D.rid.unique(); sh = []
byr = {r_: g_ for r_, g_ in D.groupby('rid')}
for _ in range(200):
    pick = rng.choice(ids, len(ids)); bs = pd.concat([byr[r_].assign(rid=i_) for i_, r_ in enumerate(pick)], ignore_index=True)
    w = fitw(bs, ['p_rel', 'nett', 'spd2']); sh.append(w / w.sum())
sh = np.array(sh); print('bootstrap 5/50/95% share Proj', np.round(np.percentile(sh[:, 0], [5, 50, 95]), 3), 'Nett', np.round(np.percentile(sh[:, 1], [5, 50, 95]), 3), 'Spd', np.round(np.percentile(sh[:, 2], [5, 50, 95]), 3))
