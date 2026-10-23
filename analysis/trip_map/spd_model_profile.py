"""GPS running-profile history inside the shipped rebuilt Spd model (23 Oct 2026). Same build as speed_model.train() (formula + context + relevance on speed figures, fit 2023-07 to 2025,
held out 2026), with and without the profile inputs (early / mid / finishing speed, kick, fade, peak speed, positions, lane, stride; mean of the last 3 and 8 GPS runs as of the race).
Reports held-out RMSE and full-field winner accuracy (model only, no price). Run after gps_profile.py: PYTHONPATH=. python analysis/trip_map/spd_model_profile.py"""
import os, sys, warnings
import numpy as np, pandas as pd, lightgbm as lgb
from scipy.optimize import minimize_scalar
warnings.filterwarnings('ignore')
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..')); sys.path.insert(0, os.path.dirname(__file__))
import speed_model as SM
from projection import ctx as C
import build_trip_map as B
OUTP = '/tmp/spd_model_profile_te.parquet'
H = pd.read_parquet('/tmp/gps_profile_hist.parquet'); H['hdate'] = H.hdate.astype('datetime64[ns]'); H = H.sort_values('hdate')
PFH = [c for c in H.columns if c.startswith(('pf3_', 'pf8_'))] + ['pf_n']
if not os.path.exists(OUTP):
    rp = SM.frame(); co = SM.fit_formula(rp, SM.CUT); rp = SM.prepare(rp, co); rp = C.add_jockey(rp, C.jockey_table(rp)); rp = C.add_venue(rp, rp)
    classes = sorted(rp.cls.dropna().unique().tolist()); rp['cls_c'] = C._cls(rp.cls, classes)
    need = rp[(rp.date >= SM.TR_FROM) & rp.f.notna()]
    need = pd.concat([need, C.rel_features(need, rp)], axis=1)
    need['hn'] = B.clean_name(need.key); need['date'] = need.date.astype('datetime64[ns]')
    need = need.sort_values('date')
    need = pd.merge_asof(need, H, left_on='date', right_on='hdate', by='hn', allow_exact_matches=False, tolerance=pd.Timedelta(days=900)).drop(columns='hdate')
    F0, F1 = C.FEATS, C.FEATS + C.REL_FEATS
    tr, va, te = need[need.date < SM.ES_FROM], need[(need.date >= SM.ES_FROM) & (need.date < SM.CUT)], need[need.date >= SM.CUT].copy()
    def fitm(feats, rel_only):
        a, b = (tr[tr.n >= C.REL_MIN_RUNS], va[va.n >= C.REL_MIN_RUNS]) if rel_only else (tr, va)
        return lgb.LGBMRegressor(n_estimators=4000, **SM.P).fit(a[feats], a.resid, eval_set=[(b[feats], b.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    for tag, extra in (('base', []), ('prof', PFH)):
        m0, m1 = fitm(F0 + extra, False), fitm(F1 + extra, True)
        te['p_' + tag] = np.where(te.n >= C.REL_MIN_RUNS, te.f + m1.predict(te[F1 + extra]), te.f + m0.predict(te[F0 + extra]))
        print(tag, 'trees', m0.best_iteration_, m1.best_iteration_, flush=True)
    te[['key', 'hn', 'date', 'race_id', 'wpr', 'n', 'positionFinish', 'p_base', 'p_prof', 'pf_n']].to_parquet(OUTP)
te = pd.read_parquet(OUTP)
r = lambda x: float(np.sqrt(np.nanmean(np.asarray(x) ** 2)))
big = te.groupby('race_id').wpr.transform('size') >= 5
print('\nHELD OUT 2026 speed figures: n', len(te))
for lab, msk in (('all runs', np.ones(len(te), bool)), ('runs with GPS profile history', te.pf_n.notna().values)):
    d = te[msk]; eb, ep = d.wpr - d.p_base, d.wpr - d.p_prof
    wb = (eb - eb.groupby(d.race_id).transform('mean'))[big[msk]]; wp = (ep - ep.groupby(d.race_id).transform('mean'))[big[msk]]
    s = eb ** 2 - ep ** 2
    print(f'  {lab:30s} n={len(d):6d} RMSE base {r(eb):.4f} -> profile {r(ep):.4f} | within-race {r(wb):.4f} -> {r(wp):.4f} | sq-error gain {s.mean():+.4f} (se {s.std() / np.sqrt(len(s)):.4f})')
# winners, full fields
w = te.dropna(subset=['positionFinish']).copy(); w['win'] = (w.positionFinish == 1).astype(int)
sz = w.groupby('race_id').win.transform('size'); w = w[sz >= 6]
gb = w.groupby('race_id'); w = w[gb.win.transform('sum') == 1].copy()
w['share_prof'] = w.groupby('race_id').pf_n.transform(lambda s: s.notna().mean())
d0 = w.date.sort_values().iloc[len(w) // 2]
def ll(df, col, beta):
    s = beta * (df[col] - df.groupby('race_id')[col].transform('mean')); mx = s.groupby(df.race_id).transform('max'); ex = np.exp(s - mx); den = ex.groupby(df.race_id).transform('sum')
    return np.log(ex / den)[df.win == 1]
def cross(df, col):
    parts = []
    for a, b in ((df[df.date < d0], df[df.date >= d0]), (df[df.date >= d0], df[df.date < d0])):
        beta = minimize_scalar(lambda x: -ll(a, col, x).sum(), bounds=(0.001, 1), method='bounded').x; parts.append(ll(b, col, beta))
    return pd.concat(parts)
print('\nWINNERS (full fields, model only, beta cross-fitted by date halves)')
for lab, df in (('all races', w), ('races where >= 50% of runners have profile history', w[w.share_prof >= 0.5]), ('races where < 50% have it', w[w.share_prof < 0.5])):
    lb, lp = cross(df, 'p_base'), cross(df, 'p_prof'); dd = (lp - lb).dropna()
    tb = df[df.groupby('race_id').p_base.rank(ascending=False, method='first') == 1].win.mean(); tp = df[df.groupby('race_id').p_prof.rank(ascending=False, method='first') == 1].win.mean()
    print(f'  {lab:52s} races {df.race_id.nunique():5d} LL {lb.mean():.4f} -> {lp.mean():.4f} gain {dd.mean():+.4f} (se {dd.std() / np.sqrt(len(dd)):.4f}) | top pick {100 * tb:.1f}% -> {100 * tp:.1f}%')
