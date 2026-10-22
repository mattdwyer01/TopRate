"""Deeper run-by-run study of the live Proj's misses (22 Oct 2026). Runner-page ATW ratings only; models fit before 2026-01-01, scored on 2026 runs.
(1) Horse-specific patterns under conditions: the horse's own earlier formula misses at this distance band, going group, track, after a similar spell, and with this jockey
(shrunk means, strictly before the run). (2) The rest of the field: the other runners' pre-race formula figures in the same race as the store holds it. (3) Is the size of the
miss predictable (heteroscedasticity)? (4) What the big under-performances look like: finish, price, steward words.
Run: PYTHONPATH=. python research/proj_horse_conditions.py"""
import os, re, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

rp = C.training_frame()
pg = rp[rp.f.notna()].copy().sort_values(['horse_id', 'date']).reset_index(drop=True)
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
pg['gg'] = pd.cut(pg.going_n, [-1, 3, 4, 7, 99], labels=False)
pg['db'] = (pg.distance / 200).round()
pg['fu'] = (pg.d_last > 60).astype(int)
K = 5.0
def cond(key, name):
    g = pg.groupby(['horse_id'] + key).resid
    cs = g.cumsum() - pg.resid; cn = g.cumcount()
    pg[name] = cs / (cn + K); pg[name + '_n'] = cn
for key, name in ((['db'], 'h_dist'), (['gg'], 'h_going'), (['track'], 'h_track'), (['fu'], 'h_spell'), (['jockey'], 'h_jock')):
    cond(key, name)
# the rest of the field in the same race as the store holds it (pre-race formula figures only)
pg['race'] = pg.date.astype(str) + '|' + pg.track.astype(str) + '|' + pg.distance.astype(str) + '|' + pg.field_size.astype(str) + '|' + pg.race_class.astype(str)
gs = pg.groupby('race').f
pg['fld_n'] = gs.transform('size') - 1
pg['fld_other'] = np.where(pg.fld_n > 0, (gs.transform('sum') - pg.f) / pg.fld_n.replace(0, np.nan), np.nan)
pg['f_vs_fld'] = pg.f - pg.fld_other
HC = ['h_dist', 'h_dist_n', 'h_going', 'h_going_n', 'h_track', 'h_track_n', 'h_spell', 'h_spell_n', 'h_jock', 'h_jock_n']
FL = ['fld_n', 'fld_other', 'f_vs_fld']
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
def fitpred(feats):
    m = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return m, m.predict(te[feats])
print(f"held-out runs {len(te):,}")
res = {}
for lab, feats in (('live (context only)', C.FEATS), ('+ horse patterns by condition', C.FEATS + HC), ('+ rest of field', C.FEATS + FL), ('+ both', C.FEATS + HC + FL)):
    m, p = fitpred(feats); e = te.resid - p; res[lab] = (m, feats, e)
    te['_e'] = e; w = e - te.groupby('race')._e.transform('mean')
    big = te.groupby('race').resid.transform('size') >= 4
    print(f"  {lab:32s} RMSE {np.sqrt((e**2).mean()):.4f}  within-race RMSE {np.sqrt((w[big]**2).mean()):.4f}  trees {m.best_iteration_}")
m, feats, _ = res['+ both']
imp = pd.Series(m.booster_.feature_importance('gain'), index=feats).sort_values(ascending=False); imp = imp / imp.sum()
print("  gain share of the new inputs in '+ both':", {k: round(float(imp[k]), 3) for k in HC + FL if imp[k] > 0.01})
base_e = res['live (context only)'][2]; both_e = res['+ both'][2]
d = (base_e ** 2 - both_e ** 2)
print(f"  paired squared-error gain '+ both' vs live: {d.mean():.3f} points^2 per run (se {d.std()/np.sqrt(len(d)):.3f}); by earlier runs:")
for lab, s in (('1-2', te.n <= 2), ('3-5', (te.n >= 3) & (te.n <= 5)), ('6-8', (te.n >= 6) & (te.n <= 8)), ('9+', te.n >= 9)):
    print(f"     {lab:4s} live {np.sqrt((base_e[s]**2).mean()):.3f}  both {np.sqrt((both_e[s]**2).mean()):.3f}")

print("\n[3] is the SIZE of the miss predictable?  (|miss| vs pre-race facts, fit on 2026-01..05, scored 2026-06+)")
te['e'] = base_e; te['ae'] = te.e.abs()
mid = pd.Timestamp('2026-06-01'); a, b = te[te.date < mid], te[te.date >= mid]
sf = C.FEATS + ['std4']
sf = list(dict.fromkeys(sf))
ms = lgb.LGBMRegressor(n_estimators=300, learning_rate=0.03, num_leaves=15, min_child_samples=200, subsample=.8, subsample_freq=1, colsample_bytree=.8, verbose=-1).fit(a[sf], a.ae)
b = b.assign(psd=ms.predict(b[sf])); q = pd.qcut(b.psd, 5, labels=False)
print("  predicted |miss| quintile -> actual RMSE:", b.groupby(q).e.apply(lambda s: round(float(np.sqrt((s**2).mean())), 2)).tolist(), " (flat = size not predictable)")
print("  by std4 (spread of the last four ratings):", b.groupby(pd.cut(b.std4, [-1, 2, 4, 6, 9, 99]), observed=True).e.apply(lambda s: round(float(np.sqrt((s**2).mean())), 2)).tolist())
print("  by projected level:", b.assign(pr=b.f).groupby(pd.cut(b.f, [0, 60, 70, 80, 90, 200]), observed=True).e.apply(lambda s: round(float(np.sqrt((s**2).mean())), 2)).tolist())

print("\n[4] what the big under-performances look like (miss below -12) against everything else")
bad = te[te.e < -12]; ok = te[te.e >= -12]
te['pf'] = te.positionFinish / te.field_size
print(f"  runs {len(bad):,}; finish place fraction mean {bad.positionFinish.div(bad.field_size).mean():.2f} vs {ok.positionFinish.div(ok.field_size).mean():.2f}; last 3 home {100*(bad.positionFinish >= bad.field_size - 2).mean():.0f}% vs {100*(ok.positionFinish >= ok.field_size - 2).mean():.0f}%")
sp = pd.to_numeric(te.priceStarting, errors='coerce')
print(f"  starting price median ${sp[bad.index].median():.1f} vs ${sp[ok.index].median():.1f}; ran as favourite-ish (under $4): {100*(sp[bad.index] < 4).mean():.0f}% vs {100*(sp[ok.index] < 4).mean():.0f}%")
print(f"  margin beaten median {bad.marginFinish.median():.1f} L vs {ok.marginFinish.median():.1f} L")
com = te.comments_steward.fillna('').astype(str)
has = com.str.len() > 3
print(f"  has a steward comment: {100*has[bad.index].mean():.1f}% of bad runs vs {100*has[ok.index].mean():.1f}% of the rest")
words = ['slow', 'slowly', 'checked', 'held up', 'blocked', 'tailed', 'vet', 'lame', 'bled', 'sore', 'tongue', 'shifted', 'hampered', 'wide', 'raced keenly', 'resented', 'failed to', 'galloped', 'interference', 'fell']
rows = []
for w_ in words:
    pb = com[bad.index].str.contains(w_, case=False, regex=False).mean(); po = com[ok.index].str.contains(w_, case=False, regex=False).mean()
    if pb > 0.005: rows.append((w_, 100 * pb, 100 * po, pb / max(po, 1e-9)))
print("  steward words (share of bad runs vs rest, lift):", [(w_, f"{a_:.1f}%", f"{b_:.1f}%", f"x{l_:.1f}") for w_, a_, b_, l_ in sorted(rows, key=lambda r: -r[3])[:8]])
print("  share of bad runs with any of those words:", f"{100*com[bad.index].str.contains('|'.join(words), case=False).mean():.0f}% vs {100*com[ok.index].str.contains('|'.join(words), case=False).mean():.0f}%")
