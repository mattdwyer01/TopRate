"""Which unused runner-page fields still carry information about the next rating? (22 Oct 2026). Runner-page ATW ratings only. Baseline = the live context model's inputs
(projection/ctx.py FEATS). Each family below is added on its own, then all together; model fit before 2026-01-01 (early stop 2025-10..12), scored on 35k held-out 2026 runs;
paired squared-error gain per run with its standard error. Families: trainer (shrunk mean formula miss of the trainer's earlier page runs), race value (prize money and its change),
gear (blinkers today and first-time), pace shape of the last run's race, last run's running style (positions and margins at 800/600/400/200m), last run's sectional speeds,
set-weights vs handicap. Everything from earlier runs is as of before the run. Run: PYTHONPATH=. python research/proj_unused_fields.py"""
import glob, gzip, json, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'projection'))
import ctx as C

rp = C.training_frame()
pg = rp[rp.f.notna()].copy().sort_values(['horse_id', 'date']).reset_index(drop=True)
rows = []
for f in sorted(glob.glob('data/tr_form/*.json.gz')):
    for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
        if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
        sr = r.get('sectionalRating') or {}
        rows.append(dict(horse_id=r['horse_id'], date=r['date'], trainer=r.get('trainer'), prize=r.get('prizeMoney'), blk=r.get('blinkersOn'), wrest=r.get('weightRestriction'),
                         shE=r.get('raceShapeEarly'), shM=r.get('raceShapeMid'), shL=r.get('raceShapeLate'), p800=r.get('position800m'), p600=r.get('position600m'), p400=r.get('position400m'),
                         m800=r.get('margin800m'), m600=r.get('margin600m'), m400=r.get('margin400m'), m200=r.get('margin200m'), starters=r.get('starters'),
                         s_fin=sr.get('individualLast200mSpeed'), s_400=sr.get('individualEarlySpeed'), s_600=sr.get('individualLast600mSpeed'), s_800=sr.get('individualLast400mSpeed'),
                         letup=r.get('isLetup'), spell=r.get('isSpell')))
x = pd.DataFrame(rows); x['horse_id'] = pd.to_numeric(x.horse_id, errors='coerce'); x['date'] = pd.to_datetime(x.date)
x = x.drop_duplicates(['horse_id', 'date'], keep='last')
print('sectional keys seen (sample):', [k for k in (json.load(gzip.open(sorted(glob.glob('data/tr_form/2026-0*.json.gz'))[-2], 'rt'))['runs'].values().__iter__().__next__().get('sectionalRating') or {}).keys()][:12])
for c in ('s_fin', 's_400', 's_600', 's_800'): x[c] = pd.to_numeric(x[c], errors='coerce')
pg = pg.merge(x, on=['horse_id', 'date'], how='left')
pg['resid_f'] = pg.resid
# trainer effect, strictly before the date
t = pg[pg.trainer.notna()].groupby(['trainer', 'date']).resid.agg(['sum', 'count']).reset_index().sort_values(['trainer', 'date'])
t['cs'] = t.groupby('trainer')['sum'].cumsum() - t['sum']; t['cn'] = t.groupby('trainer')['count'].cumsum() - t['count']
pg = pg.merge(t[['trainer', 'date', 'cs', 'cn']].rename(columns={'cs': 'tcs', 'cn': 'tcn'}), on=['trainer', 'date'], how='left')
pg['trn_eff'] = pg.tcs.fillna(0) / (pg.tcn.fillna(0) + 20.0); pg['trn_n'] = pg.tcn.fillna(0)
# race value and gear
pg['lprize'] = np.log1p(pd.to_numeric(pg.prize, errors='coerce'))
g = pg.groupby('horse_id')
pg['prize_chg'] = pg.lprize - g.lprize.shift(1)
pg['blk_n'] = pg.blk.map({True: 1, False: 0, 1: 1, 0: 0}).astype(float)
pg['blk_chg'] = pg.blk_n - g.blk_n.shift(1)
pg['wr_hcp'] = (pg.wrest.astype(str) == 'HCP').astype(float).where(pg.wrest.notna())
# last run's race shape, style, sectionals (shifted by one within the horse); last-3 mean for the style and closing speed
for c in ('shE', 'shM', 'shL', 's_fin', 's_400', 's_600', 's_800', 'm600', 'm200'):
    pg['L_' + c] = g[c].shift(1)
pg['L_p800f'] = (pg.p800 / pg.starters); pg['L_p800f'] = pg.groupby('horse_id').L_p800f.shift(1)
pg['L_p600f'] = (pg.p600 / pg.starters); pg['L_p600f'] = pg.groupby('horse_id').L_p600f.shift(1)
pg['fin_vs_600'] = pg.m600 - pg.marginFinish.clip(lower=0); pg['L_close'] = pg.groupby('horse_id').fin_vs_600.shift(1)
pg['L3_close'] = pg.groupby('horse_id').fin_vs_600.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
pg['L3_p600f'] = pg.groupby('horse_id').L_p600f.transform(lambda s: s.rolling(3, min_periods=1).mean())
pg['L3_s_fin'] = pg.groupby('horse_id').s_fin.transform(lambda s: s.shift(1).rolling(3, min_periods=1).mean())
classes = sorted(pg.cls.dropna().unique().tolist()); pg['cls_c'] = C._cls(pg.cls, classes)
FAM = {'trainer': ['trn_eff', 'trn_n'], 'race value': ['lprize', 'prize_chg'], 'gear': ['blk_n', 'blk_chg'], 'set weights vs handicap': ['wr_hcp'],
       'last race pace shape': ['L_shE', 'L_shM', 'L_shL'], 'last run style': ['L_p800f', 'L_p600f', 'L3_p600f', 'L_m600', 'L_m200', 'L_close', 'L3_close'], 'last run sectionals': ['L_s_fin', 'L_s_400', 'L_s_600', 'L_s_800', 'L3_s_fin']}
cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
te['race'] = te.date.astype(str) + '|' + te.track.astype(str) + '|' + te.distance.astype(str) + '|' + te.field_size.astype(str) + '|' + te.race_class.astype(str)
def run(feats):
    m = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
    return te.resid - m.predict(te[feats]), m
base_e, _ = run(C.FEATS)
big = te.groupby('race').resid.transform('size') >= 4
def within(e): te['_e'] = e; return np.sqrt(((e - te.groupby('race')._e.transform('mean'))[big] ** 2).mean())
print(f"held-out runs {len(te):,}; coverage of each family (share of held-out runs with the key input): " + ', '.join(f"{k} {100*te[v[0]].notna().mean():.0f}%" for k, v in FAM.items()))
print(f"\n{'inputs added':28s} {'RMSE':>7s} {'within-race':>12s} {'gain pts^2/run':>15s} {'se':>6s}")
print(f"{'live context only':28s} {np.sqrt((base_e**2).mean()):7.4f} {within(base_e):12.4f}")
allf = []
for k, v in FAM.items():
    e, _ = run(C.FEATS + v); allf += v; d = base_e ** 2 - e ** 2
    print(f"{'+ ' + k:28s} {np.sqrt((e**2).mean()):7.4f} {within(e):12.4f} {d.mean():+15.3f} {d.std()/np.sqrt(len(d)):6.3f}")
e, m = run(C.FEATS + allf); d = base_e ** 2 - e ** 2
print(f"{'+ all families':28s} {np.sqrt((e**2).mean()):7.4f} {within(e):12.4f} {d.mean():+15.3f} {d.std()/np.sqrt(len(d)):6.3f}")
imp = pd.Series(m.booster_.feature_importance('gain'), index=C.FEATS + allf).sort_values(ascending=False); imp /= imp.sum()
print('top inputs by gain share in the full model:', {k: round(float(v), 3) for k, v in imp.head(10).items()})
