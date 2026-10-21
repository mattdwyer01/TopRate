"""GPS review (Triple S, VIC/SA from racing.com and QLD from Racing Queensland, data/gps): if the run's GPS facts were known before the race, would the live Proj
(formula + context, ATW runner-page ratings only) have been better, and how much is knowable? Target = ATW rating minus formula, baseline = ctx FEATS (as shape_counterfactual.py).
Own-run GPS features (hindsight): ground lost to the winner (dist_vs_winner_m), running line off the rail (VIC/SA rail_avg_m, QLD mean section rail_m), the run's early speed relative
to the field (first 400m sections), the race's early pace against the usual for its track and distance, and the run's position after the first sections.
NOT used: finish time, beaten margin, late and peak speed (the rating is computed from the margins and finish, so they give the answer away).
Knowable: the horse's own history of those (ground lost, line, early speed) from its earlier GPS runs. Run: PYTHONPATH=. python research/gps_counterfactual.py"""
import glob, gzip, json, re, sys
import numpy as np, pandas as pd, lightgbm as lgb
sys.path.insert(0, 'projection')
import ctx as C

norm = lambda s: s.astype(str).str.lower().str.replace(r'\([^)]*\)', '', regex=True).str.replace(r'[^a-z0-9]', '', regex=True)

def gps_runs():
    out = []
    for f in sorted(glob.glob('data/gps/rc_gps_runs_20*.parquet')):
        r = pd.read_parquet(f); s = pd.read_parquet(f.replace('runs', 'sections'))
        r['date'] = (pd.to_datetime(r.start_utc, utc=True) + pd.Timedelta(hours=10)).dt.tz_localize(None).dt.normalize()
        r['dist'] = pd.to_numeric(r.race_distance.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
        r['rail'] = r.rail_avg_m
        # sections run from the finish backwards: from_m large = early. first 400m of the race = sections with from_m >= dist - 400
        s = s.merge(r[['meet_code', 'race_no', 'dist']].drop_duplicates(), on=['meet_code', 'race_no'], how='left')
        e = s[s.from_m >= s.dist - 400].sort_values('from_m', ascending=False)   # explicit order: the last row is the 400m mark
        early = e.groupby(['meet_code', 'race_no', 'tab_no']).agg(early_speed=('avg_speed_ms', 'mean'), early_pos=('pos', 'last')).reset_index()
        r = r.merge(early, on=['meet_code', 'race_no', 'tab_no'], how='left')
        r['rk'] = 'rc' + r.meet_code.astype(str) + '_' + r.race_no.astype(str)
        r['n'] = r.groupby('rk').horse.transform('count')
        r['venue_k'] = r.venue
        r['race_no_'] = r.race_no; r['meet_'] = 'rc' + r.meet_code.astype(str)
        out.append(r[['date', 'horse', 'rk', 'n', 'venue_k', 'dist', 'dist_vs_winner_m', 'rail', 'early_speed', 'early_pos', 'finish', 'race_no_', 'meet_']].assign(src='rc'))
    for f in sorted(glob.glob('data/gps/rq_gps_runs_20*.parquet')):
        r = pd.read_parquet(f); s = pd.read_parquet(f.replace('runs', 'sections'))
        r['date'] = pd.to_datetime(r.race_date).dt.tz_localize(None).dt.normalize()
        key = ['race_code', 'tab_no']
        s = s.sort_values(['race_code', 'tab_no', 'cum_dist_m'])
        rl = s.groupby(key).rail_m.mean().rename('rail').reset_index()
        e = s[s.cum_dist_m <= 400]
        early = e.groupby(key).agg(early_speed=('avg_speed_ms', 'mean'), early_pos=('rank', 'last')).reset_index()
        dist = s.groupby('race_code').real_dist_m.max().rename('dist').reset_index()
        r = r.merge(rl, on=key, how='left').merge(early, on=key, how='left').merge(dist, on='race_code', how='left')
        r['rk'] = 'rq' + r.race_code.astype(str)
        r['n'] = r.groupby('rk').horse.transform('count')
        r['venue_k'] = r.course
        r['race_no_'] = r.race_no; r['meet_'] = 'rq' + r.meeting_code.astype(str)
        out.append(r[['date', 'horse', 'rk', 'n', 'venue_k', 'dist', 'dist_vs_winner_m', 'rail', 'early_speed', 'early_pos', 'finish', 'race_no_', 'meet_']].assign(src='rq'))
    g = pd.concat(out, ignore_index=True)
    g['hn'] = norm(g.horse)
    g = g.drop_duplicates(['date', 'hn'], keep='last')
    g['finish'] = g.finish.where((g.finish >= 1) & (g.finish <= g.n))   # 9% of runs carry a placeholder (2147483647) or a value beyond the field: not a finishing position
    g['gl'] = g.dist_vs_winner_m
    g['es_rel'] = g.early_speed - g.groupby('rk').early_speed.transform('mean')
    g['rail_rel'] = g.rail - g.groupby('rk').rail.transform('mean')
    g['ep_f'] = g.early_pos / g.n
    # race early pace against the usual for the same venue and distance (earlier races only, expanding mean)
    rp = g.groupby('rk').agg(date=('date', 'first'), v=('venue_k', 'first'), d=('dist', 'first'), ep=('early_speed', 'mean')).reset_index().sort_values('date')
    rp['dg'] = (rp.d / 100).round()
    rp['par'] = rp.groupby(['v', 'dg']).ep.transform(lambda s: s.shift(1).expanding(min_periods=5).mean())
    rp['race_pace'] = rp.ep - rp.par
    g = g.merge(rp[['rk', 'race_pace']], on='rk', how='left')
    return g

def main():
    rows = []
    for f in sorted(glob.glob('data/tr_form/*.json.gz')):
        for r in json.load(gzip.open(f, 'rt')).get('runs', {}).values():
            if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None: continue
            rows.append(dict(horse_id=r['horse_id'], date=r['date'], hname=r.get('horse'), p800=r.get('position800m')))
    X = pd.DataFrame(rows); X['horse_id'] = pd.to_numeric(X.horse_id, errors='coerce'); X['date'] = pd.to_datetime(X.date); X['hn'] = norm(X.hname)
    rp = C.training_frame().merge(X.drop_duplicates(['horse_id', 'date'], keep='last'), on=['horse_id', 'date'], how='left')
    rp['sf'] = rp.p800 / rp.field_size
    G = gps_runs()
    rp = rp.merge(G[['date', 'hn', 'gl', 'rail_rel', 'es_rel', 'race_pace', 'ep_f', 'src']], on=['date', 'hn'], how='left')
    print('GPS join: runs with GPS', int(rp.gl.notna().sum()), 'of', len(rp), ' by year:', rp.groupby(rp.date.dt.year).gl.apply(lambda s: round(s.notna().mean(), 2)).to_dict())
    rp = rp.sort_values(['horse_id', 'date']).reset_index(drop=True); g = rp.groupby('horse_id')
    for c, n in (('gl', 'h_gl'), ('rail_rel', 'h_rail'), ('es_rel', 'h_es'), ('ep_f', 'h_ep')):
        rp[n] = g[c].transform(lambda s: s.shift(1).rolling(4, min_periods=1).mean())
    HIST = ['h_gl', 'h_rail', 'h_es', 'h_ep']
    OWN = ['gl', 'rail_rel', 'es_rel', 'race_pace', 'ep_f']
    rp['cls_c'] = C._cls(rp.cls, sorted(rp.cls.dropna().unique().tolist()))
    pg = rp[rp.f.notna()].copy()
    cut, es_ = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
    # train and score on runs that HAVE GPS only, so the baseline sees the same runs (GPS meetings are a subset of venues)
    sub = pg[pg.gl.notna()]
    tr, va, te = sub[sub.date < es_], sub[(sub.date >= es_) & (sub.date < cut)], sub[sub.date >= cut]
    print('GPS runs: train', len(tr), 'valid', len(va), 'test', len(te))
    P = dict(n_estimators=3000, learning_rate=0.03, num_leaves=31, min_child_samples=60, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
    def fit(feats, seeds=3):
        p = []
        for s in range(seeds):
            m = lgb.LGBMRegressor(**P, random_state=s).fit(tr[feats], tr.resid, eval_set=[(va[feats], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
            p.append(m.predict(te[feats]))
        return np.mean(p, axis=0)
    rm = lambda e: float(np.sqrt(np.mean(e ** 2)))
    e0 = te.resid.values - fit(C.FEATS)
    print(f'baseline (context model, same GPS runs)      RMSE {rm(e0):.4f}')
    def rep(name, feats, mask=None):
        e = te.resid.values - fit(feats); m = np.ones(len(te), bool) if mask is None else mask
        d = e0[m] ** 2 - e[m] ** 2
        print(f'{name:50s} RMSE {rm(e[m]):.4f} (base {rm(e0[m]):.4f})  paired MSE gain {d.mean():+.2f} +-{1.96 * d.std() / np.sqrt(m.sum()):.2f}  n={m.sum()}')
    rep('A hindsight: all own GPS facts', C.FEATS + OWN)
    rep('  A1 ground lost only', C.FEATS + ['gl'])
    rep('  A2 running line off the rail only', C.FEATS + ['rail_rel'])
    rep('  A3 own early speed + position + race pace', C.FEATS + ['es_rel', 'ep_f', 'race_pace'])
    rep('  A4 race pace only (is the race fast early?)', C.FEATS + ['race_pace'])
    rep('  A5 early speed x race pace (+ settle from TopRate)', C.FEATS + ['es_rel', 'race_pace', 'ep_f', 'sf'])
    rep('B knowable: horse GPS history', C.FEATS + HIST, te.h_gl.notna().values)
    # how much of the miss does ground lost explain, directly
    t = te.assign(e0=e0)
    print('\ncorr of the miss (after live Proj) with ground lost:', round(np.corrcoef(t.e0[t.gl.notna()], t.gl[t.gl.notna()])[0, 1], 3), ' slope rating pts per metre', round(np.polyfit(t.gl[t.gl.notna()], t.e0[t.gl.notna()], 1)[0], 3))
    q = pd.cut(t.gl, [-100, -2, 2, 6, 12, 1000], labels=['shorter than winner', 'within 2m', '2-6m', '6-12m', '12m+'])
    print(t.groupby(q, observed=True).e0.agg(['mean', 'count']).round(2).T.to_string())
    q = pd.cut(t.race_pace, [-10, -0.4, 0.4, 10], labels=['slow early', 'normal', 'fast early'])
    print(t.groupby(q, observed=True).e0.agg(['mean', 'count']).round(2).T.to_string())

if __name__ == '__main__':
    main()
