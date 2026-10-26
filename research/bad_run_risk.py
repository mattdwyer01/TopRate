"""Bad-run risk model (26 Oct 2026): can pre-race information say which runs will fall far short of the Proj?

Target: a run's rating more than 12 below the formula figure (resid < -12, about 7.5% of runs; 9.4% of runs carry 66% of the squared miss, and 2,587 of
3,306 big misses were below). Runner-page ATW ratings only (the Proj rule). Fit before 2026-01-01 (early stop on 2025-10..12), scored on 2026 runs.
Baseline = the live context inputs (`projection/ctx.FEATS`). Added one family at a time, as the page record of each run holds them (all known before the race):

  A  the horse's own bad-run history: last miss, mean and spread of the last 4, bad runs in the last 4 and 8, shrunk bad-run rate, runs and days since a bad
     run, whether the last run carried an excuse (steward and video comments: vet, lame, bled, slow away, checked, resented ...)
  B  today's gear: blinkers on, blinkers first time, any first-time gear, number of changes, blinkers change from the last run
  C  connections as of the day before: trainer and jockey shrunk bad-run rate (all time and last 60 days) and the trainer's mean miss over the last 60 days
  D  prep: runs since a spell of 60+ days, length of the spell, first or second up
  F  condition record: the horse's earlier bad-run rate in the wet and at this distance band (shrunk)
  E  early market: log opening and mid price (the page record's priceOpening / priceMid, where filled)

Reports AUC, rate in the riskiest decile against the average, and a mean-model ablation (RMSE and MAE with the families added) on the same split.

  PYTHONPATH=. python research/bad_run_risk.py
"""
import os
import re
import sys

import lightgbm as lgb
import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(ROOT, 'projection'))
import ctx as C  # noqa: E402

BAD = -12.0
EXC = re.compile(r'vet|lame|bled|bleed|arrhythm|cardiac|slow(ly)? (away|into)|missed the start|fell|checked|blocked|held up|ran wide|hung|resent|failed to|did not (handle|stay)|pulled|raced keenly|tailed|amiss|sore|injur|lost (a )?shoe|tongue', re.I)
SHRINK_N = 20.0
PRIOR_BAD = 0.075


def load_extras():
    import glob
    import gzip
    import json
    rows = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'tr_form', '*.json.gz'))):
        with gzip.open(f, 'rt') as fh:
            for r in json.load(fh).get('runs', {}).values():
                if r.get('isBarrierTrial') or r.get('isJumpout') or r.get('wpr') is None:
                    continue
                gc = r.get('gearChanges') or []
                gtxt = ' | '.join(gc) if isinstance(gc, list) else str(gc)
                rows.append(dict(horse_id=r['horse_id'], date=r['date'], trainer=r.get('trainer'), blink=1.0 if r.get('blinkersOn') else 0.0,
                                 gear_n=float(len(gc)) if isinstance(gc, list) else np.nan, gear_first=1.0 if 'First Time' in gtxt else 0.0,
                                 blink_first=1.0 if re.search(r'blinkers?[^|]*first time', gtxt, re.I) else 0.0,
                                 po=r.get('priceOpening'), pm=r.get('priceMid'),
                                 cmt=((r.get('commentsSteward') or '') + ' ' + (r.get('commentsVideo') or '')).strip()))
    e = pd.DataFrame(rows)
    e['horse_id'] = pd.to_numeric(e.horse_id, errors='coerce')
    e['date'] = pd.to_datetime(e.date)
    e = e.dropna(subset=['horse_id', 'date']).drop_duplicates(['horse_id', 'date'], keep='last')
    e['exc'] = e.cmt.map(lambda s: 1.0 if EXC.search(s or '') else 0.0)
    for c in ('po', 'pm'):
        e[c] = pd.to_numeric(e[c], errors='coerce')
        e['l' + c] = np.log(e[c].where(e[c] > 1))
    return e


def asof_rate(df, key, flag, window_days=None, prior=PRIOR_BAD, k=SHRINK_N, value=None):
    """Shrunk mean of `flag` (or `value`) over the earlier rows with the same `key`, strictly before each row's date (cumulative, or the last `window_days`)."""
    v = df[value] if value else df[flag].astype(float)
    t = pd.DataFrame({'key': df[key].values, 'date': df.date.values, 'v': v.values}).dropna(subset=['key', 'v'])
    a = t.groupby(['key', 'date']).v.agg(['sum', 'count']).reset_index().sort_values(['key', 'date'])
    a['cs'] = a.groupby('key')['sum'].cumsum()
    a['cn'] = a.groupby('key')['count'].cumsum()
    q = pd.DataFrame({'key': df[key].values, 'date': df.date.values, '_i': np.arange(len(df))})
    m = pd.merge_asof(q.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
    cs, cn = m.cs.fillna(0).values, m.cn.fillna(0).values
    if window_days:
        q2 = q.assign(date=q.date - pd.Timedelta(days=window_days))
        m2 = pd.merge_asof(q2.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
        cs, cn = cs - m2.cs.fillna(0).values, cn - m2.cn.fillna(0).values
    out = pd.Series((cs + prior * k) / (cn + k), index=m._i.values).sort_index()
    cnt = pd.Series(cn, index=m._i.values).sort_index()
    return out.values, cnt.values


def build():
    rp = C.training_frame()
    pg = rp[rp.f.notna()].copy()
    pg = pg.merge(load_extras(), on=['horse_id', 'date'], how='left')
    pg = pg.sort_values(['horse_id', 'date']).reset_index(drop=True)
    pg['bad'] = (pg.resid < BAD).astype(float)
    g = pg.groupby('horse_id')
    # A
    lags = pd.concat([g.resid.shift(k) for k in range(1, 9)], axis=1)
    lags.columns = range(8)
    pg['a_p1'] = lags[0]
    pg['a_m4'] = lags.iloc[:, :4].mean(axis=1)
    pg['a_sd4'] = lags.iloc[:, :4].std(axis=1)
    pg['a_bad4'] = (lags.iloc[:, :4] < BAD).sum(axis=1).where(lags.iloc[:, :4].notna().any(axis=1))
    pg['a_bad8'] = (lags < BAD).sum(axis=1).where(lags.notna().any(axis=1))
    cb = g.bad.cumsum() - pg.bad
    cn = g.cumcount()
    pg['a_rate'] = (cb + PRIOR_BAD * 5) / (cn + 5)
    last_bad_idx = pg.index.to_series().where(pg.bad == 1)
    pg['_lb'] = last_bad_idx.groupby(pg.horse_id).ffill().groupby(pg.horse_id).shift(1)
    pg['a_runs_since_bad'] = (pg.index.to_series() - pg._lb)
    pg['a_days_since_bad'] = (pg.date - pg.date.where(pg.bad == 1).groupby(pg.horse_id).ffill().groupby(pg.horse_id).shift(1)).dt.days
    pg['a_prev_exc'] = g.exc.shift(1)
    pg['a_prev_bad_exc'] = (g.bad.shift(1) * pg.a_prev_exc)
    pg['a_prev_bad_unexc'] = (g.bad.shift(1) * (1 - pg.a_prev_exc))
    A = ['a_p1', 'a_m4', 'a_sd4', 'a_bad4', 'a_bad8', 'a_rate', 'a_runs_since_bad', 'a_days_since_bad', 'a_prev_exc', 'a_prev_bad_exc', 'a_prev_bad_unexc']
    # B
    pg['b_blink_prev'] = g.blink.shift(1)
    pg['b_blink_chg'] = pg.blink - pg.b_blink_prev
    B = ['blink', 'blink_first', 'gear_first', 'gear_n', 'b_blink_prev', 'b_blink_chg']
    # C
    pg['trainer'] = pg.trainer.fillna('?')
    pg['jock'] = pg.jockey.fillna('?').astype(str)
    pg['c_tr_rate'], pg['c_tr_n'] = asof_rate(pg, 'trainer', 'bad')
    pg['c_tr_rate60'], pg['c_tr_n60'] = asof_rate(pg, 'trainer', 'bad', window_days=60)
    pg['c_tr_miss60'], _ = asof_rate(pg, 'trainer', None, window_days=60, prior=0.0, value='resid')
    pg['c_jk_rate'], pg['c_jk_n'] = asof_rate(pg, 'jock', 'bad')
    Cc = ['c_tr_rate', 'c_tr_n', 'c_tr_rate60', 'c_tr_n60', 'c_tr_miss60', 'c_jk_rate', 'c_jk_n']
    # D
    gap = (pg.d_last > 60) | pg.d_last.isna()
    pg['_prep_id'] = gap.groupby(pg.horse_id).cumsum()
    pg['d_prep_n'] = pg.groupby(['horse_id', '_prep_id']).cumcount().astype(float)
    pg['d_spell'] = pg.d_last.where(pg.d_last > 60, 0.0)
    D = ['d_prep_n', 'd_spell']
    # F
    pg['wet'] = (pg.going_n >= 5).astype(float)
    pg['dband'] = pd.cut(pg.distance, [0, 1250, 1650, 2100, 9999], labels=False)
    for name, col in (('wet', 'wet'), ('dband', 'dband')):
        k = pg.horse_id.astype(str) + '|' + pg[col].astype(str)
        pg['f_' + name], pg['f_' + name + '_n'] = asof_rate(pg.assign(_k=k), '_k', 'bad')
    Ff = ['f_wet', 'f_wet_n', 'f_dband', 'f_dband_n']
    # E
    Ee = ['lpo', 'lpm']
    return pg, dict(A=A, B=B, C=Cc, D=D, F=Ff, E=Ee)


def main():
    pg, fam = build()
    print('runs', len(pg), 'bad rate %.3f' % pg.bad.mean(), '| price coverage open %.2f mid %.2f' % (pg.lpo.notna().mean(), pg.lpm.notna().mean()))
    classes = sorted(pg.cls.dropna().unique().tolist())
    pg['cls_c'] = C._cls(pg.cls, classes)
    cut, es = pd.Timestamp('2026-01-01'), pd.Timestamp('2025-10-01')
    tr, va, te = pg[pg.date < es], pg[(pg.date >= es) & (pg.date < cut)], pg[pg.date >= cut].copy()
    P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=100, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
    base = list(C.FEATS)
    yb = pg.bad.astype(int)
    print('train %d, valid %d, test %d (2026), test bad rate %.3f' % (len(tr), len(va), len(te), te.bad.mean()))

    def run(cols, label):
        m = lgb.LGBMClassifier(n_estimators=3000, **P).fit(tr[cols], yb[tr.index], eval_set=[(va[cols], yb[va.index])], callbacks=[lgb.early_stopping(100, verbose=False)])
        p = m.predict_proba(te[cols])[:, 1]
        auc = roc_auc_score(te.bad.astype(int), p)
        top = te.assign(p=p).nlargest(len(te) // 10, 'p').bad.mean()
        bot = te.assign(p=p).nsmallest(len(te) // 10, 'p').bad.mean()
        print(f'  {label:44s} AUC {auc:.3f}  riskiest decile {100 * top:5.1f}%  safest decile {100 * bot:4.1f}%  (average {100 * te.bad.mean():.1f}%)  trees {m.best_iteration_}')
        return m, p

    print('\nbad-run classifier (resid < -12)')
    run(base, 'baseline (live context inputs)')
    for k, name in (('A', 'A own bad-run history'), ('B', 'B today gear'), ('C', 'C trainer and jockey rates'), ('D', 'D prep and spell'), ('F', 'F wet and distance record'), ('E', 'E early market price')):
        run(base + fam[k], '+ ' + name)
    allf = base + fam['A'] + fam['B'] + fam['C'] + fam['D'] + fam['F']
    m_all, p_all = run(allf, '+ A B C D F (no market)')
    m_full, p_full = run(allf + fam['E'], '+ A B C D F + E market')
    imp = pd.Series(m_full.booster_.feature_importance('gain'), index=allf + fam['E']).sort_values(ascending=False)
    print('  top inputs (share of gain):', (imp / imp.sum()).round(3).head(10).to_dict())
    te['p_all'] = p_all
    te['dec'] = pd.qcut(te.p_all.rank(method='first'), 10, labels=False)
    cal = te.groupby('dec').agg(pred=('p_all', 'mean'), actual=('bad', 'mean'), miss=('resid', 'mean'))
    print('\ncalibration by predicted-risk decile (A B C D F):'); print((cal * [100, 100, 1]).round(1).to_string())

    # mean-model ablation
    print('\nmean model (resid), same split')
    for cols, label in ((base, 'baseline'), (allf, '+ A B C D F'), (allf + fam['E'], '+ A B C D F + E')):
        mr = lgb.LGBMRegressor(n_estimators=3000, **P).fit(tr[cols], tr.resid, eval_set=[(va[cols], va.resid)], callbacks=[lgb.early_stopping(100, verbose=False)])
        e = te.resid - mr.predict(te[cols])
        print(f'  {label:20s} RMSE {np.sqrt((e ** 2).mean()):.3f}  MAE {e.abs().mean():.3f}  median {e.median():+.2f}  trees {mr.best_iteration_}')
    te.to_pickle(os.environ.get('BR_OUT', '/tmp/bad_run_risk_test.pkl'))


if __name__ == '__main__':
    main()
