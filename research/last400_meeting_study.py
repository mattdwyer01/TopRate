"""Meeting track speed idea (26 Oct 2026): do the EARLIER races at the same meeting tell us how this race's last 400m will go?
Race-level leans from earlier races of the meeting (needs 2+; VIC/SA live GPS): lead lean (corr of position at 800m with finish, + = leaders did better),
fence lean (corr of width off the rail with finish, - = fence did better), fade lean (corr of early deficit with last-400m deficit, + = fast-early horses faded),
and the mean absolute last-400m time of earlier races against par for the distance (a closing-speed 'track speed'). Interactions with the runner's own
style (history early rank relative to the field, barrier, expected width) are added to the study-2 field-relative model. R2 on 2025 on.
  PYTHONPATH=. python research/last400_meeting_study.py
"""
import glob, os, sys
import lightgbm as lgb, numpy as np, pandas as pd
sys.path.insert(0, os.path.dirname(__file__))
import last400_predictors_study2 as S2
import closing_stage_study as CS
d, allc, Hc, Rc = S2.d, S2.allc, S2.Hc, S2.Rc
r = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'tab_no', 'rail_avg_m']) for f in sorted(glob.glob(os.path.join(CS.GPS, 'rc_gps_runs_*.parquet')))], ignore_index=True)
r['meet_code'] = r.meet_code.astype(str); r['rail_avg_m'] = pd.to_numeric(r.rail_avg_m, errors='coerce')
s = pd.concat([pd.read_parquet(f, columns=['meet_code', 'race_no', 'tab_no', 'from_m', 'pos']) for f in sorted(glob.glob(os.path.join(CS.GPS, 'rc_gps_sections_*.parquet')))], ignore_index=True)
s['meet_code'] = s.meet_code.astype(str)
s = s[(s.from_m >= 780) & (s.from_m <= 820)].groupby(['meet_code', 'race_no', 'tab_no']).pos.first().rename('pos800').reset_index()
d = d.merge(r, on=['meet_code', 'race_no', 'tab_no'], how='left').merge(s, on=['meet_code', 'race_no', 'tab_no'], how='left')
d['t_L_abs'] = d.t_L
rows = []
for k, x in d.groupby('key'):
    def c(a, b, m='spearman'):
        z = x[[a, b]].dropna()
        return z[a].corr(z[b], method=m) if len(z) >= 6 else np.nan
    rows.append(dict(key=k, meet_code=x.meet_code.iloc[0], race_no=x.race_no.iloc[0], dist=x.dist.iloc[0],
                     lead=-c('pos800', 'finish'), fence=c('rail_avg_m', 'finish'), fade=c('d_E', 'd_L', 'pearson'), L_abs=x.t_L.mean()))
R = pd.DataFrame(rows).sort_values(['meet_code', 'race_no'])
R['L_par'] = R.L_abs - R.groupby(pd.cut(R.dist, [0, 1150, 1450, 1850, 2300, 9999])).L_abs.transform('mean')
gm = R.groupby('meet_code')
for c in ('lead', 'fence', 'fade', 'L_par'):
    R['m_' + c] = gm[c].transform(lambda v: v.shift(1).expanding().mean())
R['m_n'] = gm.cumcount()
d = d.merge(R[['key', 'm_lead', 'm_fence', 'm_fade', 'm_L_par', 'm_n']], on='key', how='left')
d.loc[d.m_n < 2, ['m_lead', 'm_fence', 'm_fade', 'm_L_par']] = np.nan
# runner style relative to field, interactions
d['style'] = d.r_h_E if 'r_h_E' in d.columns else d.h_E - d.groupby('key').h_E.transform('mean')
d['x_fade'] = d.m_fade * d.style
d['x_lead'] = d.m_lead * -d.style
d['x_fence'] = d.m_fence * (d.barfrac - 0.5)
M = ['m_lead', 'm_fence', 'm_fade', 'm_L_par', 'x_fade', 'x_lead', 'x_fence']
print('earlier-race meeting leans: mean (sd) lead %.2f (%.2f), fence %.2f (%.2f), fade %.2f (%.2f)' % tuple(v for c in ('lead', 'fence', 'fade') for v in (R[c].mean(), R[c].std())))
print('carry-over corr (race lean vs mean of earlier races): ' + ', '.join(f'{c} {R[c].corr(R["m_" + c]):+.2f}' for c in ('lead', 'fence', 'fade', 'L_par')))
cols0 = allc + Rc
P = dict(learning_rate=0.03, num_leaves=31, min_child_samples=150, subsample=0.8, subsample_freq=1, colsample_bytree=0.5, reg_lambda=10, verbose=-1, n_estimators=3000)
tr = d[(d.date < '2024-07-01') & d.h_E.notna()]; va = d[(d.date >= '2024-07-01') & (d.date < '2025-01-01') & d.h_E.notna()]; te = d[(d.date >= '2025-01-01') & d.h_E.notna()]
print(f'fit {len(tr):,} test {len(te):,}; test rows with meeting leans {te.m_lead.notna().mean():.0%}')
for nm, cols in (('study-2 B (field-relative)', cols0), ('+ meeting leans and interactions', cols0 + M)):
    for tgt in ('L', 'T'):
        m = lgb.LGBMRegressor(**P).fit(tr[cols], tr[f'd_{tgt}'], eval_set=[(va[cols], va[f'd_{tgt}'])], callbacks=[lgb.early_stopping(100, verbose=False)])
        pr = m.predict(te[cols]); y = te[f'd_{tgt}']; q = te.m_lead.notna().values
        r2 = lambda yy, pp: 1 - ((yy - pp) ** 2).sum() / ((yy - yy.mean()) ** 2).sum()
        print(f'{nm:36s} {tgt}: R2 all {r2(y, pr):.4f}, races with 2+ earlier at meeting {r2(y[q], pr[q]):.4f}', flush=True)
