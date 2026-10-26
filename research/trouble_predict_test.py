"""Predicting trouble in running (26 Oct 2026): can getting CHECKED/BLOCKED or being KEEN/RESENTING be predicted from pre-race facts, and does the predicted risk matter?
Labels are the flags in the steward and video comments of the run itself (post-race, label only).  Inputs are strictly pre-race: the horse's earlier flag rates, barrier, field size,
predicted early position (as-of mean of position800m / field size) and the field's pace pressure (likely leaders), distance, going, track, days since run, first up, age, sex, blinkers,
first-time gear, weight, jockey and trainer as-of flag rates.  Results files 2019-2026-10-08, all states, trials and jump-outs out.
Part 1: AUC and lift for each flag (fit before 2024-07, early stop 2024 H2, scored 2025-01 on).  Part 2: does the predicted risk help predict a bad run (rating more than 12 below
the mean of the horse's last 3, a plain ability stand-in) beyond a baseline of the same inputs?  Part 3: how much of the bad-run excess after a flagged run is the flag itself.
  PYTHONPATH=. python research/trouble_predict_test.py
"""
import os, re, sys, warnings
warnings.filterwarnings('ignore')
import numpy as np, pandas as pd, lightgbm as lgb
from sklearn.metrics import roc_auc_score

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COLS = ['race_id', 'meeting_id', 'date', 'horse_id', 'barrier', 'distance', 'going', 'venue', 'track', 'jockey', 'trainer', 'weightCarried', 'horse_age', 'horse_sex', 'blinkers_on',
        'gear_changes', 'is_letup', 'is_spell', 'isBarrierTrial', 'is_jumpout', 'position800m', 'wpr', 'comments_steward', 'comments_video']
S = pd.concat([pd.read_csv(os.path.join(ROOT, f'race_results_{y}.csv.gz'), usecols=lambda c: c in COLS, low_memory=False) for y in range(2019, 2027)], ignore_index=True)
S = S[~S.isBarrierTrial.astype(bool) & ~S.is_jumpout.fillna(False).astype(bool)].copy()
S['date'] = pd.to_datetime(S.date)
S['horse_id'] = pd.to_numeric(S.horse_id, errors='coerce')
S = S.dropna(subset=['horse_id']).drop_duplicates(['race_id', 'horse_id']).sort_values(['horse_id', 'date', 'race_id']).reset_index(drop=True)
S['nr'] = S.groupby('race_id').horse_id.transform('size')
txt = (S.comments_steward.fillna('') + ' | ' + S.comments_video.fillna('')).str.lower()
BLOCK = r'check(ed)?\b|blocked|held up|no room|shut off|denied a run|hampered|interfer|bumped|crowded|squeezed|clipped'
KEEN = r'resent|failed to|raced (very )?keen|over.?rac|pulled hard|fought|did not (try|extend|respond)|ungenuine|\bkeen\b|pulling'
S['y_block'] = txt.str.contains(BLOCK, regex=True).astype(float)
S['y_keen'] = txt.str.contains(KEEN, regex=True).astype(float)
S['has_c'] = (txt.str.len() > 5).astype(float)
S = S[S.date < '2026-10-09']
print(f'{len(S):,} runs; comment present {100*S.has_c.mean():.0f}%; block {100*S.y_block.mean():.1f}%  keen {100*S.y_keen.mean():.1f}%')
S['pos'] = pd.to_numeric(S.position800m, errors='coerce')
S['e0'] = S.pos / S.nr
S['bf'] = (S.barrier - 1) / (S.nr - 1).clip(lower=1)
S['gs'] = pd.to_numeric(S.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
S['age'] = pd.to_numeric(S.horse_age, errors='coerce')
S['sex'] = S.horse_sex.astype(str).str.lower().str[:1].map({'g': 0, 'm': 1, 'f': 1, 'h': 2, 'c': 2, 'r': 2}).astype(float)
S['blink'] = S.blinkers_on.fillna(0).astype(float)
S['gear_first'] = S.gear_changes.astype(str).str.contains('First Time', case=False).astype(float)
S['wt'] = pd.to_numeric(S.weightCarried, errors='coerce')
S['vcode'] = S.venue.astype('category').cat.codes
S['dnum'] = pd.to_numeric(S.distance, errors='coerce')
g = S.groupby('horse_id')
S['days'] = (S.date - g.date.shift(1)).dt.days
S['firstup'] = (S.days > 60).astype(float)
S['nprev'] = g.cumcount().astype(float)
S['d_chg'] = S.dnum - g.dnum.shift(1)
S['wt_chg'] = S.wt - g.wt.shift(1)
# as-of horse rates (shrunk)
K = 5.0
for f in ('y_block', 'y_keen'):
    cs = g[f].cumsum() - S[f]
    S['h_' + f] = (cs + S[f].mean() * K) / (S.nprev + K)
S['h_nblock'] = g.y_block.cumsum() - S.y_block
S['h_nkeen'] = g.y_keen.cumsum() - S.y_keen
S['e_m4'] = g.e0.transform(lambda s: s.shift(1).rolling(4, min_periods=1).mean())
S['e_last'] = g.e0.shift(1)
# as-of jockey/trainer flag rates
def asof(key, f, k=60.0):
    d = S[[key, 'date', f]].copy(); d['i'] = np.arange(len(d))
    d = d.sort_values(['date']); d['cs'] = d.groupby(key)[f].cumsum() - d[f]; d['cn'] = d.groupby(key).cumcount()
    # same-day rows share the day's earlier rows; acceptable leakage-free approximation: use rows strictly before by date
    day = d.groupby([key, 'date']).agg(c=(f, 'sum'), n=(f, 'size')).reset_index().sort_values('date')
    day['cs'] = day.groupby(key).c.cumsum() - day.c; day['cn'] = day.groupby(key).n.cumsum() - day.n
    m = d[[key, 'date', 'i']].merge(day[[key, 'date', 'cs', 'cn']], on=[key, 'date'], how='left').sort_values('i')
    return ((m.cs + S[f].mean() * k) / (m.cn + k)).values
for key in ('jockey', 'trainer'):
    for f in ('y_block', 'y_keen'):
        S[f'{key[0]}_{f}'] = asof(key, f)
# field pace pressure from predicted early position
lead = (S.e_m4 < 0.3).astype(float)
S['n_lead'] = lead.groupby(S.race_id).transform('sum')
S['field_e'] = S.groupby('race_id').e_m4.transform('mean')
S['rank_e'] = S.groupby('race_id').e_m4.rank()
S['n_ahead_in'] = np.nan
S['crowd'] = (S.e_m4.between(0.25, 0.7)).groupby(S.race_id).transform('sum').astype(float)
# ability stand-in for part 2
S['wdev'] = S.wpr - S.groupby('race_id').wpr.transform('mean')
S['m3'] = g.wdev.transform(lambda s: s.shift(1).rolling(3, min_periods=2).mean())
S['miss'] = S.wdev - S.m3
S['bad'] = (S.miss < -12).astype(float).where(S.miss.notna())
FEAT = ['barrier', 'bf', 'nr', 'dnum', 'gs', 'vcode', 'days', 'firstup', 'nprev', 'd_chg', 'wt_chg', 'age', 'sex', 'blink', 'gear_first', 'wt', 'h_y_block', 'h_y_keen', 'h_nblock', 'h_nkeen',
        'e_m4', 'e_last', 'j_y_block', 'j_y_keen', 't_y_block', 't_y_keen', 'n_lead', 'field_e', 'rank_e', 'crowd']
S = S[S.has_c == 1].copy()
S['pred_block'] = np.nan; S['pred_keen'] = np.nan
P = dict(learning_rate=0.05, num_leaves=31, min_child_samples=200, subsample=0.8, subsample_freq=1, colsample_bytree=0.8, reg_lambda=5, verbose=-1)
tr, va, te = S[(S.date < '2024-07-01') & (S.date >= '2020-01-01')], S[(S.date >= '2024-07-01') & (S.date < '2025-01-01')], S[S.date >= '2025-01-01']
print(f'\npart 1: predict the flag from pre-race inputs. train {len(tr):,}  valid {len(va):,}  test {len(te):,}')
for f, nm in (('y_block', 'checked/blocked'), ('y_keen', 'keen/resenting')):
    m = lgb.LGBMClassifier(n_estimators=2000, **P).fit(tr[FEAT], tr[f], eval_set=[(va[FEAT], va[f])], callbacks=[lgb.early_stopping(80, verbose=False)])
    p = m.predict_proba(te[FEAT])[:, 1]
    S.loc[te.index, 'pred_' + f[2:]] = p
    auc = roc_auc_score(te[f], p)
    q = pd.qcut(pd.Series(p).rank(method='first'), 10, labels=False)
    r = te[f].reset_index(drop=True).groupby(q).mean() * 100
    print(f'\n {nm}: base rate {100*te[f].mean():.1f}%  AUC {auc:.3f}  rate by predicted-risk decile: ' + ' / '.join(f'{v:.1f}' for v in r))
    hist = roc_auc_score(te[f], te['h_' + f])
    print(f'   AUC of the horse\'s own earlier rate alone {hist:.3f}')
    imp = pd.Series(m.booster_.feature_importance('gain'), index=FEAT).sort_values(ascending=False); imp /= imp.sum()
    print('   top inputs:', {k: round(v, 3) for k, v in imp.head(10).items()})
# part 2: does predicted risk predict a bad run?
T = S[S.pred_block.notna() & S.bad.notna()].copy()
print(f'\npart 2: bad run (rating >12 below the horse\'s last-3 level), test-period runs {len(T):,}, bad rate {100*T.bad.mean():.1f}%')
print('  bad-run rate by predicted block risk quintile:', ' / '.join(f'{v:.1f}' for v in (T.bad.groupby(pd.qcut(T.pred_block.rank(method="first"), 5, labels=False)).mean() * 100)))
print('  bad-run rate by predicted keen risk quintile: ', ' / '.join(f'{v:.1f}' for v in (T.bad.groupby(pd.qcut(T.pred_keen.rank(method="first"), 5, labels=False)).mean() * 100)))
T = T.sort_values('date')
cut = T.date.quantile(0.5)
a, b = T[T.date < cut], T[T.date >= cut]
for cols, label in ((FEAT, 'baseline inputs'), (FEAT + ['pred_block', 'pred_keen'], '+ predicted block and keen risk')):
    m = lgb.LGBMClassifier(n_estimators=300, **P).fit(a[cols], a.bad)
    print(f'  {label:36s} AUC on second half {roc_auc_score(b.bad, m.predict_proba(b[cols])[:, 1]):.4f}')
# part 3: what the flag itself costs
print('\npart 3: the run\'s own flag vs its rating miss (post-race, for scale):')
for f in ('y_block', 'y_keen'):
    z = S[S.miss.notna()]
    print(f'  {f}: flagged runs miss {z[z[f] == 1].miss.mean():+.2f} (n={int(z[f].sum()):,}), others {z[z[f] == 0].miss.mean():+.2f}; bad rate {100*z[z[f]==1].bad.mean():.1f}% vs {100*z[z[f]==0].bad.mean():.1f}%')
