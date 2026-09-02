"""
wpr_trial_debut_scoping_check.py - initial scoping check (not yet a
leak-free validated test) for whether pre-debut trial/jumpout performance
predicts a horse's actual debut WPR - the structural gap flagged earlier
this session: horses with 0-2 real starts get NO base rating at all
(excluded outright by _MIN_RUNS), and trial/jumpout rows exist in the raw
form history but are currently filtered OUT of every training path
(_fit_pace_baseline excludes isBarrierTrial/is_jumpout rows explicitly).

WHAT THIS CHECKS (a quick correlation scope, before building anything):
  - How much pre-debut trial/jumpout data actually exists.
  - Whether trial finishing quality (position/field_size, margin - no WPR
    or sectional data is ever computed for trials, confirmed directly:
    0% wpr coverage) correlates at all with the horse's own subsequent
    real-race debut WPR.

RESULT: a real, meaningful correlation - avg trial finish percentile vs
debut WPR corr=0.27, won-a-trial vs debut WPR corr=0.20, n=8,430 horses
with both. Debut WPR climbs monotonically 62.6 (bottom trial-finish
quartile) -> 71.8 (top quartile), a 9-point spread. Also found: debutants
WITH a recorded trial average a LOWER debut WPR (67.75) than those with
NO trial at all (72.54) - likely a selection effect (trainers trial the
ones they're less sure about), not something trial performance itself
should be blamed for - any real base-rating model needs its own
trialled-horse baseline, not one borrowed from untrialled debutants.

NOT YET a leak-free validated test - this is purely a scoping check to
decide whether building a proper (K=4-fold, leak-free) debut base-rating
model off trial data is worth the effort. It clearly is; the follow-up
build is a separate, bigger piece of work.

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd
import numpy as np

df = pd.read_csv('wpr_form_history.csv.gz', low_memory=False,
                  usecols=['horse_id','horse','date','isBarrierTrial','is_jumpout',
                           'positionFinish','field_size','marginFinish','wpr'])
df['date'] = pd.to_datetime(df['date'], errors='coerce')
df = df.dropna(subset=['date', 'horse_id'])
df['is_trial'] = (df['isBarrierTrial'] == True) | (df['is_jumpout'] == True)
df = df.sort_values(['horse_id', 'date'])

# For each horse, find the first REAL race (is_trial==False) and how many
# trials/jumpouts happened strictly before it.
first_real = df[~df['is_trial']].groupby('horse_id')['date'].min().rename('first_real_date')
df = df.merge(first_real, on='horse_id', how='left')

pre_debut_trials = df[df['is_trial'] & (df['date'] < df['first_real_date'])]
print(f"Horses with >=1 pre-debut trial/jumpout: {pre_debut_trials['horse_id'].nunique():,}")
print(f"Total pre-debut trial/jumpout rows: {len(pre_debut_trials):,}")

n_trials_per_horse = pre_debut_trials.groupby('horse_id').size()
print(f"Median pre-debut trials per horse: {n_trials_per_horse.median()}  mean: {n_trials_per_horse.mean():.2f}")

# Horses with a debut real race AND at least one pre-debut trial - build a
# simple trial-performance summary and correlate with the debut's own wpr.
summary = pre_debut_trials.groupby('horse_id').agg(
    n_trials=('positionFinish', 'count'),
    best_pos=('positionFinish', 'min'),
    avg_pos_pct=('positionFinish', lambda s: None),  # placeholder, computed below
).reset_index()

# percentile finish per trial row, then averaged per horse
pre_debut_trials = pre_debut_trials.copy()
pre_debut_trials['finish_pct'] = 1 - (pre_debut_trials['positionFinish'] - 1) / pre_debut_trials['field_size'].clip(lower=1)
pct_summary = pre_debut_trials.groupby('horse_id')['finish_pct'].mean().rename('avg_finish_pct')
won_trial = (pre_debut_trials['positionFinish'] == 1).groupby(pre_debut_trials['horse_id']).max().rename('won_a_trial')

debut_rows = df[(~df['is_trial']) & (df['date'] == df['first_real_date'])].drop_duplicates(subset='horse_id')
debut_rows = debut_rows.set_index('horse_id')[['wpr', 'positionFinish', 'field_size']]
debut_rows.columns = ['debut_wpr', 'debut_pos', 'debut_field_size']

merged = debut_rows.join(n_trials_per_horse.rename('n_pre_trials'), how='inner') \
                    .join(pct_summary, how='left') \
                    .join(won_trial, how='left')
merged = merged.dropna(subset=['debut_wpr', 'avg_finish_pct'])
print(f"\nHorses with a debut WPR AND pre-debut trial data: {len(merged):,}")
print(f"correlation(avg_finish_pct in trials, debut_wpr): {merged['avg_finish_pct'].corr(merged['debut_wpr']):.4f}")
print(f"correlation(won_a_trial, debut_wpr): {merged['won_a_trial'].astype(float).corr(merged['debut_wpr']):.4f}")
print(f"correlation(n_pre_trials, debut_wpr): {merged['n_pre_trials'].corr(merged['debut_wpr']):.4f}")

print("\ndebut_wpr by won_a_trial:")
print(merged.groupby('won_a_trial')['debut_wpr'].agg(['mean', 'count']))

print("\ndebut_wpr by avg_finish_pct quartile:")
merged['fp_q'] = pd.qcut(merged['avg_finish_pct'], 4, duplicates='drop')
print(merged.groupby('fp_q')['debut_wpr'].agg(['mean', 'count']))

# Compare to horses with ZERO pre-debut trial data (pure blind debut) - is a
# debutant WHO trialled meaningfully different from one who didn't at all?
no_trial_debut = debut_rows.join(n_trials_per_horse.rename('n_pre_trials'), how='left')
no_trial_debut = no_trial_debut[no_trial_debut['n_pre_trials'].isna()].dropna(subset=['debut_wpr'])
print(f"\nDebutants with NO recorded pre-debut trial: {len(no_trial_debut):,}, avg debut wpr: {no_trial_debut['debut_wpr'].mean():.2f}")
print(f"Debutants WITH a pre-debut trial: {len(merged):,}, avg debut wpr: {merged['debut_wpr'].mean():.2f}")
