"""Converted history for training a Proj (26 Oct 2026): the results files' plain ratings put on the ATW scale the runner pages use, so they look like page-store runs.
A runner page rates every past run of a horse at one offset (wfa_scale.atw_offset of the race the page is struck for), so a converted horse gets ONE shift for all its runs:
the offset of its final run in the window (date, distance, age, sex, weight carried). Returns a frame with the columns features.runner_page_runs() produces.
Use: conv = conv_history.build(first_year=2020, last_date='2025-12-31', horse_frac=1.0)"""
import glob
import os
import numpy as np, pandas as pd
import wfa_scale as W

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
COLS = ['horse_id', 'horse', 'date', 'wpr', 'track', 'venue', 'distance', 'going', 'weightCarried', 'barrier', 'field_size', 'race_class', 'trackGrading', 'jockey',
        'positionFinish', 'marginFinish', 'priceStarting', 'position800m', 'comments_steward', 'horse_age', 'horse_sex', 'horse_foaled', 'isBarrierTrial', 'is_jumpout']


def load(first_year=2020):
    out = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]*.csv.gz'))):
        y = int(os.path.basename(f)[13:17]) if os.path.basename(f)[13:17].isdigit() else 0
        if '_rc' in f or y < first_year:
            continue
        out.append(pd.read_csv(f, usecols=lambda c: c in COLS, low_memory=False))
    return pd.concat(out, ignore_index=True)


def build(first_year=2020, last_date='2025-12-31', horse_frac=1.0, seed=0, per_row=True):
    d = load(first_year)
    d = d[(d.isBarrierTrial.astype(str) != 'True') & (d.is_jumpout.astype(str) != 'True')]
    d = d[~d.race_class.astype(str).str.contains('Hurdle|Steeple', case=False)]
    d['horse_id'] = pd.to_numeric(d.horse_id, errors='coerce'); d['wpr'] = pd.to_numeric(d.wpr, errors='coerce')
    d = d.dropna(subset=['horse_id', 'wpr', 'date'])
    d['date'] = pd.to_datetime(d.date)
    d = d[d.date <= pd.Timestamp(last_date)].drop_duplicates(['horse_id', 'date'], keep='last')
    if horse_frac < 1.0:
        ids = d.horse_id.drop_duplicates().sample(frac=horse_frac, random_state=seed)
        d = d[d.horse_id.isin(ids)]
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    def off(r):
        age = W.racing_age(r.horse_foaled, r.date) if isinstance(r.horse_foaled, str) and len(r.horse_foaled) >= 10 else (None if pd.isna(r.horse_age) else int(r.horse_age))
        v = W.atw_offset(age, str(r.horse_sex).upper()[:1], r.date.date(), float(r.distance), r.weightCarried) if pd.notna(r.distance) and pd.notna(r.weightCarried) else None
        return np.nan if v is None else v
    n0 = len(d)
    if per_row:
        # every run gets its OWN shift c_t (AR 168 standard weight for that race minus the weight carried, x 0.8): a runner page is struck for the race it is fetched for, so the
        # history and the target of a training row are both put on that race's scale. Runs with no weight or distance keep c_t NaN: they stay in the history (plain) but are not targets.
        d['c_t'] = [off(r) for r in d.itertuples()]
        d['wpr_plain'] = d.wpr
        d['wpr'] = d.wpr + d.c_t
        d['shift'] = d.c_t
        print(f'per-row converted history: {len(d)} runs, c_t known on {d.c_t.notna().mean():.3f}, mean {d.c_t.mean():+.2f} sd {d.c_t.std():.2f}')
        d['prize'] = np.nan
        d['race_id'] = -(10_000_000 + np.arange(len(d)))
        d['isBarrierTrial'] = 0; d['is_jumpout'] = False
        return d.drop(columns=['horse_age', 'horse_sex', 'horse_foaled'])
    last = d.groupby('horse_id').tail(1).copy()
    last['c'] = [off(r) for r in last.itertuples()]
    c = last.set_index('horse_id').c
    d['shift'] = d.horse_id.map(c)
    n0 = len(d)
    d = d.dropna(subset=['shift']).reset_index(drop=True)
    d['wpr_plain'] = d.wpr
    d['wpr'] = d.wpr + d['shift']
    d['prize'] = np.nan
    d['race_id'] = -(10_000_000 + np.arange(len(d)))
    d['isBarrierTrial'] = 0; d['is_jumpout'] = False
    print(f'converted history: {len(d)} runs of {d.horse_id.nunique()} horses ({n0 - len(d)} dropped for no shift), shift mean {d["shift"].mean():+.2f} sd {d["shift"].std():.2f}')
    return d.drop(columns=['horse_age', 'horse_sex', 'horse_foaled'])
