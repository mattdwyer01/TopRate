"""Durable log of the new model's pre-race projections (wpr_projection_log.csv.gz at the repo root).

One row per run_id: the latest projection made before the race. The dashboard payload, the trackers and the Review tab read this
log (via overlay.py), so past races keep the projection that was made before they ran and are never re-scored in-sample.

Columns: run_id, race_id, date, proj, base, adj (suitability), wtadj (weight carried), sd, model, nruns, grp (JSON: recent-form anchor and per-group corrections of the main-model base), src ('live' = made by run.py before the race,
'oof' = out-of-sample back-fill from the research evaluation, used to seed the log), made (UTC timestamp), atwo (the horse's ATW offset when the projection was made, frozen so a resulted race keeps the weight it ran at; blank for older rows).
"""
import os

import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
PATH = os.path.join(ROOT, 'wpr_projection_log.csv.gz')
COLS = ['run_id', 'race_id', 'date', 'proj', 'base', 'adj', 'wtadj', 'sd', 'model', 'nruns', 'grp', 'src', 'made', 'atwo']


def load(path=PATH):
    if not os.path.exists(path):
        return pd.DataFrame(columns=COLS)
    d = pd.read_csv(path, dtype={'run_id': 'int64', 'race_id': 'int64'})
    d['date'] = pd.to_datetime(d['date'])
    if 'wtadj' not in d.columns:
        d['wtadj'] = 0.0
    if 'grp' not in d.columns:
        d['grp'] = None
    if 'atwo' not in d.columns:
        d['atwo'] = np.nan
    return d


def update(rows, path=PATH, keep_days=120):
    """rows: DataFrame with COLS. Replaces any existing row for the same run_id (a later projection supersedes an earlier one, but
    a race that has already run is never overwritten: callers only pass runners of races that have not run)."""
    old = load(path)
    rows = rows.copy()
    if 'atwo' not in rows.columns:
        rows['atwo'] = np.nan
    new = pd.concat([old[~old.run_id.isin(rows.run_id)], rows[COLS]], ignore_index=True)
    cut = new.date.max() - pd.Timedelta(days=keep_days)
    new = new[new.date >= cut].sort_values(['date', 'race_id', 'run_id'])
    new.to_csv(path, index=False, compression='gzip', float_format='%.2f')
    return new
