"""Jockey and trainer as-of win rates (27 Oct 2026, option 2 of the Proj improvement list; research/proj_speed_joint.py).
History = results files from 2019 plus the racing.com results file for the days after the last results file; every rate for a run uses only races strictly before its date,
so a past run and an upcoming one get identical features. Names are reduced to first initial + surname (the files print jockeys and trainers in different forms).
add_rates(df) needs columns date, jockey, trainer and adds jw, jw90, tw, tw90 (shrunk win rates, all time and the last 90 days)."""
import glob
import os
import re

import numpy as np
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_H = {}


def nk(x):
    if not isinstance(x, str):
        return None
    t = re.sub(r"[^A-Za-z\s'-]", '', x).split()
    return (t[0][0] + t[-1]).lower().replace("'", '').replace('-', '') if t else None


def history():
    if 'h' in _H:
        return _H['h']
    parts = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]?.csv.gz'))) + [os.path.join(ROOT, 'race_results_2026.csv.gz'), os.path.join(ROOT, 'race_results_2026_rc.csv.gz')]:
        if not os.path.exists(f) or (os.path.basename(f)[13:17].isdigit() and int(os.path.basename(f)[13:17]) < 2019):
            continue
        x = pd.read_csv(f, usecols=lambda c: c in ('date', 'jockey', 'trainer', 'positionFinish', 'isBarrierTrial'), low_memory=False)
        x['_rc'] = f.endswith('_rc.csv.gz')
        parts.append(x)
    h = pd.concat(parts, ignore_index=True)
    h = h[~h.isBarrierTrial.astype(str).isin(['True', '1'])]
    h['date'] = pd.to_datetime(h.date)
    last_main = h.loc[~h._rc, 'date'].max()
    h = h[~h._rc | (h.date > last_main)]
    pos = pd.to_numeric(h.positionFinish, errors='coerce')
    h['winf'] = np.where(pos.notna(), (pos == 1).astype(float), np.nan)
    h['jk'], h['tk'] = h.jockey.map(nk), h.trainer.map(nk)
    h = h[['date', 'jk', 'tk', 'winf']].reset_index(drop=True)
    _H['h'] = h
    return h


def asof_rate(df, key, value, window_days=None, prior=0.1, k=50):
    t = pd.DataFrame({'key': df[key].values, 'date': df.date.values, 'v': df[value].values}).dropna(subset=['key', 'v'])
    a = t.groupby(['key', 'date']).v.agg(['sum', 'count']).reset_index().sort_values(['key', 'date'])
    a['cs'] = a.groupby('key')['sum'].cumsum()
    a['cn'] = a.groupby('key')['count'].cumsum()
    q = pd.DataFrame({'key': df[key].values, 'date': df.date.values, '_i': np.arange(len(df))}).dropna(subset=['key'])
    m = pd.merge_asof(q.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
    cs, cn = m.cs.fillna(0).values, m.cn.fillna(0).values
    if window_days:
        q2 = q.assign(date=q.date - pd.Timedelta(days=window_days))
        m2 = pd.merge_asof(q2.sort_values('date'), a[['key', 'date', 'cs', 'cn']].sort_values('date'), on='date', by='key', allow_exact_matches=False)
        cs, cn = cs - m2.cs.fillna(0).values, cn - m2.cn.fillna(0).values
    out = np.full(len(df), np.nan)
    out[m._i.values] = (cs + prior * k) / (cn + k)
    return out


def add_rates(df):
    """Adds jw, jw90, tw, tw90 (NaN for a missing name)."""
    H = history()
    T = pd.DataFrame({'date': pd.to_datetime(df.date).values, 'jk': df.jockey.map(nk).values if 'jockey' in df.columns else None,
                      'tk': df.trainer.map(nk).values if 'trainer' in df.columns else None, 'winf': np.nan})
    LH = pd.concat([H, T], ignore_index=True)
    n = len(H)
    df = df.copy()
    df['jw'] = asof_rate(LH, 'jk', 'winf')[n:]
    df['jw90'] = asof_rate(LH, 'jk', 'winf', window_days=90, k=30)[n:]
    df['tw'] = asof_rate(LH, 'tk', 'winf')[n:]
    df['tw90'] = asof_rate(LH, 'tk', 'winf', window_days=90, k=30)[n:]
    return df
