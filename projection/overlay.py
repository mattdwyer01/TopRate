"""Puts the new model's projections into the dashboard's runner table.

The payload builder (toprate_daily.py) reads wprp_proj / wprp_base / wprp_adj / wprp_conf / wprp_price / wprp_rank / wprp_peak /
wprp_desc / wprp_contrib / wprp_proj_alt / wprp_conf_alt from the runner rows. apply() fills those from wpr_projection_log.csv.gz
(the new model) and clears them everywhere else, so no projection from the previous model can reach the dashboard, the trackers or the
accuracy stats. Fair prices use the same softmax-over-WPR convention as before (beta from wpr_models/config.json).
"""
import json
import os

import numpy as np
import pandas as pd

from . import projlog as plog

ROOT = plog.ROOT
OLD_COLS = ['wprp_proj', 'wprp_conf', 'wprp_price', 'wprp_rank', 'wprp_peak', 'wprp_desc', 'wprp_proj_alt', 'wprp_conf_alt', 'wprp_base', 'wprp_adj', 'wprp_contrib']
NEW_COLS = ['wprp_sd', 'wprp_model', 'wprp_made', 'wprp_atwo']   # wprp_made: when the logged projection was made (tab_results_poller refreshes the payload when the log is newer)


def _beta():
    try:
        return float(json.load(open(os.path.join(ROOT, 'wpr_models', 'config.json'))).get('beta', 0.4))
    except Exception:
        return 0.4


def _describe(r):
    if r.model == 'light':
        w = f" Weight carried {r.wtadj:+.1f}." if abs(r.wtadj) >= 0.05 else ''
        return f"New model, light-history ({int(r.nruns)} prior run{'s' if int(r.nruns) != 1 else ''}): projected {r.proj:.1f} WPR.{w} Typical error about {r.sd:.1f}."
    adj = '' if pd.isna(r.adj) else f" Suitability adjustment {r.adj:+.1f}."
    if abs(r.wtadj) >= 0.05:
        adj += f" Weight carried {r.wtadj:+.1f}."
    return f"New model ({int(r.nruns)} prior runs): base {r.base:.1f} WPR.{adj} Typical error about {r.sd:.1f}."


def apply(runners_df, path=None):
    """Returns runners_df with the projection columns replaced by the new model's. Rows without a projection are cleared."""
    df = runners_df
    lg = plog.load(path or plog.PATH)
    for c in OLD_COLS + NEW_COLS:
        if c not in df.columns:
            df[c] = None
    # Every column from the previous model is cleared (its speed_map term was retired on 8 Oct 2026; the Speed Map / SM Adj now read suitability).
    df[OLD_COLS + NEW_COLS] = None
    if lg.empty or 'run_id' not in df.columns:
        return df
    lg = lg.drop_duplicates('run_id', keep='last').set_index('run_id')
    rid = pd.to_numeric(df['run_id'], errors='coerce')
    hit = rid.isin(lg.index)
    if not hit.any():
        return df
    m = lg.loc[rid[hit].astype('int64')]
    idx = df.index[hit]
    df.loc[idx, 'wprp_proj'] = m.proj.values
    df.loc[idx, 'wprp_base'] = m.base.values
    df.loc[idx, 'wprp_adj'] = (m.proj - m.base).round(2).values   # suitability + weight carried, so Base + Adj = Proj
    df.loc[idx, 'wprp_sd'] = m.sd.values
    df.loc[idx, 'wprp_model'] = m.model.values
    df.loc[idx, 'wprp_made'] = m.made.astype(str).values
    df.loc[idx, 'wprp_atwo'] = pd.to_numeric(m.atwo, errors='coerce').values
    # confidence on the old 0-100 scale, from the error estimate: sd 8 -> 90, sd 12 -> 70 (display only)
    df.loc[idx, 'wprp_conf'] = np.clip(np.round(130 - 5 * m.sd.values), 40, 95)
    df.loc[idx, 'wprp_desc'] = [_describe(r) for r in m.itertuples()]
    def _grp(g):
        try:
            return {'g_' + k: float(v) for k, v in json.loads(g).items()} if isinstance(g, str) and g else {}
        except Exception:
            return {}
    def _contrib(a, w, mod, g, sa):
        # sm_light: the suitability model's value for a light-history runner (history inputs blank). Display only (SM column, speed map), not part of Base + Adj = Proj.
        d = {**({'suitability': float(a)} if mod == 'main' and pd.notna(a) else {}), **({'sm_light': float(sa)} if mod == 'light' and pd.notna(sa) else {}),
             **({'weight': float(w)} if pd.notna(w) and abs(w) >= 0.005 else {}), **(_grp(g) if mod == 'main' else {})}
        return json.dumps(d) if d else None
    df.loc[idx, 'wprp_contrib'] = [_contrib(a, w, mod, g, sa) for a, w, mod, g, sa in zip(m.adj.values, m.wtadj.values, m.model.values, m.grp.values, m.sadj.values)]
    # fair price and rank within the race (same softmax convention as before; scratched runners excluded)
    beta = _beta()
    sub = df.loc[idx, ['race_id', 'wprp_proj']].copy()
    if 'scratched' in df.columns:
        sub = sub[df.loc[idx, 'scratched'].fillna(0).astype(float) != 1]
    sub['wprp_proj'] = pd.to_numeric(sub.wprp_proj, errors='coerce')
    for rid_, g in sub.dropna(subset=['wprp_proj']).groupby('race_id'):
        if len(g) < 2:
            continue
        e = np.exp(beta * (g.wprp_proj - g.wprp_proj.max()))
        df.loc[g.index, 'wprp_price'] = np.round(1 / (e / e.sum()), 2)
        df.loc[g.index, 'wprp_rank'] = g.wprp_proj.rank(ascending=False, method='min').astype(int)
    return df
