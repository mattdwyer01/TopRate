"""Walk-forward logistic regression used to compare feature sets (the repo has no copy of the private racing-model, so this is a stand-in).

Binary winner-vs-not logistic regression, features demeaned within race (a conditional-logit style approximation), trained on all
years before the test year and scored on the test year (2023..2026). Price is NEVER a feature; it is only used to settle bets.
"""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, pandas as pd
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score, log_loss
from sklearn.preprocessing import StandardScaler
from common import *

TEST_YEARS = (2023, 2024, 2025, 2026)

BASE = ['wpr_m1', 'wpr_m3', 'wpr_m5', 'wpr_m8', 'wpr_best', 'n_prior_l', 'days_l', 'w_carried', 'w_up', 'd_up', 'distance_l', 'field_size',
        'barrier_pct', 'sect_i_l600_m5', 'sect_i_400_200_m5', 'sect_i_l200_m5', 'sect_i_time_m5']
CLASS_BUG = ['tg_class_move', 'tg_peak_at_class']
CLASS_RUNG = ['rung_class_move', 'rung_peak_at_class']
CLASS_PAR = ['cp_class_move', 'cp_peak_at_class']
SR_PAR = ['sr_vs_par_m3', 'sr_vs_par_last']
XRTOF = ['XR_m3', 'TOF_m3', 'TOF_last', 'tof_rank_pct']
MAP = ['settle_m3_pos', 'map_rank_pct', 'golden8']


def prep(D):
    D = D.copy()
    D['n_prior_l'] = np.log1p(D['n_prior'])
    D['days_l'] = np.log1p(D['days_since'].clip(lower=0))
    D['distance_l'] = np.log(D['distance'].clip(lower=400))
    D['barrier_pct'] = (D['barrier'] - 1) / (D['field_size'] - 1).clip(lower=1)
    D['map_rank_pct'] = D.groupby('race_id')['settle_m3'].rank(method='min', pct=True)
    D['map_rank'] = D.groupby('race_id')['settle_m3_pos'].rank(method='min')
    D['golden8'] = (D['map_rank'] <= 8).astype(float).where(D['settle_m3_pos'].notna())
    return D


def _design(D, cols, race_mean_cols=None):
    X = D[cols].astype(float).copy()
    miss = X.isna()
    X = X.fillna(X.median())
    # demean continuous features within race so the logit compares runners in the same race
    gm = X.groupby(D['race_id'].values).transform('mean')
    keep_abs = {'field_size', 'distance_l', 'barrier_pct', 'n_prior_l', 'days_l', 'golden8'}
    for c in cols:
        if c not in keep_abs:
            X[c] = X[c] - gm[c]
    ind = miss[[c for c in cols if miss[c].mean() > 0.02]].add_suffix('_na').astype(float)
    return pd.concat([X, ind], axis=1)


def walk_forward(D, cols, years=TEST_YEARS, C=1.0, name='m'):
    """Return a frame of out-of-sample probabilities (raw and race-normalised) for rows in the test years."""
    D = D[D['wpr_m1'].notna() & (D['field_size'] >= 4)].copy()
    out = []
    X = _design(D, cols)
    y = D['win'].values
    yr = D['dt_year'].values
    for ty in years:
        tr = yr < ty; te = yr == ty
        sc = StandardScaler().fit(X[tr])
        lr = LogisticRegression(C=C, max_iter=300).fit(sc.transform(X[tr]), y[tr])
        p = lr.predict_proba(sc.transform(X[te]))[:, 1]
        o = D.loc[te, ['run_id', 'race_id']].copy(); o[f'p_{name}'] = p
        out.append(o)
    o = pd.concat(out)
    o[f'pn_{name}'] = o[f'p_{name}'] / o.groupby('race_id')[f'p_{name}'].transform('sum')
    o[f'rk_{name}'] = o.groupby('race_id')[f'pn_{name}'].rank(ascending=False, method='first')
    return o


def metrics(D, o, name):
    m = D[['run_id', 'race_id', 'win']].merge(o[['run_id', f'p_{name}', f'pn_{name}', f'rk_{name}']], on='run_id')
    auc = roc_auc_score(m['win'], m[f'p_{name}'])
    ll = log_loss(m['win'], m[f'p_{name}'].clip(1e-6, 1 - 1e-6))
    w = m[m['win'] == 1]
    race_ll = -np.log(w[f'pn_{name}'].clip(1e-6)).values
    top = m[m[f'rk_{name}'] == 1]
    return dict(variant=name, runners=len(m), races=len(w), auc=auc, logloss=ll, race_ll=race_ll.mean(), top1=top['win'].mean() * 100), pd.Series(race_ll, index=w['race_id'].values)


def paired(base_ll, ll):
    d = (base_ll - ll).dropna()     # positive = variant better
    return d.mean(), d.std(ddof=1) / np.sqrt(len(d))


# ---------------------------------------------------------------- bet sets and tables shared by the tests
def rule_sets(D):
    """Run ids of the real locked rule (Apr-Oct 2026, archive columns) and of reference rule P (as-of proxy, 2019+).
    Rule P: wpr last-3 rank<=3, as-of Mid/Late/Total sectional proxies each rank<=2, Top>=$3, >=3 prior runs, field of 4+."""
    from rules import load_archive, locked_rule_real, proxy_ranks, proxy_rule
    a = load_archive()
    real = locked_rule_real(a)
    E = D[(D['n_prior'] >= 3) & (D.groupby('race_id')['race_id'].transform('size') >= 4)].copy()
    E = proxy_ranks(E)
    P = proxy_rule(E)
    return set(real['run_id']), set(P['run_id']), a, real


def md(df, floatfmt=None):
    cols = list(df.columns)
    out = ['| ' + ' | '.join(str(c) for c in cols) + ' |', '|' + '---|' * len(cols)]
    for _, r in df.iterrows():
        cells = []
        for c in cols:
            v = r[c]
            if isinstance(v, (float, np.floating)):
                cells.append('n/a' if np.isnan(v) else (floatfmt.get(c, '{:.3f}') if floatfmt else '{:.3f}').format(v))
            else:
                cells.append(str(v))
        out.append('| ' + ' | '.join(cells) + ' |')
    return '\n'.join(out)


def model_table(D, preds, base_name, floatfmt=None):
    """AUC / log-loss / race log-loss / top-pick strike per variant with paired race-log-loss delta vs base."""
    rows, lls = [], {}
    for name, o in preds.items():
        m, ll = metrics(D, o, name)
        rows.append(m); lls[name] = ll
    t = pd.DataFrame(rows)
    d, s = [], []
    for name in t['variant']:
        if name == base_name:
            d.append(np.nan); s.append(np.nan)
        else:
            a, b = paired(lls[base_name], lls[name]); d.append(a); s.append(b)
    t['race_ll_gain_vs_base'] = d; t['gain_se'] = s
    t['gain_t'] = t['race_ll_gain_vs_base'] / t['gain_se']
    return t[['variant', 'runners', 'races', 'auc', 'logloss', 'race_ll', 'race_ll_gain_vs_base', 'gain_se', 'gain_t', 'top1']]


def bet_table(D, preds, real_ids, P_ids, min_top=3.0):
    """ROI of: model #1 at Top>=$3; reference rule P (unmodified and with model rank<=2); locked rule (unmodified and with rank<=2, 2026 window)."""
    rows = []
    for name, o in preds.items():
        k = [c for c in o.columns if c.startswith('rk_')][0]
        m = D[['run_id', 'race_id', 'date', 'win', 'price_top', 'priceStarting']].merge(o[['run_id', k]], on='run_id')
        rows.append(roi_stats(m[(m[k] == 1) & (m['price_top'] >= min_top)], 'price_top', f'{name}: model #1, Top>=$3'))
        rows.append(roi_stats(m[m['run_id'].isin(P_ids)], 'price_top', f'{name}: rule P (population, no gate)'))
        rows.append(roi_stats(m[m['run_id'].isin(P_ids) & (m[k] <= 2)], 'price_top', f'{name}: rule P + model rank<=2'))
        rr = m[m['run_id'].isin(real_ids)]
        rows.append(roi_stats(rr, 'price_top', f'{name}: locked rule (real, 2026)'))
        rows.append(roi_stats(rr[rr[k] <= 2], 'price_top', f'{name}: locked rule + model rank<=2'))
    return rows


def walk_forward_rating(D, cols, years=TEST_YEARS, alpha=10.0):
    """Ridge on the run's own WPR (race-relative) -> a pre-race rating in WPR points; walk-forward like walk_forward()."""
    from sklearn.linear_model import Ridge
    D = D[D['wpr_m1'].notna() & D['wpr'].notna() & (D['field_size'] >= 4)].copy()
    X = _design(D, cols)
    y = (D['wpr'] - D.groupby('race_id')['wpr'].transform('mean')).values
    yr = D['dt_year'].values
    out = []
    for ty in years:
        tr = yr < ty; te = yr == ty
        sc = StandardScaler().fit(X[tr])
        m = Ridge(alpha=alpha).fit(sc.transform(X[tr]), y[tr])
        o = D.loc[te, ['run_id', 'race_id']].copy(); o['rating'] = m.predict(sc.transform(X[te]))
        out.append(o)
    return pd.concat(out)
