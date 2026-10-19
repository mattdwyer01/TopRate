"""Shared loading, as-of feature and ROI helpers for the Horsetorque Edge tests.

Analysis only. Reads the raw results files (TopRate authored sect_* columns included, on purpose: the
production overlay in projection/features.own_overlay blanks them, this module must not use that path).
Nothing here writes to runners.csv, the payload or any production file.
"""
import os
import numpy as np
import pandas as pd

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
CACHE = os.environ.get('HT_CACHE', os.path.join(ROOT, 'analysis', 'horsetorque_edge', '.cache'))
os.makedirs(CACHE, exist_ok=True)

SECT = ['sect_i_time', 'sect_ld_early', 'sect_i_early', 'sect_i_to600', 'sect_i_to800', 'sect_i_l200', 'sect_i_l400',
        'sect_i_l600', 'sect_i_l800', 'sect_i_400_200', 'sect_i_600_400', 'sect_i_800_400', 'sect_i_800_600']
KEEP = ['race_id', 'date', 'horse_id', 'run_id', 'field_size', 'distance', 'going', 'track', 'venue', 'trackGrading', 'wpr',
        'weightCarried', 'barrier', 'priceStarting', 'price_top', 'price_opening', 'positionFinish', 'marginFinish',
        'position800m', 'position600m', 'position400m', 'position200m', 'margin800m', 'margin600m', 'margin400m',
        'winners_time', 'race_class', 'blackType', 'age_restriction', 'weight_restriction', 'isBarrierTrial', 'horse_age',
        'horse_sex', 'race_name', 'jockey', 'trainer', 'is_spell', 'is_letup'] + SECT
JUMPS = {'steeple', 'hurdle', 'novh', 'resth', 'r1hw', 'maih', 'jumpout'}


def load_runs(first_year=2019, last_year=2026, refresh=False):
    """All flat, non-trial runners with a finishing position, one row per runner, sorted by horse and date."""
    path = os.path.join(CACHE, f'runs_{first_year}_{last_year}.pkl')
    if os.path.exists(path) and not refresh:
        return pd.read_pickle(path)
    parts = []
    for y in range(first_year, last_year + 1):
        d = pd.read_csv(os.path.join(ROOT, f'race_results_{y}.csv.gz'), usecols=lambda c: c in KEEP, low_memory=False)
        parts.append(d)
    D = pd.concat(parts, ignore_index=True)
    D = D[D['isBarrierTrial'].astype(str).str.lower().isin(['false', '0', '0.0', 'nan'])]
    D = D[~D['race_class'].astype('string').str.strip().str.lower().isin(JUMPS)]
    D = D[D['positionFinish'].fillna(0) > 0]
    D['dt'] = pd.to_datetime(D['date'])
    D = D.drop_duplicates(['race_id', 'horse_id'])
    # keep races with exactly one winner (drops dead heats, which break win/ROI accounting)
    nw = D.groupby('race_id')['positionFinish'].transform(lambda s: (s == 1).sum())
    D = D[nw == 1]
    D['win'] = (D['positionFinish'] == 1).astype(int)
    D = D.sort_values(['horse_id', 'dt', 'race_id']).reset_index(drop=True)
    D.to_pickle(path)
    return D


def asof_mean(df, col, k, group='horse_id'):
    """Mean of the previous k runs' non-null values of `col` for the same horse (strictly earlier rows)."""
    g = df[group].values
    v = df[col].astype(float).values
    n = len(v)
    ok = ~np.isnan(v)
    cs = np.concatenate([[0.0], np.cumsum(np.where(ok, v, 0.0))])
    cn = np.concatenate([[0], np.cumsum(ok.astype(int))])
    start = np.zeros(n, dtype=int)
    chg = np.r_[True, g[1:] != g[:-1]]
    idx = np.where(chg, np.arange(n), 0)
    start = np.maximum.accumulate(idx)
    hi = np.arange(n)            # exclusive upper bound: rows strictly before i -> [lo, i)
    lo = np.maximum(start, hi - k)
    s = cs[hi] - cs[lo]
    c = cn[hi] - cn[lo]
    with np.errstate(invalid='ignore', divide='ignore'):
        out = np.where(c > 0, s / c, np.nan)
    return out


def asof_last(df, col, group='horse_id'):
    return df.groupby(group)[col].shift(1).values


def asof_max(df, col, group='horse_id'):
    return df.groupby(group)[col].transform(lambda s: s.shift(1).expanding().max()).values


def rank_in_race(df, col, ascending=False, race='race_id'):
    """1 = best. ties share the best place (min)."""
    return df.groupby(race)[col].rank(ascending=ascending, method='min')


def wilson(k, n, z=1.96):
    if n == 0:
        return (np.nan, np.nan)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (c - h, c + h)


def roi_stats(bets, price='price_top', label=None):
    """bets: DataFrame with `win` and a price column. Flat $1 win ROI, strike, CI, ex-top-3 winners, halves."""
    b = bets[(bets[price] > 1) & bets[price].notna()]
    n = len(b)
    if n == 0:
        return dict(label=label, n=0, wins=0, strike=np.nan, avg_price=np.nan, roi=np.nan, roi_se=np.nan, roi_sp=np.nan, roi_ex3=np.nan, half1=np.nan, half2=np.nan)
    ret = np.where(b['win'] == 1, b[price] - 1, -1.0)
    wins = int(b['win'].sum())
    srt = np.sort(np.where(b['win'] == 1, b[price] - 1, -np.inf))[::-1]
    ex3 = np.nan
    if wins > 3:
        top3 = np.argsort(-np.where(b['win'] == 1, b[price].values, -1))[:3]
        keep = np.ones(n, bool); keep[top3] = False
        ex3 = ret[keep].mean() * 100
    d = b['date'].values
    mid = np.sort(d)[n // 2]
    h1 = ret[d < mid].mean() * 100 if (d < mid).sum() else np.nan
    h2 = ret[d >= mid].mean() * 100 if (d >= mid).sum() else np.nan
    sp_col = next((c for c in ('priceStarting', 'starting_price_sp') if c in b.columns), None)
    roi_sp = np.nan
    if sp_col is not None:
        s = b[b[sp_col] > 1]
        if len(s):
            roi_sp = np.where(s['win'] == 1, s[sp_col] - 1, -1.0).mean() * 100
    return dict(label=label, n=n, wins=wins, strike=wins / n * 100, avg_price=float(b[price].mean()),
                roi=ret.mean() * 100, roi_se=ret.std(ddof=1) / np.sqrt(n) * 100 if n > 1 else np.nan, roi_sp=roi_sp, roi_ex3=ex3, half1=h1, half2=h2)


def fmt_table(rows, cols=('label', 'n', 'wins', 'strike', 'avg_price', 'roi', 'roi_se', 'roi_sp', 'roi_ex3', 'half1', 'half2')):
    hdr = ['Variant', 'Bets', 'Wins', 'Strike %', 'Avg price', 'ROI at Top %', 'ROI s.e.', 'ROI at SP %', 'ROI ex top-3 winners %', 'ROI 1st half %', 'ROI 2nd half %']
    out = ['| ' + ' | '.join(hdr) + ' |', '|' + '---|' * len(hdr)]
    for r in rows:
        cells = [str(r['label']), f"{r['n']:,}", f"{r['wins']:,}"]
        for k in cols[3:]:
            v = r[k]
            cells.append('n/a' if v is None or (isinstance(v, float) and np.isnan(v)) else (f'{v:.2f}' if k == 'avg_price' else f'{v:.1f}' if k in ('roi_se', 'strike') else f'{v:+.1f}' if 'roi' in k or 'half' in k else f'{v:.1f}'))
        out.append('| ' + ' | '.join(cells) + ' |')
    return '\n'.join(out)
