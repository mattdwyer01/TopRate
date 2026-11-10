"""Extra Proj inputs with ONE builder for training rows and live runners (10 Nov 2026, owner's go-ahead after research/proj_improve5.py).

Four blocks, all as of the day before the race:
  PED   pedigree and young-horse: how the sire's, dam-sire's and dam's OTHER offspring have run against their own figures (and their level), the sire at this distance band
        and on wet tracks, the trainer's record with horses on their 1st to 3rd run.
  DIRF  finishing-position inputs: age, sex, win and place share over the last 8 runs, mean finish position and margin over the last 4, 8-run mean and best rating,
        and those against the field (value minus field mean, rank in field).
  TFU   trainer patterns: overall, first up, at this venue, at this distance band, on wet, with this jockey; the jockey at this venue.
  FRK   collateral form: for each of the horse's last 3 races, how the other runners ran against their own figures in that race, and in their next run since.

They read a table of COMPLETE past fields ("SRC": one row per horse and date with the rating on that race's ATW scale, the formula figure and its miss): the results files
to their last day (plain ratings put on the ATW scale per race, research/conv_history.py) continued by TopRate's stored result pages (data/tr_results: plain and ATW rating
of every runner). SRC rows are never rating inputs of a projection; they only feed these as-of statistics, like the jockey and trainer win rates (projection/rates.py).
build_src() makes the table (about 3 minutes); run.py --build-cache saves it in the projection cache and --fast loads it.
add_all(T, rp, src) adds every column to T (the rows to project, or training rows), rp = the history frame the rows' own runs come from (page frame live)."""
import glob
import gzip
import json
import os
import sys

import numpy as np
import pandas as pd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'research'))
import ctx as C          # noqa: E402
import features as F     # noqa: E402
import rates as RT       # noqa: E402

EXT_MU = 70.0            # centre for the 'level' statistics (rating minus this)
PED = ['sire_eff', 'sire_lvl', 'sire_n', 'sire_dist_eff', 'sire_wet_eff', 'dsire_eff', 'dsire_lvl', 'dam_eff', 'dam_lvl', 'dam_n', 'trn_yng_eff', 'trn_yng_n']
DIRF_BASE = ['age', 'win8', 'plc8', 'm4_finpct', 'm4_mfin', 'm8', 'max8']
DIRF_REL = DIRF_BASE + ['weightCarried', 'barr_f']
DIRF = ['age', 'sex_c', 'win8', 'plc8', 'm4_finpct', 'm4_mfin', 'm8', 'max8'] + [p + c for c in DIRF_REL for p in ('r_', 'k_')]
TFU = ['trn_eff', 'trn_n', 'trn_fu_eff', 'trn_fu_n', 'trn_ven_eff', 'trn_ven_n', 'jk_ven_eff', 'tj_eff', 'tj_n', 'trn_db_eff', 'trn_wet_eff']
FRK = [f'{p}{k}' for k in (1, 2, 3) for p in ('rl', 'rln', 'fk', 'fkd', 'fkn')] + ['rl_w', 'fk_w']
BLOCKS = {'ped': PED, 'dirf': DIRF, 'tfu': TFU, 'frk': FRK}
EXT_FEATS = PED + DIRF + TFU + FRK
SRC_FILE = 'ctx_src.parquet'
_S = {}


def _nm(s):
    """Name key: lowercased, trimmed; None for a blank."""
    s = s.astype(str).str.strip().str.lower()
    return s.where(~s.isin(['', 'nan', 'none']))


def _season(d):
    return d.dt.year - (d.dt.month < 8).astype(int)


_SEX = {'G': 0, 'R': 0, 'M': 1, 'F': 1, 'C': 2, 'H': 2}


# ---------------------------------------------------------------- complete past fields
def tr_results_runs():
    """Every runner of every stored result page (data/tr_results) as a history row in the shape conv_history.build() returns: wpr_plain = TopRate's plain rating,
    c_t = its ATW rating minus the plain one (the shift for that race), wpr = the ATW rating."""
    rows = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'tr_results', '*.json.gz'))):
        d = os.path.basename(f)[:10]
        with gzip.open(f, 'rt') as fh:
            races = json.load(fh).get('races', {})
        for race in races.values():
            rr = race.get('runners') or []
            for ru in rr:
                if ru.get('wpr') is None or ru.get('atw') is None or ru.get('horseId') is None:
                    continue
                rows.append(dict(horse_id=ru['horseId'], horse=ru.get('horse'), date=d, wpr_plain=ru['wpr'], atw=ru['atw'], track=race.get('venue'), venue=race.get('venue'),
                                 distance=race.get('distance'), going=race.get('going'), weightCarried=ru.get('weightCarried'), barrier=ru.get('barrier'), field_size=len(rr),
                                 race_class=race.get('class'), trackGrading=race.get('grading'), jockey=ru.get('jockey'), trainer=ru.get('trainer'),
                                 positionFinish=ru.get('positionFinish'), marginFinish=ru.get('marginFinish'), priceStarting=ru.get('priceStarting'), position800m=ru.get('position800m')))
    t = pd.DataFrame(rows)
    if not len(t):
        return t
    for c in ('horse_id', 'wpr_plain', 'atw', 'priceStarting'):
        t[c] = pd.to_numeric(t[c], errors='coerce')
    t['date'] = pd.to_datetime(t.date)
    t = t.dropna(subset=['horse_id', 'wpr_plain', 'atw'])
    t = t[~F.is_jumps(t.race_class)]
    t['c_t'] = t.atw - t.wpr_plain
    t['wpr'] = t.atw
    t['shift'] = t.c_t
    t['comments_steward'] = None
    t['prize'] = np.nan
    t['isBarrierTrial'] = 0
    t['is_jumpout'] = False
    return t.drop(columns=['atw'])


def complete_history(first_year=2020, last_date=None, frac=1.0):
    """Results files (plain ratings shifted per race) continued by the stored result pages, one row per horse and date, sorted."""
    import conv_history as CH
    last = pd.Timestamp(last_date) if last_date else pd.Timestamp('2100-01-01')
    d = CH.build(first_year, str(last.date()), frac)
    t = tr_results_runs()
    if len(t):
        t = t[t.date <= last]
        if frac < 1.0:
            t = t[t.horse_id.isin(d.horse_id.unique())]
        d = pd.concat([d, t[[c for c in d.columns if c in t.columns]]], ignore_index=True)
        d = d.drop_duplicates(['horse_id', 'date'], keep='first')
    d = d.sort_values(['horse_id', 'date']).reset_index(drop=True)
    d['race_id'] = -(10_000_000 + np.arange(len(d)))
    return d


# ---------------------------------------------------------------- horse facts
def horse_facts():
    """horse_id -> foaling season, sex code, sire, dam and dam-sire name keys. Results files first, then the declared-field files (data/tr_fields) and runners.csv for
    horses the results files do not know (first raced after their last day)."""
    if 'H' in _S:
        return _S['H']
    parts = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'race_results_20[12]*.csv.gz'))):
        if '_rc' in f:
            continue
        parts.append(pd.read_csv(f, usecols=lambda c: c in ('horse_id', 'date', 'horse_age', 'horse_sex', 'sire', 'dam', 'sire_of_dam'), low_memory=False))
    R = pd.concat(parts, ignore_index=True)
    R['src'] = 0
    rows = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'data', 'tr_fields', '*.json'))):
        try:
            for r in json.load(open(f)).get('rows', []):
                rows.append(dict(horse_id=r.get('horse_id'), date=r.get('date'), horse_age=r.get('horse_age'), horse_sex=r.get('horse_sex'), sire=r.get('sire'), sire_of_dam=r.get('sire_of_dam')))
        except Exception:
            continue
    if rows:
        t = pd.DataFrame(rows); t['src'] = 1
        R = pd.concat([R, t], ignore_index=True)
    R['horse_id'] = pd.to_numeric(R.horse_id, errors='coerce')
    R = R.dropna(subset=['horse_id'])
    R['date'] = pd.to_datetime(R.date, errors='coerce')
    R['foal'] = _season(R.date) - pd.to_numeric(R.horse_age, errors='coerce')
    R['sex'] = R.horse_sex.astype(str).str.upper().str[:1].map(_SEX)
    for c in ('sire', 'dam', 'sire_of_dam'):
        R[c] = _nm(R[c]) if c in R.columns else None
    R = R.sort_values(['src', 'date'])
    first = lambda s: s.dropna().iloc[0] if s.notna().any() else np.nan
    g = R.groupby('horse_id')
    H = pd.DataFrame({'foal': g.foal.median(), 'sex': g.sex.agg(first), 'sire': g.sire.agg(first), 'dam': g.dam.agg(first), 'dsire': g.sire_of_dam.agg(first)})
    try:
        u = pd.read_csv(os.path.join(ROOT, 'runners.csv'), usecols=lambda c: c in ('horse_id', 'dam', 'horse_foaled'), low_memory=False)
        u['horse_id'] = pd.to_numeric(u.horse_id, errors='coerce')
        u = u.dropna(subset=['horse_id']).drop_duplicates('horse_id', keep='last').set_index('horse_id')
        if 'dam' in u.columns:
            H['dam'] = H.dam.where(H.dam.notna(), _nm(u.dam).reindex(H.index))
        if 'horse_foaled' in u.columns:
            fd = pd.to_datetime(u.horse_foaled, errors='coerce')
            H['foal'] = H.foal.where(H.foal.notna(), _season(fd).reindex(H.index))
    except Exception as e:
        print('  horse facts: runners.csv not read:', e)
    _S['H'] = H
    return H


# ---------------------------------------------------------------- SRC
SRC_COLS = ['horse_id', 'date', 'wpr', 'wpr_plain', 'resid', 'n', 'd_last', 'dband', 'wet', 'tk', 'jk', 'vn', 'sire', 'dam', 'dsire', 'rk']


def _keys(df):
    """dband, wet, tk, jk (and vn must exist) on a frame that has distance, going_n, trainer, jockey."""
    df['dband'] = pd.cut(pd.to_numeric(df.distance, errors='coerce'), [0, 1200, 1600, 2000, 99999], labels=False).astype(float)
    df['wet'] = (df.going_n >= 5).astype(float)
    df['tk'] = df.trainer.map(RT.nk) if 'trainer' in df.columns else None
    df['jk'] = df.jockey.map(RT.nk)
    return df


def src_from_frame(fr):
    """SRC from a frame built on complete_history() (ctx.page_frame columns plus f and resid)."""
    s = fr[fr.f.notna()].copy()
    s = _keys(s)
    h = horse_facts().reindex(s.horse_id.values)
    s['sire'], s['dam'], s['dsire'] = h.sire.values, h.dam.values, h.dsire.values
    s['rk'] = C._race_key(s)
    if 'wpr_plain' not in s.columns:
        s['wpr_plain'] = s.wpr
    s['vn'] = s.vn.where(s.vn != '')
    return s[SRC_COLS].sort_values(['horse_id', 'date']).reset_index(drop=True)


def build_src(last_date=None, frac=1.0):
    real = F._TR_CACHE.get('rows')
    F._TR_CACHE['rows'] = complete_history(2020, last_date, frac)
    try:
        fr = C.page_frame()
        fr['f'] = C.formula_pred(fr, C.coefs())
        fr['resid'] = fr.wpr - fr.f
    finally:
        if real is not None:
            F._TR_CACHE['rows'] = real
        else:
            F._TR_CACHE.pop('rows', None)
    return src_from_frame(fr)


def _cache_dir():
    return os.path.join(HERE, 'cache_tr' if F.RATINGS_SOURCE == 'toprate' else 'cache')


def save_src(src, path=None):
    path = path or os.path.join(_cache_dir(), SRC_FILE)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    src.to_parquet(path, index=False)
    return path


def load_src(path=None):
    """The cached table (run.py --build-cache), rebuilt when there is none."""
    if 'src' in _S:
        return _S['src']
    path = path or os.path.join(_cache_dir(), SRC_FILE)
    if os.path.exists(path):
        src = pd.read_parquet(path)
    else:
        print('  ctx_ext: no cached complete-field table, building it (about 3 minutes)')
        src = build_src()
        try:
            save_src(src, path)
        except Exception as e:
            print('  ctx_ext: table not saved:', e)
    _S['src'] = src
    return src


# ---------------------------------------------------------------- as-of statistics
class _Asof:
    """Sums and counts of a SRC column by key, strictly before a date. Tables are built once per (keys, value, mask) and reused."""

    def __init__(self, src):
        self.s = src[src.resid.notna()].copy()
        self.s['wdev'] = self.s.wpr - EXT_MU
        self.maps = {}
        self.tabs = {}
        self.masks = {None: None, 'wet': self.s.wet == 1, 'young': self.s.n <= 2, 'fu': self.s.d_last > 60}

    def code(self, col, values):
        if col in ('dband', 'horse_id'):
            return pd.to_numeric(values, errors='coerce').astype(float)
        if col not in self.maps:
            u = self.s[col].dropna().unique()
            self.maps[col] = dict(zip(u, np.arange(len(u), dtype=float)))
        return pd.Series(values).map(self.maps[col]).astype(float).values

    def table(self, keys, val, mask):
        k = (tuple(keys), val, mask)
        if k not in self.tabs:
            s = self.s if self.masks[mask] is None else self.s[self.masks[mask]]
            d = pd.DataFrame({c: self.code(c, s[c].values) for c in keys})
            d['date'] = s.date.values
            d['v'] = s[val].values
            d = d.dropna()
            g = d.groupby(list(keys) + ['date']).v.agg(['sum', 'count']).reset_index().sort_values('date')
            g['S'] = g.groupby(list(keys))['sum'].cumsum()
            g['C'] = g.groupby(list(keys))['count'].cumsum()
            self.tabs[k] = g[list(keys) + ['date', 'S', 'C']]
        return self.tabs[k]

    def get(self, keys, T, val, mask=None):
        g = self.table(keys, val, mask)
        t = pd.DataFrame({c: self.code(c, T[c].values) for c in keys})
        t['date'] = pd.to_datetime(T.date).values
        t['_i'] = np.arange(len(T))
        t = t.dropna().sort_values('date')
        Sv, Cv = np.zeros(len(T)), np.zeros(len(T))
        if len(t) and len(g):
            m = pd.merge_asof(t, g, on='date', by=list(keys), allow_exact_matches=False)
            Sv[m._i.values] = m.S.fillna(0).values
            Cv[m._i.values] = m.C.fillna(0).values
        return Sv, Cv

    def others(self, key, T, val, K, mask=None, extra=()):
        s1, c1 = self.get([key, *extra], T, val, mask)
        s2, c2 = self.get([key, *extra, 'horse_id'], T, val, mask)
        s, c = s1 - s2, c1 - c2
        return s / (c + K), c


def _asof(src):
    if _S.get('asof_id') != id(src):
        _S['asof'] = _Asof(src)
        _S['asof_id'] = id(src)
    return _S['asof']


def add_static(T):
    T = T.copy()
    h = horse_facts().reindex(pd.to_numeric(T.horse_id, errors='coerce').values)
    age = (_season(pd.to_datetime(T.date)).values - h.foal.values).astype(float)
    T['age'] = np.where((age >= 1) & (age <= 15), age, np.nan)
    T['sex_c'] = h.sex.values.astype(float)
    T['sire'], T['dam'], T['dsire'] = h.sire.values, h.dam.values, h.dsire.values
    return _keys(T)


def add_ped(T, A):
    sh = lambda sc, K: (sc[0] / (sc[1] + K), sc[1])
    T['sire_eff'], T['sire_n'] = A.others('sire', T, 'resid', 30)
    T['sire_lvl'], _ = A.others('sire', T, 'wdev', 30)
    T['sire_dist_eff'], _ = A.others('sire', T, 'resid', 30, extra=('dband',))
    T['sire_wet_eff'], _ = A.others('sire', T, 'resid', 30, mask='wet')
    T['dsire_eff'], _ = A.others('dsire', T, 'resid', 30)
    T['dsire_lvl'], _ = A.others('dsire', T, 'wdev', 30)
    T['dam_eff'], T['dam_n'] = A.others('dam', T, 'resid', 5)
    T['dam_lvl'], _ = A.others('dam', T, 'wdev', 5)
    T['trn_yng_eff'], T['trn_yng_n'] = sh(A.get(['tk'], T, 'resid', 'young'), 20)
    for k in ('sire', 'dsire', 'dam'):
        T.loc[T[k].isna(), [c for c in PED if c.startswith(k + '_')]] = np.nan
    return T


def add_tfu(T, A):
    sh = lambda sc, K: (sc[0] / (sc[1] + K), sc[1])
    T['trn_eff'], T['trn_n'] = sh(A.get(['tk'], T, 'resid'), 50)
    T['trn_fu_eff'], T['trn_fu_n'] = sh(A.get(['tk'], T, 'resid', 'fu'), 30)
    T['trn_ven_eff'], T['trn_ven_n'] = sh(A.get(['tk', 'vn'], T, 'resid'), 20)
    T['jk_ven_eff'], _ = sh(A.get(['jk', 'vn'], T, 'resid'), 20)
    T['tj_eff'], T['tj_n'] = sh(A.get(['tk', 'jk'], T, 'resid'), 20)
    T['trn_db_eff'], _ = sh(A.get(['tk', 'dband'], T, 'resid'), 30)
    T['trn_wet_eff'], _ = sh(A.get(['tk'], T, 'resid', 'wet'), 30)
    T.loc[T.tk.isna(), [c for c in TFU if c.startswith('trn') or c.startswith('tj')]] = np.nan
    return T


def _history(rp):
    """Per horse: dates (int days), finish position, field size, margin, in date order."""
    k = ('hist', id(rp), len(rp))
    if _S.get('hist_key') != k:
        o = rp.sort_values(['horse_id', 'date'])
        di = o.date.values.astype('datetime64[D]').astype('int64')
        pos = pd.to_numeric(o.positionFinish, errors='coerce').values
        fs = pd.to_numeric(o.field_size, errors='coerce').values
        mg = pd.to_numeric(o.marginFinish, errors='coerce').values
        hid = o.horse_id.values
        cut = np.r_[0, np.flatnonzero(hid[1:] != hid[:-1]) + 1, len(hid)]
        _S['hist'] = {hid[a]: (di[a:b], pos[a:b], fs[a:b], mg[a:b]) for a, b in zip(cut[:-1], cut[1:])}
        _S['hist_key'] = k
    return _S['hist']


def add_own(T, rp):
    """win8, plc8, m4_finpct, m4_mfin from the horse's runs in rp strictly before the row's date, and the dates of its last three runs (ld1..ld3, int days)."""
    H = _history(rp)
    n = len(T)
    out = np.full((n, 7), np.nan)
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    ti = pd.to_datetime(T.date).values.astype('datetime64[D]').astype('int64')
    with np.errstate(all='ignore'):
        for i in range(n):
            a = H.get(hid[i])
            if a is None:
                continue
            j = int(np.searchsorted(a[0], ti[i], side='left'))
            if j == 0:
                continue
            p8, f8 = a[1][max(0, j - 8):j], a[2][max(0, j - 8):j]
            ok = ~np.isnan(p8)
            if ok.any():
                out[i, 0] = (p8[ok] == 1).mean()
                out[i, 1] = (p8[ok] <= 3).mean()
            p4, f4, m4 = a[1][max(0, j - 4):j], a[2][max(0, j - 4):j], a[3][max(0, j - 4):j]
            ok4 = ~np.isnan(p4) & (f4 > 1)
            if ok4.any():
                out[i, 2] = np.clip((p4[ok4] - 1) / (f4[ok4] - 1), 0, 1).mean()
            if (~np.isnan(m4)).any():
                out[i, 3] = np.nanmean(np.clip(m4, 0, 30))
            for k in (1, 2, 3):
                if j - k >= 0:
                    out[i, 3 + k] = a[0][j - k]
    T['win8'], T['plc8'], T['m4_finpct'], T['m4_mfin'] = out[:, 0], out[:, 1], out[:, 2], out[:, 3]
    T['_ld1'], T['_ld2'], T['_ld3'] = out[:, 4], out[:, 5], out[:, 6]
    R = T[[f'r{k}' for k in range(1, 9)]]
    T['m8'], T['max8'] = R.mean(axis=1), R.max(axis=1)
    return T


def _frank_tables(src):
    if _S.get('frk_id') != id(src):
        R = src[['horse_id', 'date', 'resid', 'rk', 'wpr_plain']].copy()
        R['rc'] = pd.factorize(R.rk)[0]
        R['di'] = R.date.values.astype('datetime64[D]').astype('int64')
        g = R.groupby('horse_id')
        R['dn'] = g.di.shift(-1)
        R['rn'] = g.resid.shift(-1)
        R['dw'] = g.wpr_plain.shift(-1) - R.wpr_plain
        nrc = int(R.rc.max()) + 1
        ok = R.resid.notna().values
        Ssum = np.bincount(R.rc.values[ok], weights=R.resid.values[ok], minlength=nrc)
        Scnt = np.bincount(R.rc.values[ok], minlength=nrc).astype(float)
        V = R[R.dn.notna() & R.rn.notna()].copy()
        V['key'] = V.rc.values.astype('int64') * 1_000_000 + V.dn.values.astype('int64')
        V = V.sort_values('key')
        z = lambda x: np.concatenate([[0.0], np.cumsum(x)])
        tab = dict(keys=V.key.values, cr=z(V.rn.values), cd=z(V.dw.fillna(0).values), cdn=z(V.dw.notna().astype(float).values))
        look = pd.Series(np.arange(len(R)), index=pd.MultiIndex.from_arrays([R.horse_id.values, R.di.values]))
        _S['frk'] = (R, Ssum, Scnt, tab, look)
        _S['frk_id'] = id(src)
    return _S['frk']


def add_frank(T, src):
    R, Ssum, Scnt, tab, look = _frank_tables(src)
    ti = pd.to_datetime(T.date).values.astype('datetime64[D]').astype('int64')
    hid = pd.to_numeric(T.horse_id, errors='coerce').values
    new = {}
    for k in (1, 2, 3):
        ld = T[f'_ld{k}'].values
        idx = pd.MultiIndex.from_arrays([hid, np.where(np.isnan(ld), -1, ld).astype('int64')])
        ri = look.reindex(idx).values
        has = ~np.isnan(ri)
        r = np.where(has, ri, 0).astype(int)
        rc = R.rc.values[r]
        own = R.resid.values[r]
        own_ok = ~np.isnan(own)
        n_oth = Scnt[rc] - own_ok
        rl = (Ssum[rc] - np.where(own_ok, own, 0.0)) / np.where(n_oth > 0, n_oth, np.nan)
        lo = np.searchsorted(tab['keys'], rc.astype('int64') * 1_000_000, side='left')
        hi = np.searchsorted(tab['keys'], rc.astype('int64') * 1_000_000 + ti, side='left')
        sr, sd, nd, nn = tab['cr'][hi] - tab['cr'][lo], tab['cd'][hi] - tab['cd'][lo], tab['cdn'][hi] - tab['cdn'][lo], (hi - lo).astype(float)
        odn, orn, odw = R.dn.values[r], R.rn.values[r], R.dw.values[r]       # the horse's own next run after that race is not a rival's
        mine = (~np.isnan(odn)) & (~np.isnan(orn)) & (odn < ti)
        sr = sr - np.where(mine, orn, 0.0)
        nn = nn - mine
        md = mine & ~np.isnan(odw)
        sd = sd - np.where(md, odw, 0.0)
        nd = nd - md
        nan = lambda x: np.where(has, x, np.nan)
        new[f'rl{k}'], new[f'rln{k}'] = nan(rl), nan(n_oth)
        new[f'fk{k}'], new[f'fkd{k}'], new[f'fkn{k}'] = nan(sr / (nn + 3.0)), nan(sd / (nd + 3.0)), nan(nn)
    w = np.array([0.5, 0.3, 0.2])
    for p in ('rl', 'fk'):
        M = np.column_stack([new[f'{p}{k}'] for k in (1, 2, 3)])
        ok = ~np.isnan(M)
        den = (ok * w).sum(axis=1)
        new[f'{p}_w'] = np.where(den > 0, (np.nan_to_num(M) * w).sum(axis=1) / np.where(den > 0, den, 1), np.nan)
    for c, v in new.items():
        T[c] = v
    return T


def add_all(T, rp, src=None):
    """Every EXT column for the rows of T. T: rows with a formula figure (the population the field-relative columns compare within), with horse_id, date, distance,
    going_n, jockey, trainer, vn, cls, field_size, weightCarried, barr_f and r1..r8. rp: the frame holding the horses' own earlier runs (page frame live, the training
    frame itself in training). src: the complete-field table (load_src() when None)."""
    src = load_src() if src is None else src
    A = _asof(src)
    X = add_static(T)
    X = add_ped(X, A)
    X = add_tfu(X, A)
    X = add_own(X, rp)
    X = add_frank(X, src)
    X = C.add_field_rel(X, DIRF_REL)
    drop = [c for c in ('_ld1', '_ld2', '_ld3', 'sire', 'dam', 'dsire', 'tk', 'jk', 'dband', 'wet') if c in X.columns]
    return X.drop(columns=drop)
