"""direct_score.py -- score the direct finishing-position model on the daily complete-field log (data/direct_log).

The direct model (direct_model/V3a.txt, 189 inputs, softmax loss) turns each runner's form, class, jockey and trainer into a win chance, normalised inside the race.
Inputs are built exactly as research/direct_finish_v3.py builds them for its T2 test (real runner-page ratings, no conversion): the horse's last runs from the log row,
jockey and trainer win rates from the results files, and the Proj's context / relevance / speed block from the runner-page store (projection/ctx.py).

  python direct_score.py score --from 2026-10-27 --days 3      writes data/direct_scores/<date>.json (race_id -> {tab: chance})
  python direct_score.py classes                              rewrites direct_model/classes.json (class codes seen 200+ times before 2024-07, the model's `cls` input)

Best effort in the daily job: a failure never stops the run. The output holds win chances over every runner in the log for the race; the dashboard renormalises over
the runners still in. First starters and runners with no rated form get a score too (their form inputs are blank, as in training)."""
import argparse, datetime as dt, glob, gzip, json, os, re, sys
from pathlib import Path
import numpy as np, pandas as pd

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'projection'))
import ctx as C            # noqa: E402
import features as FT      # noqa: E402,F401

MODEL_DIR = ROOT / 'direct_model'
LOG_DIR = ROOT / 'data' / 'direct_log'
OUT_DIR = ROOT / 'data' / 'direct_scores'
SEX = {'G': 0, 'M': 1, 'F': 2, 'C': 3, 'H': 4, 'R': 5}


def nk(x):
    if not isinstance(x, str):
        return None
    t = re.sub(r"[^A-Za-z\s'-]", '', x).split()
    return (t[0][0] + t[-1]).lower().replace("'", '').replace('-', '') if t else None


def asof_rate(df, key, value, window_days=None, prior=0.1, k=50):
    v = df[value]
    t = pd.DataFrame({'key': df[key].values, 'date': df.date.values, 'v': v.values}).dropna(subset=['key', 'v'])
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


def _results(cols):
    fs = sorted(glob.glob(str(ROOT / 'race_results_20*.csv.gz')))
    return pd.concat([pd.read_csv(f, usecols=lambda c: c in cols, low_memory=False) for f in fs if not f.endswith('_rc.csv.gz')], ignore_index=True)


def make_classes():
    """Class codes with 200+ runs before 2024-07 (the model's `cls` input is the index into this list)."""
    r = _results(['race_id', 'horse_id', 'date', 'race_class', 'isBarrierTrial', 'is_jumpout'])
    r = r[~r.isBarrierTrial.astype(bool) & ~r.is_jumpout.fillna(False).astype(bool)]
    r['date'] = pd.to_datetime(r.date)
    r = r[(r.date >= '2019-06-01') & (r.date <= '2025-12-31')].drop_duplicates(['race_id', 'horse_id'])
    vc = C.class_code(r.loc[r.date < '2024-07-01', 'race_class']).value_counts()
    cls = vc[vc >= 200].index.tolist()
    (MODEL_DIR / 'classes.json').write_text(json.dumps(cls))
    return cls


def load_log(dates):
    rows = []
    for d in dates:
        f = LOG_DIR / f'{d}.json.gz'
        if not f.exists():
            continue
        R = json.load(gzip.open(f, 'rt'))['rows']
        for x in (R.values() if isinstance(R, dict) else R):
            rows.append(dict(x))
    return pd.DataFrame(rows)


def build_features(L, meta):
    """L: log rows (any dates, all runners of each race). Returns L with the model's inputs."""
    import runners_io
    L = L.copy()
    L['race_id'] = pd.to_numeric(L.race_id, errors='coerce')
    L['horse_id'] = pd.to_numeric(L.horse_id, errors='coerce')
    rr = runners_io.read_runners()
    rr['race_id'] = pd.to_numeric(rr.race_id, errors='coerce')
    rr['horse_id'] = pd.to_numeric(rr.horse_id, errors='coerce')
    ag = rr.drop_duplicates(['race_id', 'horse_id']).set_index(['race_id', 'horse_id'])[['horse_age', 'horse_sex']]
    L = L.join(ag, on=['race_id', 'horse_id'])
    L['date'] = pd.to_datetime(L.date)
    L['nr'] = L.groupby('race_id').horse_id.transform('size').astype(float)
    L['jk'], L['tk'] = L.jockey.map(nk), L.trainer.map(nk)
    Lr = L.reset_index(drop=True)
    # jockey / trainer win rates: results files to 2025-12, the 2026 file, then the racing.com file after it
    # same history the research test used: results 2019-06 to 2025-12 (no trials or jump-outs), the 2026 results file, then the racing.com file after it
    cols = ['race_id', 'horse_id', 'date', 'jockey', 'trainer', 'positionFinish', 'isBarrierTrial', 'is_jumpout']
    old = _results(cols)
    old = old[~old.isBarrierTrial.astype(bool) & ~old.is_jumpout.fillna(False).astype(bool)]
    old['date'] = pd.to_datetime(old.date)
    old = old[(old.date >= '2019-06-01') & (old.date <= '2025-12-31')].drop_duplicates(['race_id', 'horse_id'])
    r26 = pd.read_csv(ROOT / 'race_results_2026.csv.gz', usecols=lambda c: c in cols, low_memory=False)
    rc = pd.read_csv(ROOT / 'race_results_2026_rc.csv.gz', usecols=lambda c: c in cols, low_memory=False)
    r26 = r26[~r26.isBarrierTrial.astype(str).isin(['True', '1'])]
    rc = rc[~rc.isBarrierTrial.astype(str).isin(['True', '1'])]
    for t in (old, r26, rc):
        t['date'] = pd.to_datetime(t.date)
        t['pos'] = pd.to_numeric(t.positionFinish, errors='coerce')
        t['jk'], t['tk'] = t.jockey.map(nk), t.trainer.map(nk)
        t['winf'] = np.where(t.pos.notna(), (t.pos == 1).astype(float), np.nan)
    H = pd.concat([old[['date', 'jk', 'tk', 'winf']], r26[['date', 'jk', 'tk', 'winf']], rc[rc.date > r26.date.max()][['date', 'jk', 'tk', 'winf']]], ignore_index=True)
    LH = pd.concat([H, Lr[['date', 'jk', 'tk']].assign(winf=np.nan)], ignore_index=True)
    nH = len(H)
    jw = asof_rate(LH, 'jk', 'winf')[nH:]
    jw90 = asof_rate(LH, 'jk', 'winf', window_days=90, k=30)[nH:]
    tw = asof_rate(LH, 'tk', 'winf')[nH:]
    tw90 = asof_rate(LH, 'tk', 'winf', window_days=90, k=30)[nH:]
    feat_rows = []
    for i, x in enumerate(Lr.itertuples()):
        h = list(x.hist or [])[::-1]
        rt = [a.get('wpr') if a.get('wpr') is not None else np.nan for a in h] + [np.nan] * 12
        mf = [min(max(a.get('marginFinish'), 0), 30) if a.get('marginFinish') is not None else np.nan for a in h] + [np.nan] * 4
        fp = [((a['positionFinish'] - 1) / (a['starters'] - 1)) if a.get('positionFinish') and a.get('starters') and a['starters'] > 1 else np.nan for a in h] + [np.nan] * 4
        ps = [a.get('positionFinish') if a.get('positionFinish') is not None else np.nan for a in h][:8]
        last = h[0] if h else None
        arr8 = np.array(rt[:8], dtype=float)
        m8 = np.nanmean(arr8) if np.isfinite(arr8).any() else np.nan
        pk = np.array(ps, dtype=float)
        npk = np.isfinite(pk).sum()
        feat_rows.append(dict(
            w1=rt[0], w2=rt[1], w3=rt[2], w4=rt[3], w5=rt[4], w6=rt[5], m3_wpr=np.nanmean(rt[:3]) if np.isfinite(rt[:3]).any() else np.nan, m8_wpr=m8,
            max8_wpr=np.nanmax(arr8) if np.isfinite(arr8).any() else np.nan, s8_wpr=np.nanstd(arr8, ddof=1) if np.isfinite(arr8).sum() > 1 else np.nan,
            trend=(rt[0] - m8) if np.isfinite(rt[0]) else np.nan, p1_mfin=mf[0], m4_mfin=np.nanmean(mf[:4]) if np.isfinite(mf[:4]).any() else np.nan, p1_finpct=fp[0],
            m4_finpct=np.nanmean(fp[:4]) if np.isfinite(fp[:4]).any() else np.nan,
            win8=float((pk == 1).sum() / npk) if npk else np.nan, plc8=float((pk <= 3).sum() / npk) if npk else np.nan,
            days=(x.date - pd.Timestamp(last['date'])).days if last else np.nan,
            wchg=(x.weight - last['weightCarried']) if last and last.get('weightCarried') is not None and x.weight is not None else np.nan,
            dchg=(x.distance - last['distance']) if last and last.get('distance') is not None else np.nan, n_runs=float(min(len(h), 12)),
            cls_same=float(C.class_code(pd.Series([last.get('class')])).iloc[0] == C.class_code(pd.Series([x.race_class])).iloc[0]) if last and last.get('class') else np.nan,
            jock_chg=float(nk(last.get('jockey')) != x.jk) if last and last.get('jockey') and x.jk else np.nan,
            jw=jw[i], jw90=jw90[i], tw=tw[i], tw90=tw90[i]))
    Lf = pd.concat([Lr, pd.DataFrame(feat_rows)], axis=1)
    Lf['weightCarried'] = pd.to_numeric(Lf.weight, errors='coerce')
    Lf['distance'] = pd.to_numeric(Lf.distance, errors='coerce')
    Lf['gs'] = pd.to_numeric(Lf.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    Lf['horse_age'] = pd.to_numeric(Lf.horse_age, errors='coerce')
    Lf['sex'] = Lf.horse_sex.astype(str).str.upper().str[:1].map(SEX)
    Lf['clsc'] = C.class_code(Lf.race_class)
    Lf['barfrac'] = (Lf.barrier - 1) / (Lf.nr - 1)
    Lf['rk'] = Lf.race_id
    # Proj's context / relevance / speed block from the live store, exactly as the live Proj builds it
    co = C.coefs()
    rp = C.page_frame()
    rp['f'] = C.formula_pred(rp, co)
    rp = C.context_columns(rp)
    rp['resid'] = rp.wpr - rp.f
    rp = C.add_speed(rp)
    tab = C.jockey_table(rp)
    X = pd.DataFrame({'horse_id': Lf.horse_id, 'date': Lf.date, 'jockey': Lf.jockey.fillna('').astype(str), 'venue': Lf.venue, 'distance': Lf.distance, 'going': Lf.going,
                      'weightCarried': Lf.weightCarried, 'barrier': Lf.barrier, 'field_size': Lf.nr, 'race_class': Lf.race_class, 'trackGrading': Lf.grading, 'prize': Lf.prize})
    X['going_n'] = C.going_num(X.going)
    X['grade'] = pd.to_numeric(X.trackGrading, errors='coerce')
    X['cls'] = C.class_code(X.race_class)
    X['vn'] = C.venue_key(X.venue.astype(str))
    X['venue'] = X.vn
    X['lprize'] = np.log1p(pd.to_numeric(X['prize'], errors='coerce'))
    h = C.target_history(X, rp)
    X = pd.concat([X.drop(columns=[c for c in h.columns if c in X.columns]), h], axis=1)
    X['f'] = C.formula_pred(X, co)
    X = C.context_columns(X)
    X = C.add_jockey(X, tab, targets=True)
    X = C.add_venue(X, rp)
    X = C.add_field(X)
    Xr = pd.concat([X, C.rel_features(X, rp)], axis=1)
    Xr = pd.concat([Xr, C.speed_features(Xr, rp)], axis=1)
    feats = meta['feats']
    for c in [c for c in feats if c.startswith('x_')]:
        Lf[c] = Xr[c[2:]].values if c[2:] in Xr.columns else np.nan
    # field-relative inputs (same definitions as research/direct_finish_v3.py add_features, V3a part)
    classes = json.loads((MODEL_DIR / 'classes.json').read_text())
    Lf['cls'] = pd.Categorical(Lf.clsc, categories=classes).codes.astype(float)
    Lf.loc[Lf.cls < 0, 'cls'] = np.nan
    gk = Lf.groupby('rk')
    REL2 = ['w1', 'm3_wpr', 'm8_wpr', 'max8_wpr', 'm4_mfin', 'm4_finpct', 'days', 'weightCarried', 'barfrac', 'horse_age', 'jw', 'jw90', 'tw', 'tw90', 'win8', 'plc8']
    XREL = [c for c in ['x_f', 'x_sim_all', 'x_sim_dist', 'x_sim_going', 'x_sim_track', 'x_c_max', 'x_c_ewm3', 'x_h_dist', 'x_h_going', 'x_h_track', 'x_jock_eff', 'x_sp_ewm4', 'x_sd_mean4', 'x_spd_vs_f'] if c in Lf.columns]
    rel = {}
    for c in REL2 + XREL:
        rel['r_' + c] = Lf[c] - gk[c].transform('mean')
        rel['k_' + c] = gk[c].rank(pct=True)
    rel['gap_top_m3'] = Lf.m3_wpr - gk.m3_wpr.transform('max')
    rel['gap_top_m8'] = Lf.m8_wpr - gk.m8_wpr.transform('max')
    return pd.concat([Lf, pd.DataFrame(rel, index=Lf.index)], axis=1)


def score(Lf, meta):
    import lightgbm as lgb
    m = lgb.Booster(model_file=str(MODEL_DIR / 'V3a.txt'))
    s = pd.Series(m.predict(Lf[meta['feats']]) * meta['T'], index=Lf.index)
    e = np.exp(s - s.groupby(Lf.race_id).transform('max'))
    return e / e.groupby(Lf.race_id).transform('sum')


def run(dates):
    meta = json.loads((MODEL_DIR / 'meta.json').read_text())['V3a']
    L = load_log(dates)
    if L.empty:
        print('no log rows for', dates)
        return {}
    Lf = build_features(L, meta)
    Lf['dm'] = score(Lf, meta)
    out = {}
    for d, g in Lf.groupby(Lf.date.dt.strftime('%Y-%m-%d')):
        races = {}
        skipped = 0
        for rid, gr in g.groupby('race_id'):
            tabs = pd.to_numeric(gr.tab, errors='coerce')
            # a field that is not declared yet (tab or barrier 0 / blank, repeated tabs) has no real scores; it is scored once the card is declared
            if tabs.isna().any() or (tabs <= 0).any() or tabs.duplicated().any() or (pd.to_numeric(gr.barrier, errors='coerce').fillna(0) <= 0).any():
                skipped += 1
                continue
            races[str(int(rid))] = {str(int(t)): round(float(p), 4) for t, p in zip(tabs, gr.dm)}
        out[d] = races
        OUT_DIR.mkdir(parents=True, exist_ok=True)
        (OUT_DIR / f'{d}.json').write_text(json.dumps({'generated': dt.datetime.now(dt.timezone.utc).isoformat(timespec='seconds'), 'races': races}, separators=(',', ':')))
        print(f'{d}: {len(races)} races, {sum(len(v) for v in races.values())} runners scored, {skipped} races not declared yet')
    return Lf


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['score', 'classes'])
    ap.add_argument('--from', dest='start', default=None)
    ap.add_argument('--days', type=int, default=3)
    a = ap.parse_args()
    if a.cmd == 'classes':
        print(make_classes())
    else:
        start = dt.date.fromisoformat(a.start) if a.start else dt.date.today()
        run([(start + dt.timedelta(days=i)).isoformat() for i in range(a.days)])
