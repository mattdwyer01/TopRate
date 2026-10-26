"""Score the race-call running order (from sky_audio_call.py transcripts) against racing.com GPS and the official finish.
usage: PYTHONPATH=. python research/sky_audio_eval.py CALLS_DIR OUT_JSON
"""
import difflib, glob, json, os, re, sys
import numpy as np
import pandas as pd
from scipy.stats import kendalltau

MAP = {'FLER': ('Flemington', '2026-10-24'), 'MOPR': ('Morphettville', '2026-10-24'), 'CAUR': ('Caulfield', '2026-10-17')}
rng = np.random.default_rng(0)


def norm(s):
    return re.sub(r'[^a-z0-9 ]', '', s.lower().replace("'", ''))


def mentions(words, field, thr=0.8):
    """[(time, tab)] for every place a runner's name is heard (fuzzy over word windows of the name's length +-1)."""
    ws = [(w[0], norm(w[2])) for w in words if norm(w[2])]
    out = []
    for tab, name in field:
        nm = norm(name)
        k = len(nm.split())
        best = []
        for n in {max(1, k - 1), k, k + 1}:
            for i in range(len(ws) - n + 1):
                cand = ' '.join(w[1] for w in ws[i:i + n])
                r = difflib.SequenceMatcher(None, cand.replace(' ', ''), nm.replace(' ', '')).ratio()
                if r >= thr:
                    best.append((ws[i][0], tab, r, i, n))
        # keep the best non-overlapping hits
        best.sort(key=lambda x: -x[2])
        used = set()
        for t, tb, r, i, n in best:
            span = set(range(i, i + n))
            if span & used:
                continue
            used |= span
            out.append((t, tb))
    return sorted(out)


def clusters(ms, gap=3.0, min_h=4):
    cs, cur = [], []
    for t, tab in ms:
        if cur and t - cur[-1][0] > gap:
            cs.append(cur)
            cur = []
        cur.append((t, tab))
    if cur:
        cs.append(cur)
    res = []
    for c in cs:
        order = []
        for t, tab in c:
            if tab not in order:
                order.append(tab)
        if len(order) >= min_h:
            res.append((c[0][0], order))
    return res


def truth(venue, date, race):
    y = date[:4]
    r = pd.read_parquet(f'data/gps/rc_gps_runs_{y}.parquet')
    s = pd.read_parquet(f'data/gps/rc_gps_sections_{y}.parquet')
    r = r[(r.venue == venue) & (r.start_utc.str[:10] == date) & (r.race_no == race)]
    m = r.meet_code.iloc[0]
    s = s[(s.meet_code == m) & (s.race_no == race)]
    pos = s.pivot_table(index='tab_no', columns='from_m', values='pos')
    fin = r.set_index('tab_no').finish
    return pos, fin


def best_tau(order, pos):
    best, col_b = -2, None
    for col in pos.columns:
        pr = np.array([pos.loc[a, col] if a in pos.index else np.nan for a in order])
        ok = ~np.isnan(pr)
        if ok.sum() >= 4:
            t = kendalltau(np.arange(len(order))[ok], pr[ok]).statistic
            if t > best:
                best, col_b = t, col
    return best, col_b


def main():
    calls, out = sys.argv[1:3]
    res = []
    for f in sorted(glob.glob(calls + '/*.json')):
        name = os.path.basename(f)[:-5]
        code, n = name[8:12], int(name[12:])
        venue, date = MAP[code]
        d = json.load(open(f))
        fld = [(a, b) for a, b in d['field']]
        words = [w for s in d['segments'] for w in s[3]]
        ms = mentions(words, fld)
        cl = clusters(ms)
        pos, fin = truth(venue, date, n)
        row = dict(race=name, n=len(fld), heard=len({t for _, t in ms}), mentions=len(ms), clusters=[])
        for t, order in cl:
            tau, col = best_tau(order, pos)
            nulls = [best_tau(list(rng.permutation(order)), pos)[0] for _ in range(100)]
            finish_tau = None
            fo = [fin.get(a, np.nan) for a in order]
            ok = ~np.isnan(fo)
            if ok.sum() >= 4:
                finish_tau = float(kendalltau(np.arange(len(order))[ok], np.array(fo)[ok]).statistic)
            row['clusters'].append(dict(t=float(t), k=len(order), cover=len(order) / len(fld), tau_gps=float(tau), mark=None if col is None else int(col),
                                        null=float(np.mean(nulls)), p=float(np.mean([x >= tau for x in nulls])), tau_finish=finish_tau))
        res.append(row)
        print(name, 'heard', row['heard'], '/', len(fld), 'clusters', [(round(c['t']), c['k'], round(c['tau_gps'], 2), c['mark']) for c in row['clusters']], flush=True)
    json.dump(res, open(out, 'w'), indent=1)
    cs = [c for r in res for c in r['clusters']]
    if cs:
        print('races', len(res), 'clusters', len(cs), 'mean cover', round(np.mean([c['cover'] for c in cs]), 2),
              '| mean tau vs GPS', round(np.mean([c['tau_gps'] for c in cs]), 3), 'null', round(np.mean([c['null'] for c in cs]), 3),
              '| share p<=0.05', round(np.mean([c['p'] <= 0.05 for c in cs]), 3),
              '| mean heard share', round(np.mean([r['heard'] / r['n'] for r in res]), 3))
        last = [r['clusters'][-1] for r in res if r['clusters'] and r['clusters'][-1]['tau_finish'] is not None]
        print('last cluster tau vs official finish', round(np.mean([c['tau_finish'] for c in last]), 3), 'n', len(last))


if __name__ == '__main__':
    main()
