"""Proj v2 (winner-trained rating, winner_v2.py) against Proj v1 on the complete-field log (4 Nov 2026).
Rows = every labelled race in data/direct_log whose runners are all in the log (same filter as direct_finish_v3.py T2) and have a Proj v1 figure. The direct model (V3a, trained
before 2025) never saw these races. Features are built by direct_score.build_features, i.e. the production path. Reports winner log-lik / top pick / winner in top 3 / top 4
for Proj v1 (softmax at beta 0.20), the winner model alone, and the blend at several shares, the number of runners and winners inside 2 / 4 points of the top, the
rating sanity (mean, spread, change) and the paired gain over v1 (standard error over races).
  PYTHONPATH=.:projection python research/proj_v2_eval.py [--src live|backfill|all]
"""
import argparse, glob, json, os, sys
import numpy as np, pandas as pd
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT); sys.path.insert(0, os.path.join(ROOT, 'projection'))
import direct_score as DS
import winner_v2 as V2
import runners_io

ap = argparse.ArgumentParser()
ap.add_argument('--src', default='all')
ap.add_argument('--out', default=None, help='pickle of the scored rows')
a = ap.parse_args()

dates = sorted(os.path.basename(f)[:10] for f in glob.glob(os.path.join(ROOT, 'data', 'direct_log', '*.json.gz')))
L = DS.load_log(dates)
L = L[L.won.notna()].copy()
if a.src != 'all':
    L = L[L.src == a.src]
rr = runners_io.read_runners()
rr['race_id'] = pd.to_numeric(rr.race_id, errors='coerce')
act = rr[rr.scratched.fillna(0).astype(float) == 0]
cnt = act.groupby('race_id').size()
L['race_id'] = pd.to_numeric(L.race_id, errors='coerce')
gl = L.groupby('race_id').agg(n=('won', 'size'), w=('won', 'sum'))
ok = gl[(gl.n == gl.index.map(cnt)) & (gl.w == 1) & (gl.n >= 5)].index
L = L[L.race_id.isin(ok)].copy()
print(f'{L.race_id.nunique()} complete labelled races, {len(L)} runners, dates {L.date.min()} to {L.date.max()}', flush=True)

meta = json.load(open(os.path.join(DS.MODEL_DIR, 'meta.json')))['V3a']
Lf = DS.build_features(L, meta)
Lf['dm'] = DS.score(Lf, meta)
Lf['proj'] = pd.to_numeric(Lf.proj, errors='coerce')
Lf['win'] = Lf.won.astype(float)
Lf['pos'] = pd.to_numeric(Lf['finish'], errors='coerce')
Lf['top3'] = (Lf.pos <= 3).astype(float)
Lf = Lf[Lf.groupby('race_id').proj.transform(lambda s: s.notna().all())].copy()
print(f'{Lf.race_id.nunique()} races where every runner has a Proj v1, {len(Lf)} runners', flush=True)


def softmax(s, key):
    e = np.exp(s - s.groupby(key).transform('max'))
    return e / e.groupby(key).transform('sum')


def metrics(df, p, name):
    df = df.assign(p=np.asarray(p))
    ll = np.log(df.loc[df.win == 1].set_index('race_id').p.clip(1e-9))
    rk = df.groupby('race_id').p.rank(ascending=False, method='first')
    out = dict(ll=ll.mean(), top1=df.win[rk == 1].mean(), w3=df.win[rk <= 3].sum() / df.win.sum(), w4=df.win[rk <= 4].sum() / df.win.sum())
    print(f'{name:34s} winner LL {out["ll"]:8.4f}  top pick {out["top1"]:6.1%}  winner in top 3 {out["w3"]:6.1%} top 4 {out["w4"]:6.1%}', flush=True)
    return ll


base = metrics(Lf, softmax(Lf.proj * V2.BETA, Lf.race_id), 'Proj v1 (softmax beta 0.20)')
res = {}
for w in (0.0, 0.4, 0.6, 0.8, 0.9, 1.0):
    Lf[f'v2_{w}'] = V2.to_rating(Lf, w=w)
    ll = metrics(Lf, softmax(Lf[f'v2_{w}'] * V2.BETA, Lf.race_id), f'Proj v2 w={w}')
    d = ll - base
    res[w] = (d.mean(), d.std() / np.sqrt(len(d)))
    print(f'      minus Proj v1: {d.mean():+.4f} (se {d.std() / np.sqrt(len(d)):.4f}) over {len(d)} races', flush=True)
metrics(Lf, Lf.dm, 'winner model alone (chance)')

v = Lf[f'v2_{V2.W_DIRECT}']
print(f'\nrating sanity (w={V2.W_DIRECT}): mean Proj v1 {Lf.proj.mean():.2f} v2 {v.mean():.2f}; within-race sd v1 {Lf.proj.sub(Lf.groupby("race_id").proj.transform("mean")).std():.2f} '
      f'v2 {v.sub(v.groupby(Lf.race_id).transform("mean")).std():.2f}; mean |change| {(v - Lf.proj).abs().mean():.2f}, max {(v - Lf.proj).abs().max():.1f}')
r1 = Lf.groupby('race_id').proj.rank(ascending=False, method='first')
r2 = v.groupby(Lf.race_id).rank(ascending=False, method='first')
print(f'top pick changes in {(Lf.groupby("race_id").apply(lambda g: g.proj.idxmax() != v[g.index].idxmax(), include_groups=False)).mean():.1%} of races')

print('\nrunners and winners inside N points of the top rated runner')
for name, col in (('Proj v1', 'proj'), (f'Proj v2 w={V2.W_DIRECT}', f'v2_{V2.W_DIRECT}')):
    for pts in (2, 4):
        gap = Lf.groupby('race_id')[col].transform('max') - Lf[col]
        ins = gap <= pts
        print(f'   {name:16s} within {pts}: {ins.groupby(Lf.race_id).sum().mean():.2f} runners a race, winners inside {Lf.win[ins].sum() / Lf.win.sum():.1%}')
if a.out:
    Lf.drop(columns=['hist'], errors='ignore').to_pickle(a.out)
