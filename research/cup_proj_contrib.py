import sys, os, json, pandas as pd, numpy as np, lightgbm as lgb
sys.path.insert(0, 'projection'); sys.path.insert(0, '.')
os.environ.setdefault('PROJECTION_RATINGS', 'toprate')
import ctx as C
M = C.M; meta = json.load(open(os.path.join(M, 'ctx.json')))
class W:
    def __init__(s, b): s.b = b; s.X = None
    def predict(s, X, **k): s.X = X.copy(); return s.b.predict(X, **k)
rel = W(lgb.Booster(model_file=os.path.join(M, 'ctx_rel_model.txt')))
r = pd.read_csv('../flem/runners.csv', low_memory=False)
r = r[r.venue.astype(str).str.contains('Flemington') & r.date.isin(['2026-11-03', '2026-11-05', '2026-11-07'])]
r = r[pd.to_numeric(r.scratched, errors='coerce').fillna(0) == 0] if 'scratched' in r else r
r['field_size'] = r.groupby(['date','race']).horse.transform('size')
cols = dict(weight_carried='weightCarried', track_grading='trackGrading', prize_money='prize')
r = r.rename(columns=cols)
for c in ('field_size', 'trackGrading', 'race_class', 'barrier', 'jockey', 'trainer'):
    if c not in r: print('missing', c)
T = r[['horse_id','date','jockey','trainer','distance','going','weightCarried','barrier','field_size','race_class','trackGrading','prize','horse','race']].assign(venue='Flemington').reset_index(drop=True)
f, corr = C.predict(T, meta=meta, rel_booster=rel)
T['f'] = f; T['corr'] = corr
stretch = float(meta.get('stretch', 1.2))
Xr = rel.X; ctb = rel.b.predict(Xr, pred_contrib=True)
CB = pd.DataFrame(ctb[:, :-1], columns=Xr.columns, index=Xr.index)
T.to_pickle('../flem/cup_now.pkl'); CB.to_pickle('../flem/cup_contrib.pkl'); Xr.to_pickle('../flem/cup_X.pkl')
cup = T[(T.date == '2026-11-03') & (T.race == 7)]
print('Cup with today\'s models: formula', cup.f.round(1).tolist()[:6], 'corr', cup['corr'].round(1).tolist()[:6])
cc = CB.loc[CB.index.intersection(cup.index)]
rest = CB.loc[CB.index.difference(cup.index)]
d = pd.DataFrame({'Cup mean': cc.mean(), 'rest of week mean': rest.mean()}); d['diff'] = d['Cup mean'] - d['rest of week mean']
print(d.sort_values('diff').head(15).round(2).to_string()); print('...'); print(d.sort_values('diff').tail(5).round(2).to_string())
print('Cup median corr', np.nanmedian(cup['corr']), 'x stretch', stretch, '| rest', np.nanmedian(T.loc[T.index.difference(cup.index), 'corr']))
