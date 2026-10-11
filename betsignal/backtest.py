"""Walk-forward backtest of the production model: for each test year, train (production features and parameters, 3 seeds) on data up to two
years earlier, stop on the year before, score the test year, and report the Select / Volume tiers exactly as score.py defines them.
Prices are closing SP, so this is the optimistic case (see README). usage: python betsignal/backtest.py   (about 15 minutes)"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, pandas as pd, lightgbm as lgb
from betsignal import features as F
from betsignal.score import tier
from betsignal.train import PARAMS, SEEDS, logit

H = F.load_history()
D = F.batch_features(H, F.categories(H))
D['dow'] = D.date.dt.dayofweek
out = []
for ty in range(2022, 2027):
    tr, va, te = D[D.year <= ty - 2], D[D.year == ty - 1], D[D.year == ty].copy()
    raw = 0
    for sd in SEEDS:
        m = lgb.train(dict(PARAMS, seed=sd), lgb.Dataset(tr[F.FEATURES], tr.win, init_score=logit(tr.pm)), 2000,
                      valid_sets=[lgb.Dataset(va[F.FEATURES], va.win, init_score=logit(va.pm))], callbacks=[lgb.early_stopping(80, verbose=False)])
        raw = raw + m.predict(te[F.FEATURES], raw_score=True) / len(SEEDS)
    s = raw + logit(te.pm).values
    from betsignal.score import win_probabilities
    e = win_probabilities(s, te.race_id, te.index).values
    te['pmod'] = e / pd.Series(e, index=te.index).groupby(te.race_id).transform('sum').values
    te['ev'] = te.pmod * te.sp
    te['tier'] = [tier(a, b, c) for a, b, c in zip(te.ev, te.sp, te.rank_m)]
    out.append(te)
    print('done', ty, flush=True)
T = pd.concat(out)
T['ret'] = np.where(T.win == 1, T.sp, 0.0)
T.to_pickle(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'backtest_preds_norm.pkl' if os.environ.get('NORM_FIX') else 'backtest_preds.pkl'))
nsat = T[T.dow == 5].date.nunique()
ll_m, ll_o = -np.log(T.pm[T.win == 1]).mean(), -np.log(T.pmod[T.win == 1]).mean()
print(f'\nlog-loss market {ll_m:.4f} model {ll_o:.4f}')
for label, msk in (('Volume (incl. Select)', T.tier != ''), ('Select', T.tier == 'S'), ('Volume only', T.tier == 'V')):
    x = T[msk].sort_values('date')
    sat = x[x.dow == 5]
    ex10 = x.drop(x[x.win == 1].nlargest(10, 'sp').index)
    q = np.array_split(np.arange(len(x)), 4)
    print(f'{label:22} n={len(x):6} /yr {len(x)/5:5.0f} Sat {len(sat)/nsat:4.1f} win {x.win.mean()*100:4.1f}% ${x.sp.mean():5.2f} ROI {(x.ret.mean()-1)*100:+6.1f}% SatROI {(sat.ret.mean()-1)*100:+6.1f}% '
          'yrs ' + ' '.join(f"{(x[x.year==y].ret.mean()-1)*100:+4.0f}" for y in range(2022, 2027)) +
          ' qtrs ' + ' '.join(f"{(x.ret.iloc[i].mean()-1)*100:+4.0f}" for i in q) +
          f' ex10 {(ex10.ret.mean()-1)*100:+5.1f}% hc10 {(np.where(x.win==1, x.sp*.9, 0).mean()-1)*100:+5.1f}%')
