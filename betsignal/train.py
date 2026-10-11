"""Trains the market-residual win model and saves it to betsignal/models/.
Walk-forward recipe from the research (see README): LightGBM binary, started from the normalised market probability (init score),
heavily regularised, early-stopped on the most recent 365 days, then refitted on everything with that many rounds. 3 seeds averaged.
usage: python betsignal/train.py   (about 6-8 minutes)"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, pandas as pd, lightgbm as lgb
from betsignal import features as F

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'models')
PARAMS = dict(objective='binary', learning_rate=.03, num_leaves=15, min_data_in_leaf=400, feature_fraction=.7, bagging_fraction=.7,
              bagging_freq=1, lambda_l2=50, verbose=-1)
SEEDS = (1, 2, 3)
logit = lambda p: np.log(p / (1 - p))


def main():
    os.makedirs(OUT, exist_ok=True)
    H = F.load_history()
    cats = F.categories(H)
    D = F.batch_features(H, cats)
    last = D.date.max()
    cut = last - pd.Timedelta(days=365)
    tr, va = D[D.date <= cut], D[D.date > cut]
    iters = []
    for sd in SEEDS:
        m = lgb.train(dict(PARAMS, seed=sd), lgb.Dataset(tr[F.FEATURES], tr.win, init_score=logit(tr.pm)), 2000,
                      valid_sets=[lgb.Dataset(va[F.FEATURES], va.win, init_score=logit(va.pm))], callbacks=[lgb.early_stopping(80, verbose=False)])
        iters.append(m.best_iteration)
        print('seed', sd, 'best iteration', m.best_iteration, flush=True)
    n_rounds = int(np.mean(iters) * 1.1)
    for sd in SEEDS:
        m = lgb.train(dict(PARAMS, seed=sd), lgb.Dataset(D[F.FEATURES], D.win, init_score=logit(D.pm)), n_rounds)
        m.save_model(os.path.join(OUT, f'bet_seed{sd}.txt'))
    from betsignal.score import _results_signature
    state = F.build_state(H)
    state['sig'] = _results_signature()
    pd.to_pickle(state, os.path.join(OUT, 'state.pkl'))
    meta = dict(features=F.FEATURES, cats=cats, rounds=n_rounds, seeds=list(SEEDS), trained_through=str(last.date()), rows=len(D),
                races=int(D.race_id.nunique()))
    json.dump(meta, open(os.path.join(OUT, 'meta.json'), 'w'), indent=1)
    print('saved', meta['rows'], 'rows through', meta['trained_through'], 'rounds', n_rounds)


if __name__ == '__main__':
    main()
