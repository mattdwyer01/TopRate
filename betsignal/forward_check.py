"""The live check: judges every logged bet at the price when its last pre-jump pass was made.
usage: python betsignal/forward_check.py [--mins 5]   reads bet_signal_log.csv.gz (written by score.py) and toprate_runners.csv (results)."""
import argparse, os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, pandas as pd
import runners_io

ap = argparse.ArgumentParser(); ap.add_argument('--mins', type=float, default=5.0); a = ap.parse_args()
L = pd.read_csv(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'bet_signal_log.csv.gz'))
L = L[L.mins >= a.mins].sort_values('made').groupby('run_id').tail(1)          # last pass at least `mins` before the jump
R = runners_io.read_runners()[['run_id', 'finish_position', 'won', 'starting_price_sp']].drop_duplicates('run_id')
X = L.merge(R, on='run_id', how='left')
X = X[(X.won.notna()) | (pd.to_numeric(X.finish_position, errors='coerce').notna())]
X['win'] = (X.won == 1) | (pd.to_numeric(X.finish_position, errors='coerce') == 1)
units = {'S': 2.0, 'V': 0.5}
for t, name in (('S', 'Select'), ('V', 'Volume')):
    x = X[X.tier == t]
    if x.empty: print(f'{name}: no resulted bets yet'); continue
    flat = np.where(x.win, x.price - 1, -1.0)
    sp = np.where(x.win, x.starting_price_sp.fillna(x.price) - 1, -1.0)
    print(f'{name}: {len(x)} bets, {int(x.win.sum())} won ({x.win.mean()*100:.1f}%), avg ${x.price.mean():.2f}, flat ROI at pass price {flat.mean()*100:+.1f}%, at SP {sp.mean()*100:+.1f}%, '
          f'staked {len(x)*units[t]:.1f}u, profit {(flat*units[t]).sum():+.1f}u')
