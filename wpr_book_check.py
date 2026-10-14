"""Does the projection rule's apparent edge come from races where the SP book is thin (sum of 1/SP lower)? (14 Oct 2026)
Reuses the setup of wpr_value_rules_three_models.py. usage: python wpr_book_check.py speed_preds.pkl proj_oos.pkl"""
import sys
import numpy as np, pandas as pd
src = open('wpr_value_rules_three_models.py').read().split('GRID =')[0]
exec(src)
T = calibrated('p_proj')
T['book'] = 1 / T.sp
T['book'] = T.groupby('race_id').book.transform('sum')          # overround: >1 means the SP book is over-round, <1 under-round
T['ev_n'] = T.cp * T.sp / T.book                                 # EV if the price is scaled to a fair (100%) book
rules = {'A: EV>1.5, $3-15, topp>=.30, rank<=2': (T.ev > 1.5) & T.sp.between(3, 15) & (T.topcp >= .30) & (T.rk <= 2),
         'B: A and field<=10, mkt rank>=1': (T.ev > 1.5) & T.sp.between(3, 15) & (T.topcp >= .30) & (T.rk <= 2) & (T.field_size <= 10)}
races = T.drop_duplicates('race_id')
print('SP book (sum of 1/SP) over all complete races: mean %.3f, quartiles %s, share under 100%%: %.1f%%' % (races.book.mean(), races.book.quantile([.25, .5, .75]).round(3).tolist(), (races.book < 1).mean() * 100))
cuts = [0, 1.0, 1.10, 1.20, 9]
lab = ['<100%', '100-110%', '110-120%', '>120%']
T['bb'] = pd.cut(T.book, cuts, labels=lab, right=False)
print('\nshare of ALL complete races by book band:', (pd.cut(races.book, cuts, labels=lab, right=False).value_counts(normalize=True).sort_index() * 100).round(1).to_dict())
for name, m in rules.items():
    X = T[m]
    print(f'\n=== rule {name}: {len(X)} bets, mean book on its races {X.book.mean():.3f} vs all races {races.book.mean():.3f}')
    print('  share of bets by book band:', (X.bb.value_counts(normalize=True).sort_index() * 100).round(1).to_dict())
    for per in ('dev', 'hold'):
        Y = X[X.period == per]
        print(f'  {per}: ' + ' | '.join(f'{b}: n={len(g)} ROI {(g.ret.mean()-1)*100:+.0f}%' for b, g in Y.groupby('bb', observed=True)))
    print('  all periods by band: ' + ' | '.join(f'{b}: n={len(g)} win {g.win.mean()*100:.1f}% (mkt-implied, book-normalised {g.pm.mean()*100:.1f}%) ROI {(g.ret.mean()-1)*100:+.0f}%' for b, g in X.groupby('bb', observed=True)))
    # same bets priced as if the book were fair (100%): return = win * sp / book
    fair = np.where(X.win == 1, X.sp / X.book, 0.0)
    print(f'  ROI at SP {(X.ret.mean()-1)*100:+.1f}%   ROI if prices were scaled to a fair 100% book {(fair.mean()-1)*100:+.1f}%   (hold only: {(X.ret[X.period=="hold"].mean()-1)*100:+.1f}% vs {(fair[(X.period=="hold").values].mean()-1)*100:+.1f}%)')
    # does the rule still show a hit-rate lift inside each band, and compare to the same-band all-runner baseline?
    print('  hit-rate lift vs book-normalised market by band: ' + ' | '.join(f'{b}: {(g.win.mean()-g.pm.mean())*100:+.1f} pts' for b, g in X.groupby('bb', observed=True)))
# the rule restricted to races with book >= 110% (a normal, non-thin book)
m = rules['A: EV>1.5, $3-15, topp>=.30, rank<=2'] & (T.book >= 1.10)
X = T[m]
print(f'\nRule A only in races with book >= 110%: n={len(X)} (dev {(X.period=="dev").sum()}, hold {(X.period=="hold").sum()}); ROI dev {(X.ret[X.period=="dev"].mean()-1)*100:+.1f}%, hold {(X.ret[X.period=="hold"].mean()-1)*100:+.1f}%, win {X.win.mean()*100:.1f}% vs mkt {X.pm.mean()*100:.1f}%')
