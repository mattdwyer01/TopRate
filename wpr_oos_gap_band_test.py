"""Read-only: gap-from-top bands (0-2, 2-4, 4-6, 6-8, 4-8) crossed with SM tiers on the 15-month out-of-sample main-model projections
(see wpr_oos_2025_backtest_build.py). usage: python wpr_oos_gap_band_test.py oos_main.csv.gz"""
import sys
src=open('wpr_oos_2025_backtest_analysis.py').read()
exec(src[:src.index("for tag,M in")])
def tiers(M):
    return [('any SM',M.price>0),('SM>=+0.5',M.sm>=.5),('SM>=+1.0',M.sm>=1.0),('SM<=-0.5',M.sm<=-.5)]
bands=[('0-2',0,2),('2-4',2,4),('4-6',4,6),('6-8',6,8),('4-8',4,8),('8+',8,99)]
for tag,M in (('COMPLETE RACES',full),('ALL RACES (main runners only)',part)):
    print('\n=====',tag,'=====')
    # capture: share of winners and runners per race inside each line
    nr=M.race_id.nunique(); w=M[M.win]
    print('line capture (share of winners, runners per race):',' | '.join(f'<={g}: {(w.gap<=g).mean()*100:.0f}% winners, {(M.gap<=g).sum()/nr:.2f} runners' for g in (2,4,6,8)))
    print(f'\n{"band":6}{"SM tier":10}','result')
    for b,lo,hi in bands:
        for tn,tf in tiers(M):
            x=M[(M.gap>=lo)&(M.gap<hi)&tf.reindex(M.index)]
            print(f'{b:6}{tn:10}{st(x)}')
        print()
    print('4-6 and 4-8 over $5, and share of the SM+0.5 pool they add:')
    for b,lo,hi in (('0-4',0,4),('4-6',4,6),('4-8',4,8),('6-8',6,8)):
        for tn,tf in tiers(M)[1:3]:
            x=M[(M.gap>=lo)&(M.gap<hi)&tf.reindex(M.index)&(M.price>5)]
            print(f'  {b} over $5 {tn:9}{st(x)}')
