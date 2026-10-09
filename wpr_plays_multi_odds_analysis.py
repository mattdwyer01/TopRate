"""Read-only: races with 2+ plays split by the plays' odds, 15-month out-of-sample (complete races, no first starters).
Play = lead (#1, 4+ clear) or map4 (inside 4, SM >= +0.5) or value (4 to 8 off, SM >= +1.0). Price = starting price.
usage: python wpr_plays_multi_odds_analysis.py oos_main.csv.gz"""
import sys
src=open('wpr_plays_multi_analysis.py').read()
exec(src[:src.index("for tag,M in")])
import numpy as np, pandas as pd

def race_table(M):
    P=flag(M); P=P[P.play]; P=P[P.nplay>=2]
    g=P.groupby('race_id')
    R=pd.DataFrame({'n':g.size(),'date':g.date.first(),'minp':g.price.min(),'maxp':g.price.max(),'sump':g.price.sum(),
                    'imp':g.price.apply(lambda s:(1/s).sum()),'hit':g.win.any(),'ret':g.ret.sum(),'fav':g.mrank.min().eq(1),
                    'best_p':g.apply(lambda x:x.sort_values('rating',ascending=False).price.iloc[0])})
    return R

def row(R,label):
    if len(R)<40: print(f'  {label:34}races={len(R):5} (few)'); return
    R=R.sort_values('date'); h=len(R)//2; cost=R.n.sum()
    ex=R.drop(R[R.hit].nlargest(3,'ret').index)  # drop the 3 biggest winning races
    print(f'  {label:34}races={len(R):5} runners/race {R.n.mean():.2f} a play wins {R.hit.mean()*100:4.1f}% (market-implied {R.imp.mean()*100:4.1f}%) ROI {R.ret.sum()/cost*100:+6.1f}% halves {R.ret.iloc[:h].sum()/R.n.iloc[:h].sum()*100:+4.0f}/{R.ret.iloc[h:].sum()/R.n.iloc[h:].sum()*100:+4.0f} ex3 {ex.ret.sum()/ex.n.sum()*100:+6.1f}%')

for tag,M in (('COMPLETE RACES (no first starters)',full),):
    R=race_table(M); print(f'\n===== {tag}: {len(R)} races with 2+ plays, {R.n.sum()} runners =====')
    print('\nBy the shortest play price in the race:')
    for lab,lo,hi in (('under $3',0,3),('$3 to $4',3,4),('$4 to $6',4,6),('$6 to $10',6,10),('$10+',10,999)): row(R[(R.minp>=lo)&(R.minp<hi)],f'shortest play {lab}')
    print('\nBy the best-rated play\'s price:')
    for lab,lo,hi in (('under $3',0,3),('$3 to $5',3,5),('$5 to $8',5,8),('$8+',8,999)): row(R[(R.best_p>=lo)&(R.best_p<hi)],f'best-rated play {lab}')
    print('\nBy the market-implied chance that one of the plays wins (sum of 1/price):')
    for lab,lo,hi in (('under 35%',0,.35),('35 to 45%',.35,.45),('45 to 55%',.45,.55),('55%+',.55,9)): row(R[(R.imp>=lo)&(R.imp<hi)],f'implied {lab}')
    print('\nContains the market favourite vs not:')
    row(R[R.fav],'plays include the favourite'); row(R[~R.fav],'plays do not include the favourite')
    print('\nLongest play price (any play over $10 vs none):')
    row(R[R.maxp>10],'longest play over $10'); row(R[R.maxp<=10],'all plays $10 or under')
    print('\nBy number of plays and favourite:')
    for n in (2,3):
        for f,lab in ((True,'with fav'),(False,'no fav')): row(R[(R.n==n if n==2 else R.n>=3)&(R.fav==f)],f'{n}{"+" if n==3 else ""} plays {lab}')
