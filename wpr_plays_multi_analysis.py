"""Read-only: Plays tab, races where 2+ runners qualify as plays vs races with exactly 1, on the 15-month out-of-sample main-model projections
(see wpr_oos_2025_backtest_build.py). Play = lead (#1 and 4+ clear) or map4 (within 4 of the top, SM >= +0.5) or value (4 to 8 off, SM >= +1.0).
usage: python wpr_plays_multi_analysis.py oos_main.csv.gz"""
import sys
src=open('wpr_oos_2025_backtest_analysis.py').read()
exec(src[:src.index("def plays(M)")])
import numpy as np, pandas as pd

def flag(M):
    lead=(M['rank']==1)&(M.lead>=4); map4=(M.gap<4)&(M.sm>=.5); val=(M.gap>=4)&(M.gap<8)&(M.sm>=1.0)
    M=M.copy(); M['play']=lead|map4|val; M['lead_p']=lead; M['map4_p']=map4; M['val_p']=val
    M['nplay']=M.groupby('race_id').play.transform('sum'); return M

def line(x,label):
    if len(x)<40: print(f'  {label:44}n={len(x):5} (few)'); return
    x=x.sort_values('date'); h=len(x)//2; ex=x.drop(x[x.win].nlargest(3,'price').index)
    print(f'  {label:44}n={len(x):5} win={x.win.mean()*100:4.1f}% plc={x.plc.mean()*100:3.0f}% ${x.price.mean():5.2f} ROI={x.ret.mean()*100:+6.1f}% halves {x.ret.iloc[:h].mean()*100:+4.0f}/{x.ret.iloc[h:].mean()*100:+4.0f} ex3 {ex.ret.mean()*100:+6.1f}%')

for tag,M in (('COMPLETE RACES (no light-history runner, so no first starters)',full),('ALL RACES (main-model runners only)',part)):
    M=flag(M); P=M[M.play]
    races=M.groupby('race_id').agg(n=('nplay','first'),date=('date','first'))
    print(f'\n===== {tag} =====\nraces {len(races)}; with 1 play {(races.n==1).sum()}, 2 plays {(races.n==2).sum()}, 3+ plays {(races.n>=3).sum()}, none {(races.n==0).sum()}')
    print('\nPer-runner win bet, by how many plays the race has:')
    line(P[P.nplay==1],'race has 1 play'); line(P[P.nplay==2],'race has 2 plays (both runners)'); line(P[P.nplay>=3],'race has 3+ plays (all runners)')
    print('\nIn races with 2+ plays, by the runner\'s order among the plays (1 = best rated):')
    Q=P[P.nplay>=2].copy(); Q['ord']=Q.groupby('race_id').rating.rank(ascending=False,method='first')
    for o in (1,2,3): line(Q[Q.ord==o],f'play #{o} in race')
    print('\nWhat qualifies the 2nd play in 2-play races (by kind):')
    Q2=Q[(Q.nplay==2)&(Q.ord==2)]
    for k,c in (('lead',Q2.lead_p),('map4',Q2.map4_p),('value',Q2.val_p)): line(Q2[c],f'2nd play is {k}')
    print('\nRace-level: does one of the plays win? (any play wins) and the cost of backing every play $1 each:')
    for lab,sel in (('1 play',races.n==1),('2 plays',races.n==2),('3+ plays',races.n>=3)):
        ids=races.index[sel]; X=P[P.race_id.isin(ids)]
        g=X.groupby('race_id'); hit=g.win.any().mean(); ret=g.ret.sum(); cost=g.size().sum()
        rs=pd.DataFrame({'ret':g.ret.sum(),'n':g.size(),'date':g.date.first()}).sort_values('date'); h=len(rs)//2
        print(f'  {lab:10} races={len(ids):5} a play wins {hit*100:4.1f}%  runners/race {cost/len(ids):.2f}  ROI on all bets {ret.sum()/cost*100:+6.1f}% (per race {ret.mean():+.2f}u)  halves {rs.ret.iloc[:h].sum()/rs.n.iloc[:h].sum()*100:+4.0f}/{rs.ret.iloc[h:].sum()/rs.n.iloc[h:].sum()*100:+4.0f}')
    print('\n2-play races: both plays in the first two / first three, and a quinella of the two plays:')
    ids=races.index[races.n==2]; X=P[P.race_id.isin(ids)]; g=X.groupby('race_id')
    q=(g.fin.apply(lambda s:(s<=2).all())); t3=g.fin.apply(lambda s:(s<=3).all()); one=g.fin.apply(lambda s:(s<=3).any()); 
    print(f'  both in top 2: {q.mean()*100:.1f}%   both in top 3: {t3.mean()*100:.1f}%   at least one in top 3: {one.mean()*100:.1f}%   (random pair at ~{(2/ X.groupby("race_id").field.first().mean()*1/ (X.groupby("race_id").field.first().mean()-1))*100:.1f}% for a top-2 quinella)')
    print('\nWhen the best-rated play loses, how often does the other play win (2-play races)?')
    two=Q[Q.nplay==2]; w1=two[two.ord==1].set_index('race_id').win; w2=two[two.ord==2].set_index('race_id').win
    print(f'  best play wins {w1.mean()*100:.1f}%, second play wins {w2.mean()*100:.1f}%, either {(w1|w2).mean()*100:.1f}%, second wins when best loses {w2[~w1].mean()*100:.1f}%')
