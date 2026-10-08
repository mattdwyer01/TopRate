"""Read-only: run the EXISTING suitability model on light-history runners (inputs it cannot build left blank) and check whether
its value predicts the light model's miss (actual WPR minus logged projection). Sanity check: main runners must reproduce the log's adj."""
import sys, os, json; sys.path.insert(0,'.')
import numpy as np, pandas as pd, lightgbm as lgb
from projection import features as F
M='projection/models'
H=F.load_history().sort_values(['horse_id','date','race_id']).reset_index(drop=True)
ph=F.build_pos_hist(H)
Y=F.load_results_all()
print('history',len(H),'all runs',len(Y),flush=True)
S=F.build_suit(Y,ph,bias_since='2026-06-25')
S=S[S.date>='2026-07-01'].drop_duplicates(['race_id','horse_id'])
Hd=H[H.date>='2026-07-01'][['race_id','horse_id','distance','going','wpr']].copy()
rm=pd.read_csv('race_results_2026.csv.gz',usecols=['race_id','horse_id','run_id']).drop_duplicates(['race_id','horse_id'])
Hd=Hd.merge(rm,on=['race_id','horse_id'],how='left')
Hd['dist']=Hd.distance;Hd['going_num']=F._num(Hd.going)
Z=Hd.merge(S.drop(columns=[c for c in ('distance','going','wpr','run_id') if c in S.columns]),on=['race_id','horse_id'],how='left')
Z=Z.merge(ph[['race_id','horse_id','m800_hist3','own_rel','pos_hist3']].rename(columns={'pos_hist3':'pos_hist3_ph'}),on=['race_id','horse_id'],how='left',suffixes=('','_p'))
if 'pos_hist3' not in Z.columns or Z.pos_hist3.isna().all(): Z['pos_hist3']=Z.pos_hist3_ph
Z['pos_hist3']=Z.pos_hist3.fillna(Z.pos_hist3_ph)
Z['sty']=Z.pos_hist3-0.5
Z['i_front'],Z['i_front2']=Z.fa_cum*Z.sty,Z.fa_last*Z.sty
Z['i_out'],Z['i_out2']=Z.oa_cum*(Z.bf-0.5),Z.oa_last*(Z.bf-0.5)
Z['j_style'],Z['j_p8_x']=Z.j_dev*Z.sty,Z.j_p8-Z.pos_hist3
sf=json.load(open(f'{M}/suitability_features.json'));sm=lgb.Booster(model_file=f'{M}/suitability_model.txt')
for c in sf:
    if c not in Z.columns: Z[c]=np.nan
Z['adj_all']=sm.predict(Z[sf])
log=pd.read_csv('wpr_projection_log.csv.gz').sort_values('made').drop_duplicates('run_id')
D=Z[['run_id','race_id','adj_all','wpr']].merge(log[['run_id','model','nruns','proj','wtadj','sd']],on='run_id')
D['rating']=D.proj+D.wtadj.fillna(0)
rn=pd.read_csv('toprate_runners.csv',usecols=['run_id','starting_price_sp','fixed_win_price','won','finish_position','scratched','resulted','date'],low_memory=False)
import runners_io
rn=runners_io.read_runners()[['run_id','starting_price_sp','fixed_win_price','won','finish_position','scratched','resulted','date']]
D=D.merge(rn.drop_duplicates('run_id'),on='run_id')
D=D[(D.resulted==1)&(D.scratched.fillna(0)!=1)&(D.date.astype(str)<='2026-10-07')]
D['price']=D.starting_price_sp.fillna(D.fixed_win_price);D=D[D.price.notna()&(D.price>1)]
g=D.groupby('race_id');D=D[g.won.transform('sum').eq(1)&g.run_id.transform('count').ge(6)].copy()
D['gap']=D.groupby('race_id').rating.transform('max')-D.rating
mainmean=D[D.model=='main'].groupby('race_id').adj_all.mean()      # dashboard rule: demean against MAIN-model runners only
D['sm']=D.adj_all-D.race_id.map(mainmean)
D['win']=D.won==1;D['ret']=np.where(D.win,D.price-1,-1);D['t3']=D.finish_position.between(1,3)
D['first']=D.nruns==0
L=D[(D.model=='light')&D.sm.notna()].copy()
L.to_csv('/tmp/claude-0/-home-user-TopRate/f2a6ceff-314e-5923-bf8d-3676f162bf18/scratchpad/light_sm.csv',index=False)
print('light runners with price+result+SM:',len(L),'races',L.race_id.nunique(),'dates',L.date.nunique())
def st(x):
    if len(x)<40: return f'n={len(x):4} (few)'
    x=x.sort_values('date');h=len(x)//2;ex=x.drop(x[x.win].nlargest(3,'price').index)
    return f'n={len(x):4} win={x.win.mean()*100:4.1f}% t3={x.t3.mean()*100:3.0f}% avg${x.price.mean():5.1f} ROI={x.ret.mean()*100:+6.1f}% halves {x.ret.iloc[:h].mean()*100:+4.0f}/{x.ret.iloc[h:].mean()*100:+4.0f} ex3 {ex.ret.mean()*100:+6.1f}%'
print('\nall light runners        ',st(L))
for t in(0.5,1.0):print(f'light SM >= +{t}          ',st(L[L.sm>=t]))
print('light SM <= -0.5         ',st(L[L.sm<=-.5]))
print('\nby prior runs (SM>=+0.5 vs all light):')
for k in(0,1,2):print(f'  {k} runs: ',st(L[(L.nruns==k)&(L.sm>=.5)]),'| all',st(L[L.nruns==k]))
print('\nby gap from top rated:')
for lo,hi in((0,4),(4,6),(6,10),(10,99)):print(f'  gap {lo}-{hi}: ',st(L[(L.gap>=lo)&(L.gap<hi)&(L.sm>=.5)]),'| all',st(L[(L.gap>=lo)&(L.gap<hi)]))
print('\nby price:')
for lo,hi in((1,5),(5,10),(10,20),(20,1000)):print(f'  ${lo}-{hi}: ',st(L[L.price.between(lo,hi)&(L.sm>=.5)]),'| all',st(L[L.price.between(lo,hi)]))
print('\nSM>=+0.5, gap<6, price>=5:',st(L[(L.sm>=.5)&(L.gap<6)&(L.price>=5)]))
