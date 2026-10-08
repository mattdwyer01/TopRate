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
D=Z[['run_id','race_id','adj_all','wpr']].merge(log[['run_id','model','nruns','proj','adj','src']],on='run_id')
main=D[D.model=='main'].dropna(subset=['adj'])
print('\nsanity, main runners: corr(recomputed, logged adj) = %.3f  mean abs diff %.3f  n=%d'%(main.adj_all.corr(main.adj),(main.adj_all-main.adj).abs().mean(),len(main)))
L=D[(D.model=='light')&D.wpr.notna()].copy()
L['miss']=L.wpr-L.proj
L['sm']=L.adj_all-L.groupby('race_id').adj_all.transform('mean')
print('\nlight runners',len(L),'adj_all sd %.2f'%L.adj_all.std(),'| main sd %.2f'%main.adj_all.std())
for k,g in L.groupby('nruns'):
    print(f'  prior runs {int(k)}: n={len(g)} adj sd {g.adj_all.std():.2f} corr(adj, miss) {g.adj_all.corr(g.miss):+.3f} corr(demeaned, miss) {g.sm.corr(g.miss):+.3f}')
import numpy.polynomial.polynomial as P
b=np.polyfit(L.sm.fillna(0),L.miss,1);print('slope of miss on demeaned adj (all light): %.2f  (1.0 = the value is worth its face)'%b[0])
# same on main runners
main=main.assign(miss=main.wpr-main.proj,sm=lambda x:x.adj_all-x.groupby('race_id').adj_all.transform('mean'))
mm=main.dropna(subset=['miss','sm']);print('slope of miss on demeaned adj (main, for reference, base model includes adj already so ~0 expected)  %.2f'%np.polyfit(mm.sm,mm.miss,1)[0])
print('\nbuckets of demeaned adj, light runners: mean miss (actual - projection)')
L['b']=pd.cut(L.sm,[-9,-1,-.5,-.2,.2,.5,1,9])
print(L.groupby('b',observed=True).miss.agg(['count','mean']).round(2))
