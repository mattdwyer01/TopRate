"""Read-only: builds ~15 months (2025-07-01 onward) of OUT-OF-SAMPLE main-model projections by training the ladder-179 main model on data before 2025
(early stop on 2025-H1), exactly as projection/train_main.py validates it, then scoring every main-model runner from 2025-07 on. Also computes the
suitability adjustment (frozen suitability_model.txt; NOTE it was fitted on older data, so SM here is not strictly out of sample).
Writes oos_main_projections.csv.gz into the scratchpad. usage: python wpr_oos_2025_backtest_build.py OUTFILE   (about 30-40 min)"""
import sys, os, json; sys.path.insert(0,'.'); sys.path.insert(0,'projection')
import numpy as np, pandas as pd, lightgbm as lgb
import features as F, train_main as T
out=sys.argv[1]
L=T.assemble()
n_all=L.groupby('race_id').horse_id.transform('size')
L['n_rated_in_race']=n_all
L=L[(L.nruns>=3)&L[T.BASE].notna().all(axis=1)&L.wpr.notna()&(L.date>='2018-01-01')].copy()
tr,va,te=L[L.date<'2025-01-01'],L[(L.date>='2025-01-01')&(L.date<'2025-07-01')],L[L.date>='2025-07-01'].copy()
feats=T.ORIGINAL+F.LADDER_FEATURES
print('rows',len(L),'train/valid/test',len(tr),len(va),len(te),flush=True)
m,coef=T.fit(tr,feats,None,1,valid=va)
te['p0']=np.c_[np.ones(len(te)),te[T.BASE].values]@coef+m.predict(te[feats],num_iteration=m.best_iteration)
err=te.wpr-te.p0; print('test RMSE %.4f bias %+.3f best_iter %d'%(np.sqrt((err**2).mean()),err.mean(),m.best_iteration),flush=True)
ph=F.build_pos_hist(F.load_history().sort_values(['horse_id','date','race_id']).reset_index(drop=True))
Y=F.load_results_all(); M=F.MODELS
S=F.build_suit(Y,ph,bias_since='2025-06-28'); S=S[S.date>='2025-07-01'].drop_duplicates(['race_id','horse_id'])
Z=te[['race_id','horse_id','bf','field_size','dist','going_num']].merge(S,on=['race_id','horse_id'],how='left',suffixes=('','_s'))
Z=Z.merge(ph[['race_id','horse_id','m800_hist3','own_rel']],on=['race_id','horse_id'],how='left')
Z['sty']=Z.pos_hist3-0.5
Z['i_front'],Z['i_front2']=Z.fa_cum*Z.sty,Z.fa_last*Z.sty
Z['i_out'],Z['i_out2']=Z.oa_cum*(Z.bf-0.5),Z.oa_last*(Z.bf-0.5)
Z['j_style'],Z['j_p8_x']=Z.j_dev*Z.sty,Z.j_p8-Z.pos_hist3
sf=json.load(open(f'{M}/suitability_features.json')); sm=lgb.Booster(model_file=f'{M}/suitability_model.txt')
for c in sf:
    if c not in Z.columns: Z[c]=np.nan
Z['adj']=sm.predict(Z[sf])
te=te.merge(Z[['race_id','horse_id','adj']].drop_duplicates(['race_id','horse_id']),on=['race_id','horse_id'],how='left')
keep=[c for c in ['race_id','horse_id','date','track','field_size','n_rated_in_race','wpr','positionFinish','priceStarting','wt_rel','p0','adj','nruns','jockey'] if c in te.columns]
te[keep].to_csv(out,index=False,compression='gzip'); print('wrote',out,len(te),flush=True)
