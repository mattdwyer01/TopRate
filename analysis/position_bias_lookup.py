"""Position bias lookup for an upcoming race's conditions.

For a track, distance, going and rail, returns how often each running position
at 800m has won relative to the market's own win probability (A/E: 1.00 is fair,
above 1.00 means winners come from that position more often than prices imply).

Estimates start from the pooled value of each position and are refined step by
step (distance band, going, rail, track, exact distance). Each step is blended
with the one before it according to how much data its cell has (empirical Bayes
shrinkage), so thin cells fall back to broader ones.

Built from 895k runners in 85k races (fields of 8 or more, all runners priced).
These are hindsight values: they describe what a position was worth once a horse
was there. Applied pre-race (via predicted positions) they added nothing beyond
the market in testing, so treat them as race-reading context, not a betting edge.

Usage:  python position_bias_lookup.py Flemington 1200 "Good 4" "Out 5m" [--scheme pos|gap]
"""
import json,os,re,sys
import pandas as pd

HERE=os.path.dirname(os.path.abspath(__file__));TAB=os.path.join(HERE,'position_bias_tables')
K=json.load(open(os.path.join(HERE,'position_bias_K.json')))
LEV=[('band',['band']),('band+going',['band','gb']),('band+going+rail',['band','gb','rl']),('track+band',['track','band']),
     ('track+dist',['track','dist']),('track+dist+going',['track','dist','gb']),('track+dist+going+rail',['track','dist','gb','rl'])]
LABELS={'pos':['1 lead','2 handy (2-3)','3 mid-front','4 mid-back','5 back'],'gap':['0 (leader)','<1L','1-3L','3-6L','6-10L','10L+']}
COL={'pos':'b_pos','gap':'b_gap'};_cache={}

def _load(scheme,name):
    k=(scheme,name)
    if k not in _cache:_cache[k]=pd.read_csv(os.path.join(TAB,f'{scheme}__{name.replace("+","_")}.csv'))
    return _cache[k]

def band_of(d):
    return 'sprint<=1100' if d<=1150 else '1200-1400' if d<=1450 else '1500-1800' if d<=1850 else '2000+'

def going_bucket(g):
    if g is None:return 'syn/unk'
    if isinstance(g,(int,float)):n=float(g)
    else:
        m=re.search(r'(\d+)',str(g))
        if not m:return 'syn/unk'
        n=float(m.group(1))
    return 'dry' if n<=4 else 'soft' if n<=7 else 'heavy'

def rail_bucket(r):
    if r is None:return 'unk'
    if isinstance(r,(int,float)):m=float(r)
    else:
        s=str(r)
        if 'true' in s.lower():return 'true'
        mm=re.search(r'(\d+)\s*m',s)
        if not mm:return 'unk'
        m=float(mm.group(1))
    return 'true' if m<=0.5 else '1-3m' if m<=3 else '4-6m' if m<=6 else '7-9m' if m<=9 else '10m+'

def lookup(track,distance,going=None,rail=None,scheme='pos'):
    col=COL[scheme];kv={'band':band_of(int(distance)),'gb':going_bucket(going),'rl':rail_bucket(rail),'track':track,'dist':int(distance)}
    root=_load(scheme,'root').set_index(col).AE;est=root.copy();out=pd.DataFrame({'pooled':root});support={}
    for name,keys in LEV:
        t=_load(scheme,name);m=t
        for key in keys:m=m[m[key]==kv[key]]
        m=m.set_index(col);new=est.copy();sup=pd.Series(0.0,index=est.index)
        for b in m.index:
            E=m.loc[b,'E'];w=E/(E+K[col]);new[b]=w*m.loc[b,'AE_raw']+(1-w)*est[b];sup[b]=E
        est=new;out[name]=est;support[name]=sup
    out.index=[LABELS[scheme][int(i)] for i in out.index]
    res=out[['pooled']+[n for n,_ in LEV]].round(2)
    res['expected wins in most detailed cell']=support['track+dist+going+rail'].round(0).values
    return res,kv

if __name__=='__main__':
    a=[x for x in sys.argv[1:] if not x.startswith('--')];scheme='gap' if '--scheme' in sys.argv and sys.argv[sys.argv.index('--scheme')+1]=='gap' else 'pos'
    a=[x for x in a if x not in ('pos','gap')]
    if len(a)<2:sys.exit(__doc__)
    t,d=a[0],int(a[1]);g=a[2] if len(a)>2 else None;r=a[3] if len(a)>3 else None
    res,kv=lookup(t,d,g,r,scheme);print(f'{t} {d}m | going bucket: {kv["gb"]} | rail bucket: {kv["rl"]} | distance band: {kv["band"]}\n');print(res.to_string())
