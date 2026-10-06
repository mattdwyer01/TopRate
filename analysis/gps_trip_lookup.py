"""Expected trip for a barrier at a track/distance/going/rail, from 184k GPS-tracked runs (VIC/SA 2021-26, QLD 2022-26).
Returns extra ground (m beyond race distance), lane (avg metres off the rail), settle (fraction of field at 800m, 0=lead)
and gap to leader at 800m (lengths). Pre-race conditions explain only a modest share (extra ~24%, lane ~22-27%, settle/gap ~0-12%
of variance); settle/gap depend mostly on the horse's own style. Context, not a rating input.
Usage: python gps_trip_lookup.py Flemington 1400 "Good 4" "Out 5m" """
import os,sys,pandas as pd
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from gps_trip_build import LEV,K,T,OUT,prep
from position_bias_lookup import going_bucket,rail_bucket,band_of
def lookup(track,distance,going=None,rail=None):
    bgs=['1-3','4-6','7-9','10-12','13+'];rows=[]
    for bg in bgs:
        kv={'band':band_of(int(distance)),'bg':bg,'gb':going_bucket(going),'rl':rail_bucket(rail),'track':track,'dist':int(round(distance/100)*100)};r={'barrier':bg}
        for t in T:
            est=pd.read_csv(os.path.join(OUT,f'{t}__root.csv'))['mean'].iloc[0]
            for name,keys in LEV:
                d=pd.read_csv(os.path.join(OUT,f'{t}__{name.replace("+","_")}.csv'));m=d
                for k in keys:m=m[m[k]==kv[k]]
                if len(m):n=m['n'].iloc[0];w=n/(n+K[t]);est=w*m['mean'].iloc[0]+(1-w)*est;r[t+'_n']=int(n)
            r[t]=round(est,2)
        rows.append(r)
    return pd.DataFrame(rows)[['barrier']+T+['extra_n']]
if __name__=='__main__':
    a=sys.argv[1:]
    if len(a)<2:sys.exit(__doc__)
    print(lookup(a[0],int(a[1]),a[2] if len(a)>2 else None,a[3] if len(a)>3 else None).to_string(index=False))
