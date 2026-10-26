"""Export the TAB fixed-win price at fixed minutes before the jump from the Vultr runner's permanent price log (tab_price_log.py), for early-price value tests.
Reads $PRICE_LOG_DIR (default ~/racing-data/tab_prices) YYYY-MM-DD.csv and .csv.gz, one row per read (about every 1 to 2 minutes within 2 h of the jump).
Writes /tmp/price_snap/prices_snap.csv.gz: one row per (date, venue, race_no, tab) with the latest read at or before each offset, plus the last read before the jump.
Run on the self-hosted runner only (the log lives on its disk): research/price_snapshots.yml."""
import glob, gzip, os, sys
from pathlib import Path
import numpy as np, pandas as pd

LOG_DIR = Path(os.environ.get('PRICE_LOG_DIR', Path.home() / 'racing-data' / 'tab_prices'))
OFFS = [120, 90, 60, 45, 30, 20, 10, 5, 2]
files = sorted(glob.glob(str(LOG_DIR / '*.csv*')))
print('log dir', LOG_DIR, 'files', len(files), flush=True)
if not files:
    sys.exit('no price log files found on this runner')
frames = []
for f in files:
    try:
        frames.append(pd.read_csv(f))
    except Exception as e:
        print('skip', f, e)
d = pd.concat(frames, ignore_index=True)
print('rows', len(d), 'dates', d.date.min(), d.date.max(), 'races', d.groupby(['date', 'venue', 'race_no']).ngroups, flush=True)
d['cap'] = pd.to_datetime(d.captured_utc, utc=True, errors='coerce')
d['start'] = pd.to_datetime(d.race_start_utc, utc=True, errors='coerce')
d['mins'] = (d.start - d.cap).dt.total_seconds() / 60
d['p'] = pd.to_numeric(d.fixed_win_price, errors='coerce')
d = d.dropna(subset=['mins', 'p'])
d = d[d.p > 1]
key = ['date', 'venue', 'race_no', 'tab_number']
d = d.sort_values('mins', ascending=False)           # earliest read first
out = d.groupby(key).agg(start=('start', 'first'), reads=('p', 'size'), first_mins=('mins', 'max'), p_open=('p', 'first')).reset_index()
for o in OFFS:
    sub = d[d.mins >= o].sort_values('mins')         # reads at least o minutes before the jump; the closest one last
    last = sub.groupby(key).p.last().rename(f'p_{o}')
    out = out.merge(last.reset_index(), on=key, how='left')
pre = d[d.mins > 0].sort_values('mins')
out = out.merge(pre.groupby(key).p.last().rename('p_last').reset_index(), on=key, how='left')
out = out.merge(pre.groupby(key).mins.last().rename('last_mins').reset_index(), on=key, how='left')
os.makedirs('/tmp/price_snap', exist_ok=True)
out.to_csv('/tmp/price_snap/prices_snap.csv.gz', index=False)
print('written', len(out), 'runners;', out.groupby(['date', 'venue', 'race_no']).ngroups, 'races')
print(out[[c for c in out.columns if c.startswith('p_') or c == 'reads']].notna().mean().round(2).to_string())
