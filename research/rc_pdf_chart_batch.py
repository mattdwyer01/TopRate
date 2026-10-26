"""Resumable batch run of rc_pdf_full.parse_chart over the chart-layout PDFs (list in /tmp/pdf_kinds.csv from the layout scan). One parquet per chunk in work/rc_pdf_chart/."""
import os, sys, glob
import pandas as pd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rc_pdf_full as P

ROOT = P.ROOT
OUT = os.path.join(ROOT, 'work', 'rc_pdf_chart')
os.makedirs(OUT, exist_ok=True)
kinds = pd.read_csv('/tmp/pdf_kinds.csv') if os.path.exists('/tmp/pdf_kinds.csv') else None
files = kinds[kinds.k == 'chart'].f.tolist()
CH = 24
for ci in range(0, len(files), CH):
    out = os.path.join(OUT, f'chunk_{ci // CH:04d}.parquet')
    if os.path.exists(out):
        continue
    W = P.run_charts([os.path.join(ROOT, f) if not os.path.isabs(f) else f for f in files[ci:ci + CH]])
    if W.empty:
        W = pd.DataFrame({'meet_code': []})
    W.to_parquet(out, index=False)
    print('chunk', ci // CH, 'of', (len(files) + CH - 1) // CH, len(W), flush=True)
parts = [pd.read_parquet(f) for f in sorted(glob.glob(os.path.join(OUT, 'chunk_*.parquet')))]
W = pd.concat([p for p in parts if len(p)], ignore_index=True)
W.to_parquet(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_chart_sections.parquet'), index=False)
print('done', W.shape, W.groupby(['meet_code', 'race_no']).ngroups, 'races')
