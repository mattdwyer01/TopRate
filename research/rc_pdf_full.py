"""Full parse of the Racing Victoria / Triple S sectional PDFs (VIC, SA), 26 Oct 2026. rc_pdf_gps.py keeps only Distance from Rail. Each runner page also prints, per
section (about 200m): time remaining at the post with the runner's rank [n], the section time, average speed, top speed, average distance to rail, stride frequency (Hz) and
stride length (m). Page 1 has the field times and the race tempo per section, the track rating, weather and rail text.
Reads work/rc_pdf/*.pdf (downloaded by rc_pdf_gps.py download) through `pdftotext -raw`. Writes data/gps/rc_pdf_full_sections.parquet (runner x section) and
data/gps/rc_pdf_full_races.parquet (race level). Horses are matched to TAB numbers through data/gps/rc_pdf_rail_*.parquet.
  python research/rc_pdf_full.py [--limit N]
"""
import glob, os, re, subprocess, sys
from multiprocessing import Pool
import numpy as np, pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
T = r'(-:--\.--|\d+:\d\d\.\d\d)'


def tsec(s):
    if s is None or s.startswith('-'):
        return np.nan
    m, r = s.split(':')
    return int(m) * 60 + float(r)


def nums(line):
    out = []
    for tok in line.split():
        try:
            out.append(float(tok))
        except ValueError:
            out.append(np.nan)
    return out


def parse(path):
    try:
        txt = subprocess.run(['pdftotext', '-raw', path, '-'], capture_output=True, text=True, timeout=60).stdout.replace('\f', '\n')
    except Exception:
        return [], None
    stem = os.path.basename(path)[:-4]
    meet, race = stem.split('_')
    parts = re.split(r'(?m)^Horse/Jockey Name ', txt)
    head = parts[0]
    race_row = dict(meet_code=meet, race_no=int(race))
    m = re.search(r'Track Rating: ([^,]+), Weather: ([^,]+), Rail Position: (.*)', head)
    if m:
        race_row.update(track_rating=m.group(1).strip(), weather=m.group(2).strip(), rail_text=m.group(3).strip())
    ft = re.search(r'Field Times\s*\n((?:.*\n)*?)\(Race Tempo\)\s*\n((?:\(.*\)\s*\n)+)', head)
    if ft:
        race_row['field_times'] = ' '.join(re.findall(T, ft.group(1)))
        race_row['tempo'] = ' '.join(re.findall(T, ft.group(2)))
    rows = []
    for blk in parts[1:]:
        lines = [x.strip() for x in blk.split('\n')]
        name = lines[0].split('/')
        horse = name[0].strip()
        fr = re.search(r'Finish Rank (\S+)', blk)
        labs = None
        for ln in lines:
            if ln.startswith('Section L') or re.match(r'^Section( L\d+)+$', ln):
                labs = re.findall(r'L\d+', ln)
                break
        if not labs:
            continue
        i0 = next((i for i, x in enumerate(lines) if x.startswith('Section Times')), None)
        i1 = next((i for i, x in enumerate(lines) if x.startswith('Average Speed')), None)
        if i0 is None or i1 is None:
            continue
        cum, sec, rank = [], [], []
        for ln in lines[i0 + 1:i1]:
            m1 = re.match(r'^' + T + r'(?: \[(\d+)\])?$', ln)
            m2 = re.match(r'^\(' + T + r'\)$', ln)
            if m1:
                cum.append(tsec(m1.group(1)))
                rank.append(float(m1.group(2)) if m1.group(2) else np.nan)
            elif m2:
                sec.append(tsec(m2.group(1)))
        vals = {}
        for key, pat in (('avg_kmh', r'^Average Speed \[km/h\](.*)$'), ('top_kmh', r'^Top Speed \[km/h\]((?: [\d.]+| NA)+)$'), ('rail_m', r'^Avg\. Dist\. to Rail \[m\](.*)$'),
                         ('stride_hz', r'^Avg\. Stride Freq\. \[Hz\](.*)$'), ('stride_m', r'^Avg\. Stride Length \[m\](.*)$')):
            for ln in lines:
                mm = re.match(pat, ln)
                if mm:
                    vals[key] = nums(mm.group(1))
                    break
        n = len(labs)
        for j in range(n):
            rows.append(dict(meet_code=meet, race_no=int(race), horse=horse, finish=fr.group(1) if fr else None, label=labs[j], j=j, n_sec=n,
                             remaining_s=cum[j] if j < len(cum) else np.nan, rank=rank[j] if j < len(rank) else np.nan, sect_s=sec[j] if j < len(sec) else np.nan,
                             **{k: (v[j] if j < len(v) else np.nan) for k, v in vals.items()}))
    return rows, race_row


if __name__ == '__main__':
    files = sorted(glob.glob(os.path.join(ROOT, 'work', 'rc_pdf', '*.pdf')))
    if '--limit' in sys.argv:
        files = files[:int(sys.argv[sys.argv.index('--limit') + 1])]
    with Pool(4) as p:
        res = p.map(parse, files, chunksize=20)
    S = pd.DataFrame([r for rows, _ in res for r in rows])
    R = pd.DataFrame([rr for _, rr in res if rr])
    rail = pd.concat([pd.read_parquet(f) for f in glob.glob(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_rail_*.parquet'))])
    tab = rail[['meet_code', 'race_no', 'horse', 'tab_no']].drop_duplicates(['meet_code', 'race_no', 'horse'])
    S['race_no'] = S.race_no.astype(int)
    S['meet_code'] = S.meet_code.astype(str)
    tab['meet_code'] = tab.meet_code.astype(str)
    S = S.merge(tab, on=['meet_code', 'race_no', 'horse'], how='left')
    print('races', len(R), 'runner-sections', len(S), 'runners', S.groupby(['meet_code', 'race_no', 'horse']).ngroups, 'tab matched', S.tab_no.notna().mean().round(3))
    for c in ('avg_kmh', 'top_kmh', 'rail_m', 'stride_hz', 'stride_m', 'remaining_s', 'rank'):
        print(c, 'filled', S[c].notna().mean().round(3))
    if '--limit' not in sys.argv:
        S.to_parquet(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_full_sections.parquet'), index=False)
        R.to_parquet(os.path.join(ROOT, 'data', 'gps', 'rc_pdf_full_races.parquet'), index=False)
