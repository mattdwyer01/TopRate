"""Barrier vs historical run style table for every venue (like the Flemington 'Rail True' table).
Style = the horse's average 800m position (fraction of field) over its up to 6 earlier runs (needs 2), split Forward / Midfield / Back at the overall 22% / 59% quantiles.
A2E = wins / sum of SP-implied chances normalised to 1 per race; POT% = flat $1 win return at SP minus 1. Clean-book races only (SP book 1.05 to 2.0), one winner, field 5+, no trials or jumps.
Run: PYTHONPATH=. python research/venue_barrier_style.py OUTDIR [--all-rails]"""
import sys, re, html
import numpy as np, pandas as pd
from rc_field_rows import norm_venue
out = sys.argv[1]; ALL_RAILS = '--all-rails' in sys.argv
cols = ['race_id', 'date', 'track', 'field_size', 'barrier', 'horse_id', 'priceStarting', 'positionFinish', 'position800m', 'rail_position', 'isBarrierTrial', 'is_jumpout', 'race_class']
d = pd.concat([pd.read_csv(f'race_results_{y}.csv.gz', usecols=lambda c: c in cols, low_memory=False) for y in range(2017, 2027)])
d = d[(d.isBarrierTrial.astype(str) != 'True') & (d.is_jumpout.astype(str) != 'True') & ~d.race_class.astype(str).str.contains('Hurdle|Steeple', na=False)]
d['date'] = pd.to_datetime(d.date)
for c in ['field_size', 'barrier', 'priceStarting', 'positionFinish', 'position800m']: d[c] = pd.to_numeric(d[c], errors='coerce')
d = d.dropna(subset=['horse_id', 'field_size', 'barrier']).sort_values(['horse_id', 'date'])
d['pf'] = (d.position800m - 1) / (d.field_size - 1)
d['pf'] = d.pf.where(d.field_size >= 5)
d['style_avg'] = d.groupby('horse_id').pf.transform(lambda s: s.shift(1).rolling(6, min_periods=2).mean())
# priced, single winner, clean book
d = d[(d.field_size >= 5) & (d.barrier > 0) & (d.priceStarting > 1)]
d['won'] = (d.positionFinish == 1).astype(int)
g = d.groupby('race_id')
d = d[(g.won.transform('sum') == 1) & (g.priceStarting.transform(lambda s: (1 / s).sum()).between(1.05, 2.0)) & (g.priceStarting.transform('size') >= 0.9 * g.field_size.transform('first'))]
d['p'] = (1 / d.priceStarting) / d.groupby('race_id').priceStarting.transform(lambda s: (1 / s).sum()); d['ret'] = d.won * d.priceStarting - 1; d['half'] = np.where(d.date.dt.year <= 2021, 'A', 'B')
if not ALL_RAILS: d = d[d.rail_position.astype(str).str.startswith('True')]
d = d[d.style_avg.notna()]
q1, q2 = d.style_avg.quantile([.22, .59])
d['style'] = np.where(d.style_avg <= q1, 'Forward', np.where(d.style_avg <= q2, 'Midfield', 'Back'))
d['bg'] = np.where(d.barrier <= 3, 'Inside (1-3)', np.where(d.barrier <= 7, 'Middle (4-7)', 'Wide (8+)'))
d['v'] = d.track.astype(str).map(lambda s: re.sub(r'\s*(synthetic|poly|polytrack|inner|outer)\b.*$', '', norm_venue(s)).strip())
print(f'{len(d)} runners, {d.race_id.nunique()} races, style cut-offs {q1:.3f} / {q2:.3f}; overall A2E {d.won.sum() / d.p.sum():.3f}, POT {d.ret.mean() * 100:.1f}%')
BG = ['Inside (1-3)', 'Middle (4-7)', 'Wide (8+)']; ST = ['Forward', 'Midfield', 'Back']
def cell(x):
    n = len(x); w = x.won.sum(); e = x.p.sum()
    if n == 0: return None
    z = (w - e) / np.sqrt((x.p * (1 - x.p)).sum())
    ha = x[x.half == 'A']; hb = x[x.half == 'B']
    return dict(n=n, wins=int(w), sr=100 * w / n, a2e=w / e, pot=100 * x.ret.mean(), z=z,
                a2eA=ha.won.sum() / ha.p.sum() if len(ha) > 30 else np.nan, a2eB=hb.won.sum() / hb.p.sum() if len(hb) > 30 else np.nan)
rows = []
for v, x in d.groupby('v'):
    if len(x) < 600: continue
    for b in BG + ['Totals']:
        for s in ST:
            xs = x[(x['style'] == s) & ((x.bg == b) | (b == 'Totals'))]
            c = cell(xs)
            if c: rows.append(dict(venue=v, barrier=b, style=s, **c))
print(len(rows), 'cell rows;', d.v.nunique(), 'venues;', (d.v.value_counts() >= 600).sum(), 'with 600+')
R = pd.DataFrame(rows); R.to_csv(f'{out}/venue_barrier_style.csv', index=False)
# html
def col(v, good): return 'color:#b00020' if v < good else ('color:#0a7d33' if v > good else '')
parts = ['<html><head><meta charset="utf-8"><title>Venue barrier vs run style</title><style>body{font-family:sans-serif;margin:20px}table{border-collapse:collapse;margin:0 0 28px;font-size:13px}th{background:#3b4a7a;color:#fff;padding:4px 8px}td{padding:3px 8px;border:1px solid #ddd;text-align:right}td.l{text-align:left;font-weight:600}h2{margin:18px 0 4px}.n{color:#666;font-size:12px}</style></head><body>',
         f'<h1>Barrier vs historical run style, every venue</h1><p class="n">{"All rails" if ALL_RAILS else "Rail true only"}, 2017 to Oct 2026, clean-book races, SP. A2E = wins / expected wins from SP (overall {d.won.sum()/d.p.sum():.2f}). POT = flat $1 win return at SP. Style: average 800m position over the last 6 runs (Forward is the front 22%, Midfield the next 37%, Back the rest). Cells under 30 runners are blank.</p>']
for v in sorted(R.venue.unique()):
    n = int(R[(R.venue == v) & (R.barrier == 'Totals')].n.sum())
    parts.append(f'<h2>{html.escape(v.title())} <span class="n">({n} runners)</span></h2><table><tr><th rowspan=2>Barrier</th>' + ''.join(f'<th colspan=5>{s}</th>' for s in ST) + '</tr><tr>' + 'A2E POT% WinSR% Wins Runners'.split().__len__() * 0 * '' + ''.join('<th>A2E</th><th>POT%</th><th>WinSR%</th><th>Wins</th><th>Runners</th>' for _ in ST) + '</tr>')
    for b in BG + ['Totals']:
        tds = f'<td class="l">{b}</td>'
        for s in ST:
            r = R[(R.venue == v) & (R.barrier == b) & (R['style'] == s)]
            if r.empty or r.iloc[0].n < 30: tds += '<td colspan=5 style="color:#aaa">-</td>'; continue
            r = r.iloc[0]
            tds += f'<td style="{col(r.a2e, .95) if r.a2e < .95 else col(r.a2e, 1.0)}">{r.a2e:.2f}</td><td style="{col(r.pot, 0)}">{r.pot:.1f}</td><td>{r.sr:.1f}</td><td>{r.wins}</td><td>{r.n}</td>'
        parts.append(f'<tr>{tds}</tr>')
    parts.append('</table>')
open(f'{out}/venue_barrier_style.html', 'w').write(''.join(parts) + '</body></html>')
# robust standouts
c = R[R.barrier != 'Totals'].copy(); c = c[c.n >= 150]
c['stable'] = (c.a2eA > 1) & (c.a2eB > 1)
print('\nOverall by style x barrier group:')
print(R[R.venue.notna()].groupby(['barrier', 'style']).apply(lambda z: pd.Series(dict(n=z.n.sum(), a2e=(z.a2e * z.n).sum() / z.n.sum(), pot=(z.pot * z.n).sum() / z.n.sum()))).round(2).to_string())
print(f'\nCells with 150+ runners: {len(c)}; |z|>2: {(c.z.abs() > 2).sum()} (chance ~{0.046 * len(c):.0f}); A2E>1 in both halves & z>2: {(c.stable & (c.z > 2)).sum()}')
print(c[c.z > 2].sort_values('z', ascending=False).head(12)[['venue', 'barrier', 'style', 'n', 'wins', 'a2e', 'pot', 'z', 'a2eA', 'a2eB']].round(2).to_string(index=False))
print(c[c.z < -2.5].sort_values('z').head(8)[['venue', 'barrier', 'style', 'n', 'wins', 'a2e', 'pot', 'z', 'a2eA', 'a2eB']].round(2).to_string(index=False))
print('\nFlemington:'); print(R[(R.venue == 'flemington')].round(2).to_string(index=False))
