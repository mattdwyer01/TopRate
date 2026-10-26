"""Aggregate the per-race JSON from sky_replay_track.py. usage: python research/sky_replay_summary2.py DIR"""
import glob, json, sys
import numpy as np

rs = [json.load(open(f)) for f in sorted(glob.glob(sys.argv[1] + '/**/track_*.json', recursive=True))]
print('races', len(rs))
print('tracks (3+ frames)', sum(r['tracks'] for r in rs), 'frames in tracks', sum(r['track_frames'] for r in rs))
nt, ft, fo = (sum(r.get(k, 0) for r in rs) for k in ('tracks_with_number', 'frames_in_number_tracks', 'frames_with_own_number'))
print('tracks with a number read in >=1 frame', nt, '| frames in those tracks', ft, '| frames where the number itself was read', fo,
      '| propagation multiplier', round(ft / max(fo, 1), 2))
rows = [(r['race'], s) for r in rs for s in r['shot_rows']]
sideon = [(b, s) for b, s in rows if s['aspect'] >= 0.9]
print('scored shots', len(rows), 'side-on', len(sideon))
for name, sel in (('all shots', rows), ('side-on shots', sideon)):
    for v in ('silk', 'number', 'both'):
        x = [s[v] for _, s in sel]
        if x:
            print(name, v, 'shots', len(x), 'mean tracks', round(float(np.mean([a['n'] for a in x])), 1),
                  '| |tau|', round(float(np.mean([a['tau'] for a in x])), 3), 'null', round(float(np.mean([a['null'] for a in x])), 3),
                  '| placed within 1 rank', round(float(np.mean([a['placed'] for a in x])), 3), 'null', round(float(np.mean([a['placed_null'] for a in x])), 3),
                  '| share p<=0.05', round(float(np.mean([a['p_null'] <= 0.05 for a in x])), 3))
for r in rs:
    sb = [s['both'] for s in r['shot_rows'] if s['aspect'] >= 0.9]
    print(r['race'], 'n', r['n'], 'shots', r['shots'], 'tracks', r['tracks'], 'side-on scored', len(sb),
          'placed(both)', round(float(np.mean([a['placed'] for a in sb])), 2) if sb else None)
