"""Print aggregate results from research/sky_replay_eval.py output. usage: python research/sky_replay_summary.py EVAL_JSON"""
import json, sys
import numpy as np

res = json.load(open(sys.argv[1]))
print('races', len(res))
rec = [r['mean_recall'] for r in res]
tot = sum(r['race_win_frames'] for r in res)
print('mean field recall in race window', round(float(np.mean(rec)), 3),
      '| frames with >=80% of field detected', round(sum(r['frames_ge80'] for r in res) / max(tot, 1), 3),
      '| >=50%', round(sum(r['frames_ge50'] for r in res) / max(tot, 1), 3))
print('races with at least one side-on frame usable for ordering', sum(1 for r in res if r['ord']), 'of', len(res))
fr = [o for r in res for o in r['ord']]
print('usable ordering frames', len(fr))
if fr:
    print('jockey box height px median', round(float(np.median([o['jh'] for o in fr])), 1))
    print('OCR valid number per candidate', round(sum(o.get('ocr_valid', 0) for o in fr) / max(sum(o['cands'] for o in fr), 1), 3))
    for v in ('silk', 'number', 'both'):
        x = [o[v] for o in fr if v in o]
        if x:
            print(v, 'frames', len(x), 'mean |tau|', round(float(np.mean([a['tau'] for a in x])), 3),
                  'null', round(float(np.mean([a['null_mean'] for a in x])), 3),
                  'share beating null p<=0.05', round(float(np.mean([a['p_null_ge'] <= 0.05 for a in x])), 3))
for r in res:
    x = [o['both'] for o in r['ord'] if 'both' in o]
    print(r['race'], 'n', r['n'], 'recall', round(r['mean_recall'], 2), 'ord frames', len(r['ord']),
          'tau both', round(float(np.mean([a['tau'] for a in x])), 2) if x else None)
