"""Sky replay v2: track horses within a shot at 2 fps and carry silk / saddlecloth-number identity along each track.

For one race:  PYTHONPATH=. python3 research/sky_replay_track.py DET_JSON VIDEO SILK_DIR OUT_JSON
(DET_JSON from sky_replay_detect.py at fps 2). Race is named {YYYYMMDD}{CODE}{NN}.

Pipeline: shot cuts from frame histogram changes; per frame jockey/horse candidates with a colour descriptor and an
OCR'd number; greedy IoU linking of candidates inside a shot into tracks; per shot an assignment of runners to tracks using
the evidence summed over the whole track (silk similarity + number votes), so one clear frame identifies the horse for
every frame of its track. Scored against GPS running order (Kendall tau at the best matching GPS mark, against a
permutation null) and by the share of identified runners placed within one rank of GPS.
"""
import json, os, subprocess, sys
import cv2
import numpy as np
from scipy.optimize import linear_sum_assignment
from scipy.stats import kendalltau

sys.path.insert(0, os.path.dirname(__file__))
from sky_replay_eval import MAP, dets, jockey_for, colour_desc, silk_desc, silk_path, sim, ocr_num, load_field, truth  # noqa: E402

rng = np.random.default_rng(0)
W_, H_ = 640, 360
FPS = 2.0


def read_frames(path):
    p = subprocess.Popen(['ffmpeg', '-v', 'error', '-i', path, '-vf', f'fps={FPS}', '-f', 'rawvideo', '-pix_fmt', 'bgr24', '-'],
                         stdout=subprocess.PIPE)
    n = W_ * H_ * 3
    out = []
    while True:
        b = p.stdout.read(n)
        if len(b) < n:
            break
        out.append(np.frombuffer(b, np.uint8).reshape(H_, W_, 3).copy())
    return out


def shot_ids(frames):
    hs = []
    for f in frames:
        h = cv2.calcHist([cv2.resize(f, (64, 36))], [0, 1, 2], None, [6, 6, 6], [0, 256] * 3).ravel()
        hs.append(h / h.sum())
    sid, cur = [0], 0
    for i in range(1, len(hs)):
        if np.minimum(hs[i], hs[i - 1]).sum() < 0.55:
            cur += 1
        sid.append(cur)
    return sid


def iou(a, b):
    x0, y0 = max(a[0], b[0]), max(a[1], b[1])
    x1, y1 = min(a[2], b[2]), min(a[3], b[3])
    i = max(x1 - x0, 0) * max(y1 - y0, 0)
    u = (a[2] - a[0]) * (a[3] - a[1]) + (b[2] - b[0]) * (b[3] - b[1]) - i
    return i / u if u > 0 else 0


def main():
    det_json, video, silk_dir, out = sys.argv[1:5]
    b = os.path.basename(video)[:-4]
    pre, race = b[:12], int(b[12:])
    venue, date = MAP[pre]
    field = load_field(venue, date, race)
    runs, pos, rt = truth(venue, date, race)
    d = json.load(open(det_json))
    frames = read_frames(video)
    sid = shot_ids(frames)
    sd = {tab: silk_desc(silk_path(sk, silk_dir)) for tab, _, sk in field if sk}
    tabs = [k for k in sd if sd[k] is not None]
    valid = set(tabs)
    n = len(runs) if runs is not None else len(field)

    # candidates per frame
    cands = {}
    for i, fr in enumerate(frames):
        key = f'{i / FPS:.2f}'
        if key not in d:
            continue
        h, p = dets(d, key)
        cs = []
        for x in h:
            jp = jockey_for(x, p)
            if jp is None:
                continue
            x0, y0, x1, y1 = [max(int(round(v)), 0) for v in jp[:4]]
            if y1 - y0 < 5 or x1 - x0 < 3:
                continue
            ds = colour_desc(fr[y0:y1, x0:x1])
            if ds is None:
                continue
            cs.append(dict(box=x[:4], jp=jp, sims=np.array([sim(ds, sd[k]) for k in tabs]),
                           num=ocr_num(fr, x, jp, valid), frame=i))
        cands[i] = cs

    # tracks within a shot (greedy IoU link to the previous frame)
    tracks = []
    open_ = []
    for i in sorted(cands):
        new_open = []
        used = set()
        for tr in open_:
            if sid[tr['last_frame']] != sid[i] or i - tr['last_frame'] > 2:
                continue
            best, bi = 0.25, None
            for j, c in enumerate(cands[i]):
                if j in used:
                    continue
                v = iou(tr['members'][-1]['box'], c['box'])
                if v > best:
                    best, bi = v, j
            if bi is not None:
                used.add(bi)
                tr['members'].append(cands[i][bi])
                tr['last_frame'] = i
                new_open.append(tr)
        for j, c in enumerate(cands[i]):
            if j not in used:
                tr = dict(shot=sid[i], members=[c], last_frame=i)
                tracks.append(tr)
                new_open.append(tr)
        open_ = new_open
    tracks = [t for t in tracks if len(t['members']) >= 3]

    # per shot assignment from evidence aggregated over the whole track
    shots = {}
    for t in tracks:
        t['sims'] = np.mean([m['sims'] for m in t['members']], axis=0)
        votes = np.zeros(len(tabs))
        for m in t['members']:
            if m['num'] in tabs:
                votes[tabs.index(m['num'])] += 1
        t['votes'] = votes / len(t['members'])
        shots.setdefault(t['shot'], []).append(t)

    def best_tau(assign, xs):
        best = -1
        for col in pos.columns:
            pr = np.array([pos.loc[a, col] if a in pos.index else np.nan for a in assign])
            ok = ~np.isnan(pr)
            if ok.sum() >= 4:
                best = max(best, abs(kendalltau(xs[ok], pr[ok]).statistic))
        return best

    def placed_share(assign, xs):
        """share of runners whose x-order rank is within 1 of the GPS rank among the same runners (best mark)."""
        best = 0
        for col in pos.columns:
            pr = np.array([pos.loc[a, col] if a in pos.index else np.nan for a in assign])
            ok = ~np.isnan(pr)
            if ok.sum() < 4:
                continue
            for sgn in (1, -1):
                ox = np.argsort(np.argsort(sgn * xs[ok]))
                gp = np.argsort(np.argsort(pr[ok]))
                best = max(best, float(np.mean(np.abs(ox - gp) <= 1)))
        return best

    res = dict(race=b, n=n, frames=len(frames), shots=len(set(sid)), tracks=len(tracks),
               track_frames=sum(len(t['members']) for t in tracks), shot_rows=[])
    for s, ts in sorted(shots.items()):
        if len(ts) < 5 or pos is None:
            continue
        # side-on check on mean box shape
        asp = np.median([(m['box'][2] - m['box'][0]) / max(m['box'][3] - m['box'][1], 1) for t in ts for m in t['members']])
        row = dict(shot=int(s), tracks=len(ts), frames=int(sum(len(t['members']) for t in ts)), aspect=float(asp),
                   jh=float(np.median([m['jp'][3] - m['jp'][1] for t in ts for m in t['members']])))
        for vn, wv in (('silk', 0.0), ('number', 5.0), ('both', 1.0)):
            M = np.array([[(t['sims'][k] if vn != 'number' else 0.01 * t['sims'][k]) + wv * t['votes'][k] for k in range(len(tabs))]
                          for t in ts])
            ri, ci = linear_sum_assignment(-M)
            # mid-shot x position of each track
            xs = np.array([np.mean([(m['box'][0] + m['box'][2]) / 2 for m in ts[i]['members']]) for i in ri])
            assigned = [tabs[c] for c in ci]
            obs = best_tau(assigned, xs)
            nulls = [best_tau(list(rng.permutation(assigned)), xs) for _ in range(40)]
            pl = placed_share(assigned, xs)
            plnull = float(np.mean([placed_share(list(rng.permutation(assigned)), xs) for _ in range(20)]))
            row[vn] = dict(n=len(assigned), tau=obs, null=float(np.mean(nulls)), p_null=float(np.mean([x >= obs for x in nulls])),
                           placed=pl, placed_null=plnull)
        row['ident_numbers'] = int(sum(1 for t in ts if t['votes'].max() >= 0.34))
        res['shot_rows'].append(row)
    # identity propagation: tracks with a number identified in some frame vs frames then covered
    named = [t for t in tracks if t['votes'].max() > 0]
    res['tracks_with_number'] = len(named)
    res['frames_in_number_tracks'] = int(sum(len(t['members']) for t in named))
    res['frames_with_own_number'] = int(sum(sum(1 for m in t['members'] if m['num'] is not None) for t in named))
    json.dump(res, open(out, 'w'), indent=1)
    print(b, {k: v for k, v in res.items() if k != 'shot_rows'}, 'scored shots', len(res['shot_rows']))


if __name__ == '__main__':
    main()
