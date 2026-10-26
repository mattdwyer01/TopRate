"""Sky replay feasibility evaluation: coverage, silk distinguishability, silk-matched running order vs GPS.

Inputs: detections from research/sky_replay_detect.py (0.25 fps) per video, the runner silks from
toprate_history.json, GPS truth from data/gps/rc_gps_*. Run with:
  PYTHONPATH=. python3 -I research/sky_replay_eval.py DET_DIR VID_DIR SILK_DIR OUT_JSON
Races are named {YYYYMMDD}{CODE}{NN}; MAP below gives (venue, date) per file prefix.
"""
import glob, hashlib, json, os, sys
import cv2
import numpy as np
import pandas as pd
import torch
from scipy.optimize import linear_sum_assignment
from scipy.stats import kendalltau
from torchvision.ops import nms

MAP = {'20261024FLER': ('Flemington', '2026-10-24'), '20261024MOPR': ('Morphettville', '2026-10-24'),
       '20261017CAUR': ('Caulfield', '2026-10-17')}
rng = np.random.default_rng(0)


def load_field(venue, date, race):
    j = json.load(open('toprate_history.json'))
    for r in j['RACES']:
        if r['venue'] == venue and r['date'] == date and r['race'] == race:
            return [(x['tab'], x['h'], x.get('sk')) for x in r['runners'] if not x.get('scr')]
    return []


def silk_path(sk, silk_dir):
    return os.path.join(silk_dir, hashlib.md5(sk.encode()).hexdigest() + '.png')


def colour_desc(bgr, mask=None):
    """8 hue bins weighted by saturation, plus white and dark fractions (normalised)."""
    hsv = cv2.cvtColor(bgr, cv2.COLOR_BGR2HSV).reshape(-1, 3).astype(np.float32)
    if mask is not None:
        hsv = hsv[mask.reshape(-1)]
    if len(hsv) == 0:
        return None
    h, s, v = hsv[:, 0] * 2, hsv[:, 1] / 255, hsv[:, 2] / 255
    white = (s < 0.2) & (v > 0.6)
    dark = v < 0.25
    col = ~white & ~dark
    hist = np.zeros(8)
    if col.any():
        b = (h[col] // 45).astype(int) % 8
        np.add.at(hist, b, s[col] * v[col])
    out = np.concatenate([hist, [white.sum(), dark.sum()]]).astype(np.float64)
    return out / max(out.sum(), 1e-9)


def silk_desc(path):
    im = cv2.imread(path, cv2.IMREAD_UNCHANGED)
    return colour_desc(im[..., :3], im[..., 3] > 128)


def sim(a, b):
    return np.minimum(a, b).sum()


def dets(d, t, thr=0.5):
    rows = d[t]
    h = [r for r in rows if r[5] == 'horse' and r[4] >= thr]
    p = [r for r in rows if r[5] == 'person' and r[4] >= 0.3]
    if h:
        keep = nms(torch.tensor([r[:4] for r in h]), torch.tensor([r[4] for r in h]), 0.5).tolist()
        h = [h[i] for i in keep]
    return h, p


def jockey_for(hbox, persons):
    cx = (hbox[0] + hbox[2]) / 2
    cy = (hbox[1] + hbox[3]) / 2
    best, bd = None, 1e9
    for p in persons:
        px = (p[0] + p[2]) / 2
        py = (p[1] + p[3]) / 2
        if hbox[0] - 5 <= px <= hbox[2] + 5 and py < cy:
            dd = abs(px - cx) + abs(py - hbox[1])
            if dd < bd:
                best, bd = p, dd
    return best


def truth(venue, date, race):
    y = date[:4]
    r = pd.read_parquet(f'data/gps/rc_gps_runs_{y}.parquet')
    s = pd.read_parquet(f'data/gps/rc_gps_sections_{y}.parquet')
    r = r[(r.venue == venue) & (r.start_utc.str[:10] == date) & (r.race_no == race)]
    if r.empty:
        return None, None, None
    m = r.meet_code.iloc[0]
    s = s[(s.meet_code == m) & (s.race_no == race)]
    pos = s.pivot_table(index='tab_no', columns='from_m', values='pos')
    return r, pos, float(r.race_time_s.iloc[0])


def main():
    det_dir, vid_dir, silk_dir, out = sys.argv[1:5]
    res = []
    for f in sorted(glob.glob(det_dir + '/2026*.json')):
        b = os.path.basename(f)[:-5]
        pre, race = b[:12], int(b[12:])
        if pre not in MAP:
            continue
        venue, date = MAP[pre]
        d = json.load(open(f))
        field = load_field(venue, date, race)
        runs, pos, rt = truth(venue, date, race)
        n = len(runs) if runs is not None else len(field)
        ts = sorted(d, key=float)
        cnt = {t: len(dets(d, t)[0]) for t in ts}
        raceT = [t for t in ts if cnt[t] >= 3]
        t_first, t_last = (float(raceT[0]), float(raceT[-1])) if raceT else (0, 0)
        win = [t for t in ts if t_first <= float(t) <= t_last]
        rec = [min(cnt[t] / n, 1) for t in win]
        row = dict(race=b, n=n, frames=len(ts), race_win_frames=len(win),
                   frames_ge80=sum(r >= 0.8 for r in rec), frames_ge50=sum(r >= 0.5 for r in rec),
                   mean_recall=float(np.mean(rec)) if rec else 0, max_det=max(cnt.values()) if cnt else 0,
                   win_s=t_last - t_first)
        # silk distinguishability and silk-matched ordering on side-on frames with decent coverage
        sd = {tab: silk_desc(silk_path(sk, silk_dir)) for tab, _, sk in field if sk}
        row['ord'] = []
        for t in win:
            h, p = dets(d, t)
            if len(h) < max(5, int(0.7 * n)):
                continue
            asp = np.median([(x[2] - x[0]) / max(x[3] - x[1], 1) for x in h])
            if asp < 0.9:  # head-on or tall boxes: running order not readable
                continue
            cands = []
            for x in h:
                jp = jockey_for(x, p)
                if jp is None:
                    continue
                x0, y0, x1, y1 = [int(round(v)) for v in jp[:4]]
                if y1 - y0 < 6 or x1 - x0 < 4:
                    continue
                cands.append((x, jp))
            if len(cands) < 5:
                continue
            row['ord'].append(dict(t=float(t), cands=len(cands), jh=float(np.median([c[1][3] - c[1][1] for c in cands]))))
            cap = cv2.VideoCapture(os.path.join(vid_dir, b + '.mp4'))
            cap.set(cv2.CAP_PROP_POS_MSEC, float(t) * 1000)
            ok, fr = cap.read()
            cap.release()
            if not ok:
                continue
            ds = []
            for x, jp in cands:
                x0, y0, x1, y1 = [max(int(round(v)), 0) for v in jp[:4]]
                ds.append(colour_desc(fr[y0:y1, x0:x1]))
            tabs = [k for k in sd if sd[k] is not None]
            S = np.array([[sim(ds[i], sd[k]) if ds[i] is not None else 0 for k in tabs] for i in range(len(cands))])
            ri, ci = linear_sum_assignment(-S)
            xs = np.array([(cands[i][0][0] + cands[i][0][2]) / 2 for i in ri])
            assigned = [tabs[c] for c in ci]
            if pos is None or len(assigned) < 5:
                continue

            def best_tau(assign):
                best = (-1, None)
                for col in pos.columns:
                    pr = np.array([pos.loc[a, col] if a in pos.index else np.nan for a in assign])
                    ok_ = ~np.isnan(pr)
                    if ok_.sum() < 5:
                        continue
                    tau = abs(kendalltau(xs[ok_], pr[ok_]).statistic)
                    if tau > best[0]:
                        best = (tau, col)
                return best[0]
            obs = best_tau(assigned)
            nulls = [best_tau(list(rng.permutation(assigned))) for _ in range(60)]
            row['ord'][-1].update(tau=obs, null_mean=float(np.mean(nulls)), n_assigned=len(assigned),
                                  p_null_ge=float(np.mean([x >= obs for x in nulls])))
        res.append(row)
        print(b, {k: v for k, v in row.items() if k != 'ord'}, 'ord_frames', len(row['ord']), flush=True)
    json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
