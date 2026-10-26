"""Sky replay feasibility: sample frames and run a COCO Faster R-CNN (horse, person).

usage: python research/sky_replay_detect.py VIDEO OUTJSON [fps] [min_size] [detector]
detector: frcnn (default, torchvision Faster R-CNN) or yolo (ultralytics YOLO11x, 1280 px, 2x2 overlapping tiles plus the full frame)
Writes {frame_t: [[x1,y1,x2,y2,score,cls],...]} (cls 'horse' or 'person').
"""
import json, sys, subprocess, time
import numpy as np, torch
from torchvision.models.detection import fasterrcnn_resnet50_fpn_v2, FasterRCNN_ResNet50_FPN_V2_Weights as W

W_, H_ = 640, 360


def frames(path, fps):
    cmd = ['ffmpeg', '-v', 'error', '-i', path, '-vf', f'fps={fps}', '-f', 'rawvideo', '-pix_fmt', 'rgb24', '-']
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE)
    n = W_ * H_ * 3
    i = 0
    while True:
        b = p.stdout.read(n)
        if len(b) < n:
            break
        yield i / fps, np.frombuffer(b, np.uint8).reshape(H_, W_, 3)
        i += 1


def yolo_boxes(model, fr):
    """Detect person (0) and horse (17) on the full frame and on 2x2 overlapping tiles, merge with NMS."""
    from torchvision.ops import nms
    H, W = fr.shape[:2]
    tiles = [(0, 0, W, H)]
    th, tw = int(H * 0.6), int(W * 0.6)
    for y0 in (0, H - th):
        for x0 in (0, W - tw):
            tiles.append((x0, y0, x0 + tw, y0 + th))
    rows = []
    for x0, y0, x1, y1 in tiles:
        r = model.predict(fr[y0:y1, x0:x1][:, :, ::-1], imgsz=1280, conf=0.15, classes=[0, 17], verbose=False)[0]
        for b, sc, c in zip(r.boxes.xyxy.tolist(), r.boxes.conf.tolist(), r.boxes.cls.tolist()):
            rows.append([b[0] + x0, b[1] + y0, b[2] + x0, b[3] + y0, sc, 'horse' if int(c) == 17 else 'person'])
    out = []
    for cls in ('horse', 'person'):
        rr = [r for r in rows if r[5] == cls]
        if rr:
            keep = nms(torch.tensor([r[:4] for r in rr]), torch.tensor([r[4] for r in rr]), 0.5).tolist()
            out += [[round(v, 1) for v in rr[i][:5]] + [cls] for i in keep]
    return out


def main():
    path, out = sys.argv[1], sys.argv[2]
    fps = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    ms = int(sys.argv[4]) if len(sys.argv) > 4 else 720
    torch.set_num_threads(4)
    detector = sys.argv[5] if len(sys.argv) > 5 else 'frcnn'
    if detector == 'yolo':
        from ultralytics import YOLO
        ym = YOLO('yolo11x.pt')
        res = {}
        t0 = time.time()
        for t, fr in frames(path, fps):
            res[f'{t:.2f}'] = yolo_boxes(ym, fr.copy())
        json.dump(res, open(out, 'w'))
        print(path, 'yolo', len(res), 'frames', round(time.time() - t0), 's')
        return
    m = fasterrcnn_resnet50_fpn_v2(weights=W.DEFAULT, min_size=ms, max_size=ms * 2, box_score_thresh=0.2, box_detections_per_img=60).eval()
    res = {}
    t0 = time.time()
    for t, fr in frames(path, fps):
        x = torch.from_numpy(fr.copy()).permute(2, 0, 1).float() / 255
        with torch.no_grad():
            o = m([x])[0]
        rows = []
        for b, s, l in zip(o['boxes'].tolist(), o['scores'].tolist(), o['labels'].tolist()):
            if l in (1, 19):
                rows.append([round(v, 1) for v in b] + [round(s, 3), 'horse' if l == 19 else 'person'])
        res[f'{t:.2f}'] = rows
    json.dump(res, open(out, 'w'))
    print(path, len(res), 'frames', round(time.time() - t0), 's')


if __name__ == '__main__':
    main()
