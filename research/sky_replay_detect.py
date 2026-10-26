"""Sky replay feasibility: sample frames and run a COCO Faster R-CNN (horse, person).

usage: python research/sky_replay_detect.py VIDEO OUTJSON [fps] [min_size]
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


def main():
    path, out = sys.argv[1], sys.argv[2]
    fps = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    ms = int(sys.argv[4]) if len(sys.argv) > 4 else 720
    torch.set_num_threads(4)
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
