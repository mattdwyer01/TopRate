"""direct_seq.py -- the sequence model (a small GRU over a horse's last 12 runs) used as an input to the direct finishing-position model.

One module for training (research/train_direct_v4.py) and live scoring (direct_score.py), so a past and a future run are turned into the same numbers:
  step_matrix(df)   raw per-run values -> normalised step inputs (rating on the target race's page/ATW scale, margin, finish share, distance, going, days since the
                    run before, weight, class, field size)
  ctx_matrix(df)    today's race: distance, going, weight, field size, barrier fraction
  gru_forward(W, seq, ctx)   the trained network in numpy (weights from torch, saved as direct_model/v4/gru.npz), so the daily job needs no torch
  live_sequences(Lf, classes) the step tensor for log rows (data/direct_log `hist`: the horse's last 12 rated runs, ratings as the runner pages give them)
"""
import numpy as np
import pandas as pd

K = 12
STEP = ['y', 'mfin', 'finpct', 'distance', 'gs', 'gap', 'weightCarried', 'clsn', 'nr']
NS = len(STEP) + 1      # + a 'run present' flag
NC = 5


def step_matrix(df):
    """df columns: y (rating on the target's scale), mfin (beaten margin, 0..30), finpct, distance, gs (going number), gap (days since the run before),
    weightCarried, clsn (class index / number of classes), nr (field size)."""
    X = pd.DataFrame({c: pd.to_numeric(df[c], errors='coerce').astype(float).values for c in STEP})
    X['y'] = (X.y - 70) / 15
    X['mfin'] = X.mfin / 10
    X['distance'] = X.distance / 1000 - 1.5
    X['gs'] = (X.gs - 5) / 3
    X['gap'] = X.gap.fillna(60).clip(0, 400) / 100
    X['weightCarried'] = (X.weightCarried - 57) / 3
    X['nr'] = X.nr / 10
    return X.fillna(0.0).values.astype(np.float32)


def ctx_matrix(df):
    return np.stack([pd.to_numeric(df.distance, errors='coerce').fillna(1400).values / 1000 - 1.5,
                     (pd.to_numeric(df.gs, errors='coerce').fillna(5).values - 5) / 3,
                     (pd.to_numeric(df.weightCarried, errors='coerce').fillna(57).values - 57) / 3,
                     pd.to_numeric(df.nr, errors='coerce').fillna(10).values / 10,
                     pd.to_numeric(df.barfrac, errors='coerce').fillna(0.5).values], 1).astype(np.float32)


def _sig(x):
    return 1 / (1 + np.exp(-x))


def gru_forward(W, seq, ctx):
    """W: dict of numpy arrays saved from torch (g.weight_ih_l0, g.weight_hh_l0, g.bias_ih_l0, g.bias_hh_l0, h.0.weight, h.0.bias, h.2.weight, h.2.bias)."""
    Wih, Whh, bih, bhh = W['g.weight_ih_l0'], W['g.weight_hh_l0'], W['g.bias_ih_l0'], W['g.bias_hh_l0']
    H = Whh.shape[1]
    h = np.zeros((seq.shape[0], H), np.float32)
    for t in range(seq.shape[1]):
        gi = seq[:, t] @ Wih.T + bih
        gh = h @ Whh.T + bhh
        r = _sig(gi[:, :H] + gh[:, :H])
        z = _sig(gi[:, H:2 * H] + gh[:, H:2 * H])
        n = np.tanh(gi[:, 2 * H:] + r * gh[:, 2 * H:])
        h = (1 - z) * n + z * h
    a = np.maximum(np.concatenate([h, ctx], 1) @ W['h.0.weight'].T + W['h.0.bias'], 0)
    return (a @ W['h.2.weight'].T + W['h.2.bias'])[:, 0]


def live_sequences(Lf, classes, class_code):
    """Step tensor (n, K, NS) for log rows. `hist` is oldest first; the most recent run goes in the last slot, as in training."""
    cat = {c: i for i, c in enumerate(classes)}
    recs, owner, slot = [], [], []
    for i, h in enumerate(Lf['hist'].values):
        h = list(h or [])[-K:]
        prev = None
        for j, a in enumerate(h):
            d = pd.Timestamp(a.get('date')) if a.get('date') else None
            gap = (d - prev).days if (d is not None and prev is not None) else np.nan
            prev = d
            st, pos = a.get('starters'), a.get('positionFinish')
            mf = a.get('marginFinish')
            recs.append(dict(y=a.get('wpr'), mfin=min(max(mf, 0), 30) if mf is not None else np.nan,
                             finpct=(pos - 1) / (st - 1) if pos and st and st > 1 else np.nan, distance=a.get('distance'), going=a.get('going'), gap=gap,
                             weightCarried=a.get('weightCarried'), cls=a.get('class'), nr=st))
            owner.append(i)
            slot.append(K - len(h) + j)
    seq = np.zeros((len(Lf), K, NS), np.float32)
    if not recs:
        return seq
    R = pd.DataFrame(recs)
    R['gs'] = pd.to_numeric(R.going.astype(str).str.extract(r'(\d+)')[0], errors='coerce')
    cc = class_code(R['cls'])
    R['clsn'] = np.array([cat.get(c, -1) for c in cc], float) / max(1, len(classes))
    S = step_matrix(R)
    seq[np.array(owner), np.array(slot), :len(STEP)] = S
    seq[np.array(owner), np.array(slot), -1] = 1.0
    return seq
