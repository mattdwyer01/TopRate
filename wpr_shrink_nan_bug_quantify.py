"""
wpr_shrink_nan_bug_quantify.py - how often did the old _shrink() NaN-cap
bug actually fire historically?

BACKGROUND (Sep 2026): wpr_projection.py's _shrink() capped its result via
max(-cap, min(cap, shrunk)). Python's min/max do not propagate NaN
(min(cap, nan) returns cap, not nan), so a NaN delta - a matching-condition
slice that matched >=1 prior run but whose own wpr values were themselves
missing - silently became exactly +cap (the LARGEST possible adjustment)
instead of the intended "unseen -> 0" fallback every other ADJ_TERM miss
uses. Fixed directly in _shrink() (returns 0.0 on a NaN delta now); this
script quantifies how often the old behaviour would have differed.

METHOD: runs the real build_features()/build_training_frame() code path
(not a hand-rolled reimplementation, so every real call site and edge
case is covered exactly as production sees it) with _shrink wrapped to
count NaN-delta-with-n>=1 calls before delegating to the real (fixed)
function. n_jobs=1 (serial) is required for this - build_training_frame's
n_jobs=-1 path forks worker processes, and a plain Python counter's
increments in a forked child never propagate back to the parent, so
counting only works correctly single-process. Serial over the FULL
~18,000-horse history would take too long for a diagnostic, so this runs
on a random sample of horses instead (fixed seed, reproducible) - large
enough for a stable percentage estimate without the full rebuild cost.

NO EM DASHES policy: hyphens only in this file.
"""
import random

import pandas as pd

import wpr_projection as wpr

FORM_CSV = "wpr_form_history.csv.gz"
SAMPLE_HORSES = 3000
SEED = 42
TMP_CSV = "/tmp/wpr_shrink_nan_sample.csv.gz"

NAN_HIT_COUNT = {"n": 0, "total_calls": 0}
_REAL_SHRINK = wpr._shrink


def _counting_shrink(delta, n):
    if n and n > 0:
        NAN_HIT_COUNT["total_calls"] += 1
        d = float(delta) if delta is not None else float("nan")
        if d != d:
            NAN_HIT_COUNT["n"] += 1
    return _REAL_SHRINK(delta, n)


def run():
    print(f"Reading {FORM_CSV}'s horse_id column to sample {SAMPLE_HORSES} horses...")
    ids = pd.read_csv(FORM_CSV, usecols=["horse_id"])["horse_id"].dropna().unique()
    random.seed(SEED)
    sample_ids = set(random.sample(list(ids), min(SAMPLE_HORSES, len(ids))))
    print(f"  {len(ids):,} unique horses total, sampled {len(sample_ids):,}")

    print("Filtering full form history to the sample and writing a temp CSV...")
    fh = pd.read_csv(FORM_CSV, low_memory=False)
    fh = fh[fh["horse_id"].isin(sample_ids)]
    fh.to_csv(TMP_CSV, index=False)
    print(f"  {len(fh):,} rows in the sampled temp file")

    wpr._shrink = _counting_shrink
    try:
        print("\nRebuilding training frame on the sample, serial (n_jobs=1, required for counting)...")
        wpr.build_training_frame(TMP_CSV, verbose=True, n_jobs=1)
    finally:
        wpr._shrink = _REAL_SHRINK

    print(f"\n{'='*70}\nResult\n{'='*70}")
    print(f"_shrink() calls with n>=1 (the only calls that could trigger the bug): "
          f"{NAN_HIT_COUNT['total_calls']:,}")
    pct = NAN_HIT_COUNT["n"] / max(NAN_HIT_COUNT["total_calls"], 1) * 100
    print(f"of those, delta was NaN (old code: silently became +cap; fixed code: 0.0): "
          f"{NAN_HIT_COUNT['n']:,} ({pct:.3f}%)")
    print(f"\nBased on a {len(sample_ids):,}-horse sample (seed={SEED}) of {len(ids):,} total horses -")
    print("treat as an estimate of the historical rate, not an exact population count.")


if __name__ == "__main__":
    run()
