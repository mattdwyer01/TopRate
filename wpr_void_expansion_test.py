"""
wpr_void_expansion_test.py - validates the marker-list gap found by
wpr_miss_review_v1.py's diagnostic pass.

BACKGROUND: reading the raw comment text behind WPR's biggest currently
"unexplained" misses (wpr_miss.py's own explain_miss() categorization,
already running daily in production) turned up a real, evidence-backed set
of genuine incident/health phrases missing from wpr_void.py's STRONG marker
list - things like "reared", "took no part", "difficult to load",
"fractious in barriers", "struck head on barrier", "stewards queried",
"resented kickback", "failed to handle (the) going", "cardiac", "amiss",
"flatfooted". Every sample checked (see wpr_miss_review_v1.py's output) was a
genuine compromised run, often paired with corroborating language
("vet-clear", "ordered to trial", "stewards enquiry") - no false-positive
risk from negation ("nothing amiss") found in a manual sample check.

wpr_void.STRONG feeds TWO places: wpr_miss.py's daily miss categorization
(cosmetic - just a better label) AND, more importantly,
wpr_projection.py's TRAINING PIPELINE - both the per-horse own-history
discounting inside build_features (_horse_feature_rows, line ~1265) and
train_wpr_projection's own training-target exclusion filter (line ~3083).
Expanding STRONG changes which historical runs the model is trained AGAINST
and trained FROM - a real, if modest, change to training data composition
(a standalone count found ~3,664 additional historical rows, 1.16% of the
full 316k-row deduped history, would newly be excluded - see
wpr_miss_review_v1.py's own_void count).

This script tests whether that expansion actually IMPROVES held-out
projection MAE, using the project's own existing, trusted validation
methodology - it does NOT reimplement the split logic; it calls
train_wpr_projection() itself (the actual production training entry point,
same trn/cf/te 70th/85th-percentile chronological split, same track_barrier/
trainer_merit/jockey_merit/closing_merit fitting, same held-out MAE report)
TWICE - once with wpr_void.STRONG unchanged (baseline), once with it
monkeypatched to include the new markers (candidate) - and compares the
"held-out projection MAE" both print.

Non-destructive: writes model artifacts to scratch out_dir paths, never to
the real wpr_models/ - and restores wpr_void.STRONG to its original value
before exiting either way. wpr_void.py itself is NOT edited by this script;
if the result supports adoption, the STRONG list edit still needs to be made
by hand (or asked for) afterward.

NO EM DASHES policy: hyphens only.
"""
import sys
import time

import wpr_projection as wpr
import wpr_void

NEW_STRONG = [
    "reared", "took no part", "difficult to load", "fractious",
    "struck head", "stewards queried", "stewards query",
    "resented kickback", "failed to handle", "cardiac",
    "amiss", "flatfooted",
]

ORIGINAL_STRONG = list(wpr_void.STRONG)


def run_one(label, out_dir):
    print(f"\n{'=' * 70}\n{label}\nout_dir={out_dir}\n{'=' * 70}")
    t0 = time.time()
    wpr.train_wpr_projection(out_dir=out_dir, n_jobs=-1)
    print(f"{label} done in {time.time() - t0:.0f}s")


def run():
    scratch = "/tmp/claude-0/-home-user-TopRate/37b9fca0-b163-5591-8763-1dcf84252930/scratchpad"
    try:
        print("STRONG marker count: baseline", len(ORIGINAL_STRONG),
              "-> candidate", len(ORIGINAL_STRONG) + len(NEW_STRONG))

        wpr_void.STRONG = list(ORIGINAL_STRONG)
        run_one("BASELINE (current STRONG list, unchanged)",
                f"{scratch}/wpr_models_baseline")

        wpr_void.STRONG = ORIGINAL_STRONG + NEW_STRONG
        run_one("CANDIDATE (STRONG + 11 new incident/health markers)",
                f"{scratch}/wpr_models_candidate")
    finally:
        wpr_void.STRONG = ORIGINAL_STRONG
        print("\nwpr_void.STRONG restored to original (in-process only; "
              "wpr_void.py on disk was never touched).")

    print("\nDone. Compare the two 'held-out projection MAE' lines above.")


if __name__ == "__main__":
    run()
