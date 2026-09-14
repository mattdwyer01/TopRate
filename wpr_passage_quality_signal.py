"""
wpr_passage_quality_signal.py - user request (Sep 2026): capture which
runners are likely to get a WIDE run (cover extra ground, no cover, extra
work) vs a NICE PASSAGE (saved ground, got cover, economical run), and
test two distinct uses of that signal:

  (1) HISTORICAL TENDENCY: a per-horse shrunk rate of getting a bad
      passage historically, as a candidate ADJ_TERM (same architecture as
      own_first_up/closing_merit - a horse's own history, shrunk by
      sample size, applied forward).
  (2) STRUCTURAL PREDICTION: can TODAY's bad-passage risk be forecast
      pre-race from barrier + field context alone (same per-runner
      cross-fit classifier pattern as wpr_race_speed_leader_prob_model.py)?

PRIOR ART CHECKED FIRST: wpr_void.py already mines comments_video for
trouble markers ("wide throughout", "crowded", "held up", "hampered",
"tightened", "interfere" are already on its WEAK list) but ONLY to void a
run's OWN miss AFTER that same race - never as a forward-looking
predictor, and its wide-run vocabulary is a small subset of what a
frequency scan turns up (see LABEL CONSTRUCTION below). Nothing in this
codebase currently builds a per-horse "gets bad passage" HISTORY feature
or a pre-race STRUCTURAL forecast of it - this is genuinely new ground,
not a re-test of something already tried.

LABEL CONSTRUCTION (data-driven, not guessed): a frequency scan of
comments_video (209,558 non-null rows) found "with cover" (14,927) and
"no cover" (11,851) are the cleanest, most frequent, most literal
passage-quality markers - far cleaner than "wide" alone (87,373 hits,
too generic - includes barrier-width mentions etc). "two wide"/"3 wide"/
"three wide" (35k/35k/69) combined with an ABSENCE of "with cover"/"got
cover" in the same comment is the standard racing-analysis distinction
between "wide but sheltered" (not costly) and "wide and working" (costly)
- a horse wide WITH cover is not penalised, only wide WITHOUT it.
  BAD_PASSAGE  = "no cover" OR (("two wide" OR "3 wide" OR "three wide" OR
                 "wide turn" OR "wide out" OR "wide early") AND NOT
                 ("with cover" OR "got cover"))
  GOOD_PASSAGE = "with cover" OR "got cover" OR "box seat" OR
                 "saved ground" OR "one out one back"
(mutually exclusive in practice - a comment matching both is rare and
excluded from both labels as ambiguous, treated as neutral)

VALIDATION METHOD: does BAD_PASSAGE actually correlate with underperforming
relative to the horse's own recent form (own trailing average WPR of its
last 3 runs, same "residual from own recent history" logic build_features
already uses for e.g. avg_last3), on the SAME run the comment describes?
This has to be true for the label to mean anything before building
anything predictive on top of it. Uses the FULL wpr_form_history.csv.gz
(330k+ rows, not just the ~5-month toprate_runners.csv window) since this
check needs no projection, just the horse's own prior WPR series.

NO EM DASHES policy: hyphens only.
"""
import re
import numpy as np
import pandas as pd

FORM_CSV = "wpr_form_history.csv.gz"

BAD_PHRASES = ["no cover", "two wide", "3 wide", "three wide", "wide turn", "wide out", "wide early"]
GOOD_PHRASES = ["with cover", "got cover", "box seat", "saved ground", "one out one back"]
COVER_PHRASES = ["with cover", "got cover"]


def classify_passage(text):
    if not isinstance(text, str) or not text.strip():
        return None
    t = text.lower()
    has_good = any(p in t for p in GOOD_PHRASES)
    has_cover = any(p in t for p in COVER_PHRASES)
    no_cover = "no cover" in t
    wide_worked = any(p in t for p in ("two wide", "3 wide", "three wide", "wide turn", "wide out", "wide early"))
    is_bad = no_cover or (wide_worked and not has_cover)
    is_good = has_good
    if is_bad and is_good:
        return None  # ambiguous (e.g. "two wide early, got cover in the straight") - exclude
    if is_bad:
        return "bad"
    if is_good:
        return "good"
    return "neutral"


def load_form():
    print("Loading wpr_form_history.csv.gz...")
    fh = pd.read_csv(FORM_CSV, low_memory=False,
                      usecols=["run_id", "horse", "horse_id", "date", "wpr", "comments_video",
                               "barrier", "track", "isBarrierTrial", "raceNumber"])
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    fh = fh.dropna(subset=["horse_lc", "date", "wpr"])
    fh = fh.sort_values(["horse_lc", "date"]).drop_duplicates(subset=["horse_lc", "date"], keep="last")
    print(f"  {len(fh):,} rows after dedup/trial exclusion")
    return fh


def run_part1_validation(fh):
    print("\n" + "=" * 78)
    print("PART 0: label construction + validation")
    print("=" * 78)
    fh["passage"] = fh["comments_video"].apply(classify_passage)
    print(fh["passage"].value_counts(dropna=False))

    # own trailing average of the PRIOR 3 runs (own recent history, no
    # leakage - excludes the run being labelled itself)
    def trailing_avg3(s):
        return s.shift(1).rolling(3, min_periods=2).mean()

    fh["own_avg3"] = fh.groupby("horse_lc")["wpr"].transform(trailing_avg3)
    fh["residual"] = fh["wpr"] - fh["own_avg3"]
    valid = fh.dropna(subset=["residual", "passage"])

    print(f"\nrows with both a passage label and a computable own_avg3 residual: {len(valid):,}")
    g = valid.groupby("passage")["residual"].agg(n="size", mean="mean", median="median", std="std")
    print(g)

    from scipy import stats
    bad = valid[valid["passage"] == "bad"]["residual"]
    good = valid[valid["passage"] == "good"]["residual"]
    neutral = valid[valid["passage"] == "neutral"]["residual"]
    t_bn, p_bn = stats.ttest_ind(bad, neutral, equal_var=False)
    t_gn, p_gn = stats.ttest_ind(good, neutral, equal_var=False)
    print(f"\nbad vs neutral: diff={bad.mean()-neutral.mean():+.2f}  t={t_bn:.2f}  p={p_bn:.4f}")
    print(f"good vs neutral: diff={good.mean()-neutral.mean():+.2f}  t={t_gn:.2f}  p={p_gn:.4f}")
    return fh


if __name__ == "__main__":
    fh = load_form()
    fh = run_part1_validation(fh)
    fh.to_pickle("/tmp/claude-0/-home-user-TopRate/76dfed62-bd31-52ea-bf89-3275bc38fea4/scratchpad/passage_labeled_form.pkl")
    print("\nSaved labeled form history for downstream use.")
