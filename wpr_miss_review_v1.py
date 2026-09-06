"""
wpr_miss_review_v1.py - diagnostic pass over WPR's real material misses, in
response to "review races in more detail after results to see what happened,
to train a WPR prediction model more accurately."

toprate_daily.py already runs this exact idea in production, every day:
compute_miss_explanations() (see wpr_miss.py's explain_miss()) categorizes
every MATERIAL miss (|actual WPR - projected WPR| >= 4) into ceiling/comment/
untried/price/unexplained, using comments_video/comments_steward (safe here -
read only AFTER the result, purely to diagnose, never as a same-race
predictor) plus structural signals already in toprate_runners.csv.

This script does NOT reinvent that logic - it reads its own output
(wprp_miss_category/wprp_miss_reason, already computed and sitting in
toprate_runners.csv) and asks: of the misses that categorization CANNOT
explain, is there a real, recurring, pre-race-knowable pattern hiding in
there, or is it genuinely unpredictable variance (which would reconfirm
CLAUDE.md's "WPR is at its accuracy ceiling" finding, this time via a
different, qualitative method rather than more numeric feature search).

Four questions, in order:
  1. How big is the unexplained bucket, and how does its miss magnitude
     compare to the explained categories?
  2. Mechanical gap check: wpr_void.py's WEAK markers only void an
     underperformance below -8 WPR points (see WEAK_MISS_THRESHOLD) but
     wpr_miss.py's MATERIAL_THRESHOLD is only 4 - so a moderate
     underperformance (-4 to -8) with a WEAK trouble marker in the comment
     is guaranteed to land in "unexplained" purely by construction, not
     because there's no comment-based signal. Quantify how much of the
     unexplained bucket this mechanical gap accounts for.
  3. Text-pattern scan: for unexplained rows NOT caught by #2, do a keyword
     frequency scan over the raw comment text for phrases not on any
     existing marker list, to see if there's a real, recurring cause the
     current classifier simply has no marker for.
  4. Same-day track/rail bias test: track_barrier (the existing ADJ_TERM) is
     a STATIC, historical, all-time lookup - it has no notion of TODAY's
     rail position moving in/out. Test whether unexplained misses cluster by
     (venue, date) meeting with a same-direction, barrier-correlated pattern
     that a per-meeting, same-day signal could have caught but a historical
     lookup structurally cannot.

NO EM DASHES policy: hyphens only.
"""
import re
import numpy as np
import pandas as pd

pd.set_option("display.width", 140)

RUNNERS_CSV = "toprate_runners.csv"

# wpr_void.py's own marker lists, imported directly (not re-typed) so the
# "gap" comparison in question 2/3 is against the REAL live lists, not a
# stale copy of them.
from wpr_void import STRONG, WEAK, WEAK_MISS_THRESHOLD
from wpr_miss import POSITIVE, MATERIAL_THRESHOLD, _CEILING_MARGIN


def load_runners():
    df = pd.read_csv(RUNNERS_CSV, low_memory=False)
    df = df[(df["resulted"] == 1) & (df["scratched"] != 1)].copy()
    df["wprp_proj"] = pd.to_numeric(df["wprp_proj"], errors="coerce")
    df["wpr_actual"] = pd.to_numeric(df["wpr_actual"], errors="coerce")
    df["miss"] = df["wpr_actual"] - df["wprp_proj"]
    df["barrier"] = pd.to_numeric(df["barrier"], errors="coerce")
    return df


def comment_text(row):
    v = row.get("comments_video")
    s = row.get("comments_steward")
    v = "" if (v is None or (isinstance(v, float) and pd.isna(v))) else str(v)
    s = "" if (s is None or (isinstance(s, float) and pd.isna(s))) else str(s)
    return (v + " " + s).strip()


def markers_hit(text, marker_list):
    t = text.lower()
    return [m for m in marker_list if m in t]


def run():
    df = load_runners()
    print(f"Resulted, non-scratched runner rows: {len(df):,}")
    print(f"Date range: {df['date'].min()} to {df['date'].max()}")

    material = df[df["wprp_miss_category"].notna()].copy()
    print(f"\nMaterial misses (|miss|>={MATERIAL_THRESHOLD:.0f}): "
          f"{len(material):,} ({len(material) / len(df) * 100:.1f}% of resulted runners)")

    print("\n=== Q1: category breakdown ===")
    for cat, grp in material.groupby("wprp_miss_category"):
        print(f"  {cat:12s} n={len(grp):6,}  ({len(grp) / len(material) * 100:5.1f}%)  "
              f"median|miss|={grp['miss'].abs().median():5.2f}  "
              f"mean|miss|={grp['miss'].abs().mean():5.2f}")

    unexplained = material[material["wprp_miss_category"] == "unexplained"].copy()
    understated = unexplained[unexplained["miss"] > 0]   # ran BETTER than projected
    overstated = unexplained[unexplained["miss"] < 0]    # ran WORSE than projected
    print(f"\nUnexplained split: understated(ran better)={len(understated):,}  "
          f"overstated(ran worse)={len(overstated):,}")

    print("\n=== Q2: mechanical WEAK-marker-below-threshold gap ===")
    print(f"(wpr_void's WEAK markers only void an underperformance below "
          f"{WEAK_MISS_THRESHOLD:.0f}; MATERIAL_THRESHOLD is only "
          f"-{MATERIAL_THRESHOLD:.0f}, so a WEAK-marker miss between those two "
          f"cutoffs is guaranteed 'unexplained' by construction)")
    overstated = overstated.assign(text=overstated.apply(comment_text, axis=1))
    overstated = overstated.assign(
        strong_hits=overstated["text"].apply(lambda t: markers_hit(t, STRONG)),
        weak_hits=overstated["text"].apply(lambda t: markers_hit(t, WEAK)),
    )
    has_strong = overstated["strong_hits"].apply(len) > 0
    if has_strong.sum():
        print(f"  NOTE: {has_strong.sum()} 'unexplained' overstated rows actually contain "
              f"a STRONG marker (should not happen if miss<0 - checking is_void's own gate)")
    has_weak_only = (overstated["weak_hits"].apply(len) > 0) & (~has_strong)
    gap_below_threshold = has_weak_only & (overstated["miss"] >= WEAK_MISS_THRESHOLD)
    print(f"  Overstated 'unexplained' rows with a WEAK marker present: {has_weak_only.sum():,} "
          f"of {len(overstated):,} ({has_weak_only.sum() / max(len(overstated),1) * 100:.1f}%)")
    print(f"  ...of those, blocked ONLY by the -8 magnitude gate "
          f"(-8 <= miss < -4, marker present): {gap_below_threshold.sum():,} "
          f"({gap_below_threshold.sum() / max(len(overstated),1) * 100:.1f}% of all overstated-unexplained)")

    remaining_overstated = overstated[~has_weak_only]
    print(f"\n  Overstated 'unexplained' with NO strong/weak marker at all: "
          f"{len(remaining_overstated):,} ({len(remaining_overstated) / max(len(overstated),1) * 100:.1f}%)")

    print("\n=== Q3: keyword scan over remaining unexplained comment text ===")
    print("(overstated rows with no existing marker hit - looking for a recurring")
    print(" phrase the current STRONG/WEAK lists have no entry for)")
    candidate_phrases = [
        "missed the kick", "missed the jump", "slow to begin", "began slowly",
        "no luck", "no room", "short of room", "no clear run", "found the rails",
        "trapped wide", "raced wide", "wide throughout", "gave a lot of ground",
        "went back", "over-raced", "over raced", "hung", "raced greenly",
        "buffeted", "short of a run", "underdone", "found little",
        "no cover", "back class", "on the pace", "faded", "weakened",
        "one paced", "flattened out", "hit the front too soon", "left with too much to do",
        "missed the kick badly", "jumped out awkwardly", "reluctant to begin",
        "raced keenly", "took keenly", "fought rider", "hard to control",
    ]
    text_nonblank = remaining_overstated[remaining_overstated["text"].str.len() > 3]
    print(f"  n with non-blank comment text: {len(text_nonblank):,} of {len(remaining_overstated):,}")
    counts = {}
    for phrase in candidate_phrases:
        n = text_nonblank["text"].str.lower().str.contains(re.escape(phrase), regex=True).sum()
        if n > 0:
            counts[phrase] = n
    for phrase, n in sorted(counts.items(), key=lambda kv: -kv[1]):
        print(f"    '{phrase}': {n}")
    if not counts:
        print("    (none of the candidate phrases matched)")

    # Raw sample of leftover text for manual eyeballing (top 15 by |miss|,
    # i.e. the biggest, most consequential unexplained overstatements).
    print("\n  Sample of the 15 BIGGEST unexplained overstatements (raw comment text):")
    sample = text_nonblank.reindex(text_nonblank["miss"].abs().sort_values(ascending=False).index).head(15)
    for _, r in sample.iterrows():
        print(f"    miss={r['miss']:6.1f}  {r['horse']!s:20.20s}  \"{r['text'][:140]}\"")

    print("\n=== Q4: same-day track/rail bias test ===")
    material["direction"] = np.sign(material["miss"])
    meet = material.dropna(subset=["venue", "date"]).groupby(["venue", "date"])
    rows = []
    for (venue, date), g in meet:
        if len(g) < 6:
            continue
        neg_frac = (g["direction"] < 0).mean()
        rows.append({"venue": venue, "date": date, "n": len(g), "neg_frac": neg_frac})
    meets = pd.DataFrame(rows)
    print(f"  Meetings with >=6 material-miss runners: {len(meets):,}")
    print(f"  Mean fraction overstated (ran worse) per meeting: {meets['neg_frac'].mean():.3f} "
          f"(std {meets['neg_frac'].std():.3f})")
    lopsided = meets[(meets["neg_frac"] >= 0.75) | (meets["neg_frac"] <= 0.25)]
    print(f"  Meetings where >=75% (or <=25%) of material misses go the SAME direction: "
          f"{len(lopsided):,} of {len(meets):,} ({len(lopsided) / len(meets) * 100:.1f}%)")

    # Within lopsided meetings, check barrier correlation: does the
    # OVERSTATED (ran worse) group skew to wider barriers than the
    # UNDERSTATED (ran better) group, on the SAME day/track?
    lopsided_keys = set(zip(lopsided["venue"], lopsided["date"]))
    material["is_lopsided_meet"] = list(zip(material["venue"], material["date"]))
    material["is_lopsided_meet"] = material["is_lopsided_meet"].apply(lambda k: k in lopsided_keys)
    lop = material[material["is_lopsided_meet"] & material["barrier"].notna()]
    if len(lop) > 20:
        over = lop[lop["miss"] < 0]["barrier"]
        under = lop[lop["miss"] > 0]["barrier"]
        print(f"\n  Within lopsided meetings (n={len(lop):,} runners with a barrier):")
        print(f"    mean barrier, overstated/ran-worse group:  {over.mean():.2f} (n={len(over)})")
        print(f"    mean barrier, understated/ran-better group: {under.mean():.2f} (n={len(under)})")
    else:
        print("  Not enough barrier data within lopsided meetings to test.")

    print("\nDone.")


if __name__ == "__main__":
    run()
