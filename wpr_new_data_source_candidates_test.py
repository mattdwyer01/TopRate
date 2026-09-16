"""
wpr_new_data_source_candidates_test.py - tests 3 candidate ADJ_TERMS built
from data that already exists in wpr_form_history.csv.gz but is currently
UNUSED beyond narrow existing purposes, per CLAUDE.md's own documented
finding ("do not add model complexity without a fundamentally new data
source") and this session's exhaustive, mostly-negative search through
feature engineering on data already summarized elsewhere in the model.

THREE CANDIDATES:

1. own_trip_upside - comments_video (free-text race-day running
   commentary, 61% coverage, currently used ONLY to exclude void runs
   from history) is mined for trip-trouble keywords (checked, held up,
   no clear run, blocked, shuffled, taken back, steadied, trapped, hung
   wide, always wide, 3 wide, too far back, boxed in, no room, no
   galloping room). For each horse, a "trip-corrected" career average is
   built using ONLY prior runs NOT flagged as trip trouble, leak-free
   (expanding, shifted by 1, per horse, chronological). The candidate is
   the shrunk delta: (trip-corrected avg) - (existing career_avg, which
   includes bad-trip runs). Hypothesis: a horse whose bad-trip runs drag
   its average down is being underrated by that average - the classic
   "buy the unlucky horse" idea, now actually testable with real data
   instead of on faith. This is a genuinely new axis of information -
   nothing else in ADJ_TERMS looks at DESCRIBED in-running events, only
   pre-race facts and own-history WPR averages.

2. own_sustained_finish - wpr_form_history.csv.gz has full 200m-interval
   sectionals (sect_i_800_600/600_400/400_200 plus sect_i_l200), not just
   the sect_i_l600 single figure closing_merit already uses. Candidate:
   is this horse's LAST 200m faster or slower than its PRECEDING 200m
   (sect_i_400_200 - sect_i_l200, sign-flipped so positive = accelerating
   through the line, negative = fading/hanging on) - own-history average
   of this per-run "finishing shape" signal, shrunk by n. Tests whether
   knowing HOW a horse finishes (sustained vs one-paced sprint-then-fade)
   carries information closing_merit's single closing figure doesn't.

3. gear_change_v2 - the LIVE (but not currently shipped in ADJ_TERMS)
   gear_change term's own bucketing (_gear_change_bucket in
   wpr_projection.py) conflates "Blinkers Off First Time" (REMOVING
   blinkers - a calming/settling signal) into the same "other_first_time_
   gear" bucket as adding a completely different piece of gear (a nose
   roll, tongue tie, etc - typically an aggression/focus cue) - the
   string match only special-cases "Blinkers First Time" exactly, missing
   that "Blinkers Off First Time" contains "First Time" too and falls
   into the generic bucket. Splits it into its own 4th bucket
   (blinkers_off_first_time) and retests gear_change with this corrected
   bucketing against the same adoption bar gear_change failed under
   before (this session's wpr_adj_term_roi_ablation_test.py already found
   the OLD bucketing failed ROI as a candidate add) - if blinkers-on and
   blinkers-off are genuinely opposite-direction signals being averaged
   together, correcting the conflation might recover real signal the old
   bucketing diluted.

METHODOLOGY: one build_training_frame() call (shared expensive step),
leak-free own-history candidates computed directly from wpr_form_history.
csv.gz (expanding/shift(1) per horse, chronological - point-in-time
correct by construction, no separate model fit needed for candidates 1-2;
candidate 3 reuses gear_change's existing trained-model architecture,
refit on the corrected bucketing), then the SAME leak-free bidirectional
half-split MAE adoption bar used for every other candidate test tonight.

NO EM DASHES policy: hyphens only.
"""
import json
import re
import numpy as np
import pandas as pd

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date

FORM_CSV = "wpr_form_history.csv.gz"

BAD_TRIP_KEYWORDS = [
    "checked", "held up", "no clear run", "no galloping room", "blocked",
    "shuffled", "taken back", "steadied", "trapped", "hung wide",
    "always wide", "3 wide", "three wide", "too far back", "boxed in",
    "no room", "never a clear run", "no galloping",
]


def _is_bad_trip(text):
    if not isinstance(text, str) or len(text) < 5:
        return np.nan
    t = text.lower()
    return float(any(kw in t for kw in BAD_TRIP_KEYWORDS))


def build_trip_upside(fh):
    """Leak-free, per-horse: trip-corrected avg (prior clean-trip runs
    only) minus career_avg-equivalent (all prior runs) - both computed
    with expanding().shift(1), so only strictly-prior runs ever
    contribute to a given row's value."""
    d = fh[["horse_id", "date", "wpr", "comments_video"]].copy()
    d["wpr"] = pd.to_numeric(d["wpr"], errors="coerce")
    d["date"] = pd.to_datetime(d["date"], errors="coerce")
    d = d.dropna(subset=["horse_id", "date", "wpr"]).sort_values(["horse_id", "date"])
    d["bad_trip"] = d["comments_video"].apply(_is_bad_trip)

    g = d.groupby("horse_id")
    d["all_avg_prior"] = g["wpr"].transform(lambda s: s.shift(1).expanding().mean())
    d["all_n_prior"] = g["wpr"].cumcount()

    clean_wpr = d["wpr"].where(d["bad_trip"] == 0.0)
    d["clean_avg_prior"] = clean_wpr.groupby(d["horse_id"]).transform(lambda s: s.shift(1).expanding().mean())
    d["clean_n_prior"] = clean_wpr.notna().groupby(d["horse_id"]).cumsum().groupby(d["horse_id"]).shift(1)

    raw_delta = d["clean_avg_prior"] - d["all_avg_prior"]
    n = d["clean_n_prior"].fillna(0)
    K = 5.0
    shrunk = (raw_delta * n / (n + K)).clip(-wpr._OWN_DELTA_CAP, wpr._OWN_DELTA_CAP)
    d["own_trip_upside"] = shrunk.fillna(0.0)
    return d[["horse_id", "date", "own_trip_upside"]]


def build_sustained_finish(fh):
    """Leak-free, per-horse: own-history average of (sect_i_400_200 minus
    sect_i_l200), sign convention such that a POSITIVE per-run value means
    the horse ran its last 200m FASTER than the 200m before it
    (sustaining/accelerating), negative means it faded. Averaged over
    prior runs only, shrunk by n."""
    d = fh[["horse_id", "date", "sect_i_400_200", "sect_i_l200"]].copy()
    d["date"] = pd.to_datetime(d["date"], errors="coerce")
    for c in ("sect_i_400_200", "sect_i_l200"):
        d[c] = pd.to_numeric(d[c], errors="coerce")
    d = d.dropna(subset=["horse_id", "date"]).sort_values(["horse_id", "date"])
    # sectional times are TIME (lower = faster), so faster last 200m than
    # the one before it means sect_i_l200 < sect_i_400_200 - flip sign so
    # positive = sustained/accelerating, matching the docstring convention.
    d["finish_shape"] = d["sect_i_400_200"] - d["sect_i_l200"]

    g = d.groupby("horse_id")
    d["avg_prior"] = g["finish_shape"].transform(lambda s: s.shift(1).expanding().mean())
    d["n_prior"] = d["finish_shape"].notna().groupby(d["horse_id"]).cumsum().groupby(d["horse_id"]).shift(1)

    n = d["n_prior"].fillna(0)
    K = 5.0
    shrunk = (d["avg_prior"] * n / (n + K)).clip(-wpr._OWN_DELTA_CAP, wpr._OWN_DELTA_CAP)
    d["own_sustained_finish"] = shrunk.fillna(0.0)
    return d[["horse_id", "date", "own_sustained_finish"]]


_GEAR_BUCKET_CODE_V2 = {"no_change": 0, "blinkers_first_time": 1,
                        "blinkers_off_first_time": 2, "other_first_time_gear": 3}


def _gear_change_bucket_v2(raw):
    if not isinstance(raw, str):
        return "no_change"
    try:
        items = json.loads(raw)
    except (json.JSONDecodeError, TypeError):
        return "no_change"
    if not items:
        return "no_change"
    if any("Blinkers First Time" in i for i in items):
        return "blinkers_first_time"
    if any("Blinkers Off First Time" in i for i in items):
        return "blinkers_off_first_time"
    if any("First Time" in i for i in items):
        return "other_first_time_gear"
    return "no_change"


def build_gear_v2(full):
    """gear_code_v2 on the training frame, using the corrected bucketing
    (adds blinkers_off_first_time as its own category, previously
    conflated into other_first_time_gear)."""
    full = full.copy()
    full["gear_bucket_v2"] = full["gear_changes"].apply(_gear_change_bucket_v2)
    full["gear_code_v2"] = full["gear_bucket_v2"].map(_GEAR_BUCKET_CODE_V2).fillna(0)
    return full


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), len(top1)


def proj_of(frame, extra_terms):
    terms = list(wpr.ADJ_TERMS) + extra_terms
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = add_base(full)

    print("Reading raw form history for the 3 new candidates...")
    fh = pd.read_csv(FORM_CSV, low_memory=False,
                      usecols=["horse_id", "date", "wpr", "comments_video",
                               "sect_i_400_200", "sect_i_l200", "gear_changes"])

    print("  building own_trip_upside (comments_video, leak-free expanding)...")
    trip = build_trip_upside(fh)
    print("  building own_sustained_finish (fine sectionals, leak-free expanding)...")
    finish = build_sustained_finish(fh)

    full["date_only"] = full["date"]
    trip["date_only"] = trip["date"]
    finish["date_only"] = finish["date"]
    full = full.merge(trip[["horse_id", "date_only", "own_trip_upside"]],
                       on=["horse_id", "date_only"], how="left")
    full = full.merge(finish[["horse_id", "date_only", "own_sustained_finish"]],
                       on=["horse_id", "date_only"], how="left")
    full["own_trip_upside"] = full["own_trip_upside"].fillna(0.0)
    full["own_sustained_finish"] = full["own_sustained_finish"].fillna(0.0)

    print("  building gear_change_v2 corrected bucketing...")
    full = build_gear_v2(full)

    own_history_terms = ["own_first_up", "own_second_up", "own_long_spell"]
    full = full.dropna(subset=["target", "_base", "career_avg"] + own_history_terms +
                        ["speed_map", "barrier", "field_size", "track", "cur_distance", "race_id"])
    print(f"Scoped rows: {len(full):,} ({full['race_id'].nunique():,} races)")
    print(f"  own_trip_upside nonzero: {(full['own_trip_upside']!=0).mean()*100:.1f}%")
    print(f"  own_sustained_finish nonzero: {(full['own_sustained_finish']!=0).mean()*100:.1f}%")
    print(f"  gear_bucket_v2 distribution:\n{full['gear_bucket_v2'].value_counts()}")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    # gear_change_v2 needs its own trained model per direction (same
    # _fit_simple_adj_model / _merit_term pattern gear_change already
    # uses live, just on the corrected bucket codes)
    GEAR_V2_FEATURES = ["gear_code_v2", "field_size", "first_up", "second_up", "n_runs"]

    def fit_gear_v2(fit_half, held_out):
        d = fit_half.dropna(subset=GEAR_V2_FEATURES + ["target", "career_avg"])
        model = wpr._fit_simple_adj_model(d, GEAR_V2_FEATURES, "gear_change_v2")
        for frame in (fit_half, held_out):
            if model is None:
                frame["gear_change_v2"] = 0.0
                continue
            X = frame[GEAR_V2_FEATURES].copy()
            X["field_size"] = pd.to_numeric(X["field_size"], errors="coerce").fillna(0.0)
            X["n_runs"] = pd.to_numeric(X["n_runs"], errors="coerce").fillna(0.0)
            frame["gear_change_v2"] = model.predict(X)
        return model

    results = {}
    for fit_h, held_h, label in [(h1, h2, "H1->H2"), (h2, h1, "H2->H1")]:
        fit_half, held_out = fit_h.copy(), held_h.copy()
        print(f"\n{label}: fitting gear_change_v2...")
        fit_gear_v2(fit_half, held_out)

        baseline_proj = proj_of(held_out, [])
        baseline_mae = float(np.abs(held_out["target"].to_numpy() - baseline_proj).mean())
        held_out["proj_baseline"] = baseline_proj
        b_strike, b_n = top1_strike_rate(held_out, "proj_baseline")
        print(f"  {label} baseline: MAE={baseline_mae:.4f}  strike={b_strike:.2f}% (n={b_n})")
        results.setdefault("baseline", []).append((baseline_mae, b_strike, b_n, len(held_out)))

        for cand in ["own_trip_upside", "own_sustained_finish", "gear_change_v2"]:
            proj = proj_of(held_out, [cand])
            mae = float(np.abs(held_out["target"].to_numpy() - proj).mean())
            held_out[f"proj_{cand}"] = proj
            strike, n = top1_strike_rate(held_out, f"proj_{cand}")
            print(f"  {label} +{cand}: MAE={mae:.4f}  strike={strike:.2f}% (n={n})")
            results.setdefault(cand, []).append((mae, strike, n, len(held_out)))

    print("\n" + "=" * 78)
    print("POOLED HELD-OUT ADOPTION-BAR CHECK (MAE + top-1 strike rate)")
    print("=" * 78)
    def pooled_mae(rows):
        total_n = sum(r[3] for r in rows)
        return sum(r[0] * r[3] for r in rows) / total_n
    def pooled_strike(rows):
        total_n = sum(r[2] for r in rows)
        total_k = sum(r[1] / 100 * r[2] for r in rows)
        return total_k / total_n * 100 if total_n else float("nan")

    b_mae, b_strike = pooled_mae(results["baseline"]), pooled_strike(results["baseline"])
    print(f"baseline (9 live terms): MAE={b_mae:.4f}  strike={b_strike:.2f}%")
    for cand in ["own_trip_upside", "own_sustained_finish", "gear_change_v2"]:
        c_mae, c_strike = pooled_mae(results[cand]), pooled_strike(results[cand])
        mae_verdict = "IMPROVES MAE" if c_mae < b_mae else "worse MAE"
        strike_verdict = "IMPROVES strike" if c_strike > b_strike else "worse strike"
        print(f"+{cand:<22s}: MAE={c_mae:.4f} ({mae_verdict}, delta {c_mae-b_mae:+.4f})   "
              f"strike={c_strike:.2f}% ({strike_verdict}, delta {c_strike-b_strike:+.2f}pts)")


if __name__ == "__main__":
    run()
