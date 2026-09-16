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
   instead of on faith.

2. own_sustained_finish - fine 200m-interval sectionals (sect_i_400_200,
   sect_i_l200) already exist but closing_merit only uses the single
   sect_i_l600 figure. Candidate: own-history average finishing shape
   (accelerating vs fading through the last 400m), same leak-free
   construction.

3. gear_change_v2 - the existing (unshipped) gear_change term's bucketing
   conflates "Blinkers Off First Time" (REMOVING blinkers) into the same
   generic "other_first_time_gear" bucket as unrelated first-time gear
   additions. Splits it into its own bucket and retests.

METHODOLOGY CHANGE (v2, after v1 failed): speed_map's own inputs
(inside_threats especially) are computed by the CALLER (toprate_daily.py,
using whole-race-field settling_estimate machinery), not reachable
standalone from wpr_projection.py - build_training_frame() alone cannot
replicate them. Switched to calibrate_price_beta.py's _load_resulted()
(the real compute_wpr_projection() entry point, same pattern
wpr_rating_gap_qualitative_screen_test.py already uses post-merge) for a
CORRECT baseline wprp_proj that already includes real speed_map, then
adds each candidate ON TOP of that baseline (same "new term summed onto
an already-correct base+9-terms projection" pattern the ROI candidate
tests used all session), rather than trying to hand-rebuild speed_map.

gear_change_v2 needs its own per-direction leak-free model fit (same
_fit_simple_adj_model/predict pattern gear_change already uses live);
own_trip_upside/own_sustained_finish are precomputed leak-free directly
from wpr_form_history.csv.gz (expanding().shift(1) per horse), no fitting
needed, so they're just added directly.

NO EM DASHES policy: hyphens only.
"""
import json
import numpy as np
import pandas as pd

import wpr_projection as wpr
from calibrate_price_beta import _load_resulted

FORM_CSV = "wpr_form_history.csv.gz"
DAYS_BACK = 90

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
    d = fh[["horse_id", "date", "wpr", "comments_video"]].copy()
    d["wpr"] = pd.to_numeric(d["wpr"], errors="coerce")
    d["date"] = pd.to_datetime(d["date"], errors="coerce")
    d = d.dropna(subset=["horse_id", "date", "wpr"]).sort_values(["horse_id", "date"])
    d["bad_trip"] = d["comments_video"].apply(_is_bad_trip)

    g = d.groupby("horse_id")
    d["all_avg_prior"] = g["wpr"].transform(lambda s: s.shift(1).expanding().mean())

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
    d = fh[["horse_id", "date", "sect_i_400_200", "sect_i_l200"]].copy()
    d["date"] = pd.to_datetime(d["date"], errors="coerce")
    for c in ("sect_i_400_200", "sect_i_l200"):
        d[c] = pd.to_numeric(d[c], errors="coerce")
    d = d.dropna(subset=["horse_id", "date"]).sort_values(["horse_id", "date"])
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


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), len(top1)


def run():
    print(f"Loading resulted races (fresh wprp_proj via compute_wpr_projection, "
          f"{DAYS_BACK} days back)...")
    d = _load_resulted(days_back=DAYS_BACK)
    d = d.dropna(subset=["wprp_proj", "won", "race_id", "date", "horse_id"])
    d["date"] = pd.to_datetime(d["date"])
    print(f"Loaded: {len(d):,} resulted rows, {d['race_id'].nunique():,} races, "
          f"{d['date'].min()} .. {d['date'].max()}")

    print("Reading raw form history for own_trip_upside/own_sustained_finish...")
    fh = pd.read_csv(FORM_CSV, low_memory=False,
                      usecols=["horse_id", "date", "wpr", "comments_video",
                               "sect_i_400_200", "sect_i_l200"])
    trip = build_trip_upside(fh)
    finish = build_sustained_finish(fh)

    d = d.merge(trip, on=["horse_id", "date"], how="left")
    d = d.merge(finish, on=["horse_id", "date"], how="left")
    d["own_trip_upside"] = d["own_trip_upside"].fillna(0.0)
    d["own_sustained_finish"] = d["own_sustained_finish"].fillna(0.0)
    print(f"  own_trip_upside nonzero: {(d['own_trip_upside']!=0).mean()*100:.1f}%")
    print(f"  own_sustained_finish nonzero: {(d['own_sustained_finish']!=0).mean()*100:.1f}%")

    # gear_change_v2 needs the raw gear_changes string + first_up/second_up/
    # n_runs, none of which _load_resulted()'s frame carries (it's a runners_df
    # snapshot, not the per-horse training frame) - pull from a fresh
    # build_training_frame() pass (cheap relative to the _load_resulted cost
    # already paid) purely for these engineered features, merged by (horse_id, date).
    print("Building gear_change_v2 inputs from a training-frame pass...")
    feat = wpr.build_training_frame(FORM_CSV, verbose=False, n_jobs=-1)
    feat["date"] = pd.to_datetime(feat["date"])
    feat["gear_bucket_v2"] = feat["gear_changes"].apply(_gear_change_bucket_v2)
    feat["gear_code_v2"] = feat["gear_bucket_v2"].map(_GEAR_BUCKET_CODE_V2).fillna(0)
    keep = ["horse_id", "date", "gear_code_v2", "field_size", "first_up", "second_up", "n_runs", "career_avg"]
    d = d.merge(feat[keep].drop_duplicates(subset=["horse_id", "date"]), on=["horse_id", "date"], how="left")
    d["target"] = d["wpr"] if "wpr" in d.columns else np.nan
    print(f"  gear_bucket_v2 distribution:\n{d['gear_bucket_v2'].value_counts(dropna=False)}")

    mid = d["date"].quantile(0.5)
    h1, h2 = d[d["date"] < mid].copy(), d[d["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    GEAR_V2_FEATURES = ["gear_code_v2", "field_size", "first_up", "second_up", "n_runs"]

    def fit_gear_v2(fit_half, held_out):
        d2 = fit_half.dropna(subset=GEAR_V2_FEATURES + ["target", "career_avg"])
        model = wpr._fit_simple_adj_model(d2, GEAR_V2_FEATURES, "gear_change_v2")
        for frame in (fit_half, held_out):
            if model is None:
                frame["gear_change_v2"] = 0.0
                continue
            X = frame[GEAR_V2_FEATURES].copy()
            for c in ("field_size", "first_up", "second_up", "n_runs", "gear_code_v2"):
                X[c] = pd.to_numeric(X[c], errors="coerce").fillna(0.0)
            frame["gear_change_v2"] = model.predict(X)
        return model

    results = {}
    for fit_h, held_h, label in [(h1, h2, "H1->H2"), (h2, h1, "H2->H1")]:
        fit_half, held_out = fit_h.copy(), held_h.copy()
        print(f"\n{label}: fitting gear_change_v2...")
        fit_gear_v2(fit_half, held_out)

        baseline_proj = held_out["wprp_proj"].to_numpy()
        # _load_resulted()'s frame has no leak-free point-in-time "target"
        # column the way build_training_frame() does (that's a per-horse
        # training-frame concept) - MAE dropped in favour of top-1 strike
        # rate alone, an established adoption-bar metric used throughout
        # tonight's other candidate tests (e.g. wpr_rejected_candidates_
        # strike_recheck.py), against real race outcomes (won).
        b_strike, b_n = top1_strike_rate(held_out.assign(proj_baseline=baseline_proj), "proj_baseline")
        print(f"  {label} baseline: strike={b_strike:.2f}% (n={b_n})")
        results.setdefault("baseline", []).append((b_strike, b_n))

        for cand in ["own_trip_upside", "own_sustained_finish", "gear_change_v2"]:
            proj = baseline_proj + held_out[cand].fillna(0.0).to_numpy()
            strike, n = top1_strike_rate(held_out.assign(**{f"proj_{cand}": proj}), f"proj_{cand}")
            print(f"  {label} +{cand}: strike={strike:.2f}% (n={n})")
            results.setdefault(cand, []).append((strike, n))

    print("\n" + "=" * 78)
    print("POOLED HELD-OUT ADOPTION-BAR CHECK (top-1 strike rate)")
    print("=" * 78)
    def pooled_strike(rows):
        total_n = sum(r[1] for r in rows)
        total_k = sum(r[0] / 100 * r[1] for r in rows)
        return total_k / total_n * 100 if total_n else float("nan")

    b_strike = pooled_strike(results["baseline"])
    print(f"baseline (current live speed_map-era model): strike={b_strike:.2f}%")
    for cand in ["own_trip_upside", "own_sustained_finish", "gear_change_v2"]:
        c_strike = pooled_strike(results[cand])
        verdict = "IMPROVES strike" if c_strike > b_strike else "worse strike"
        print(f"+{cand:<22s}: strike={c_strike:.2f}% ({verdict}, delta {c_strike-b_strike:+.2f}pts)")


if __name__ == "__main__":
    run()
