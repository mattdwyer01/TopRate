"""
wpr_gear_change_strike_eval.py - tests a population-level "gear change"
candidate ADJ_TERM: does a horse wearing new gear TODAY (first-time
blinkers, winkers, tongue tie, etc - a PRE-RACE-KNOWN fact, announced in
the formguide before the race, no leak) predict better- or worse-than-
expected performance?

WHY THIS EXISTS
  The Form Factor Assessment doc explicitly flags gear changes as a
  factor the automated model doesn't see: "Are there any gear changes
  that influence your view on a horse's potential performance?" -
  raw_form_history.csv.gz's gear_changes column (a JSON-list string per
  run, e.g. ["Blinkers First Time"]) has never been used as a feature
  anywhere in wpr_projection.py. Classic racing lore says first-time
  blinkers in particular often sharpens focus and produces improvement -
  worth checking whether that folklore actually holds up in this data.

METHODOLOGY: population-level fitted lookup (same structure as
track_barrier), NOT a per-horse own-history match (gear changes are rare
and mostly a first-time, one-off event per horse - there's no "own
history in this gear" to match against, which is exactly why this has to
be population-level). Buckets: "blinkers_first_time" (specifically
called out in racing lore), "other_first_time_gear" (any other first-time
gear change), "no_change" (baseline). Fit shrunk mean residual
(target - career_avg) per bucket on one chronological half, apply to
both, same as track_barrier/settle_pace. Held-out top-1 strike rate and
MAE, both directions, same adoption bar as every other candidate.

USAGE
  python wpr_gear_change_strike_eval.py

NO EM DASHES policy: hyphens only in this file.
"""
import json

import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, add_track_barrier, merge_won_by_horse_date

FORM_CSV = "wpr_form_history.csv.gz"
_SHRINK_K = 3.0


def add_closing_merit(apply_frames, cutoff_date):
    """Mirrors add_track_barrier's pattern for the OTHER population+own-
    history hybrid ADJ_TERM already in production (see wpr_projection.
    _fit_pace_baseline/_closing_merit_term) - needed here since the
    current 8-term baseline includes closing_merit and this frame must
    match production's proj_of() exactly (same helper as
    wpr_sectional_merit_strike_eval.py's own copy)."""
    lookup = wpr._fit_pace_baseline(FORM_CSV, cutoff_date)
    for frame in apply_frames:
        frame["closing_merit"] = [
            wpr._closing_merit_term(pairs, lookup) for pairs in frame["closing_pairs"]
        ]


def _shrink(delta, n):
    return delta * n / (n + _SHRINK_K)


def _bucket(raw):
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
    if any("First Time" in i for i in items):
        return "other_first_time_gear"
    return "no_change"


def load_gear_buckets():
    # Keyed by (horse_id, date), NOT run_id: run_id is not a per-row race
    # key in the raw form history (see merge_won_by_horse_date's docstring
    # for the full writeup) - a horse's WHOLE scraped form table shares
    # one run_id, so keying by it would collapse gear_changes from many
    # distinct historical rows onto one shared key, each overwriting the
    # last (gear_changes is genuinely per-row, unlike a category lookup).
    fh = pd.read_csv(FORM_CSV, usecols=["horse_id", "date", "gear_changes"], low_memory=False)
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["horse_id", "date"])
    fh["gear_bucket"] = fh["gear_changes"].apply(_bucket)
    print(fh["gear_bucket"].value_counts())
    keys = list(zip(fh["horse_id"], fh["date"]))
    return dict(zip(keys, fh["gear_bucket"]))


def fit_gear_lookup(fit_rows):
    """Population mean residual (target - career_avg) per gear bucket,
    shrunk toward the global mean, fit on fit_rows only."""
    d = fit_rows.dropna(subset=["target", "career_avg", "gear_bucket"])
    resid = d["target"] - d["career_avg"]
    global_mean = resid.mean()
    lookup = {}
    for bucket, g in d.groupby("gear_bucket"):
        n = len(g)
        m = resid.loc[g.index].mean()
        shrunk = (n * m + _SHRINK_K * global_mean) / (n + _SHRINK_K)
        lookup[bucket] = float(shrunk - global_mean)
    return lookup


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), int(top1["won"].sum()), len(top1)


def proj_of(frame, extra_terms):
    terms = list(wpr.ADJ_TERMS) + extra_terms
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print("Loading gear_changes per (horse_id, date)...")
    gear_map = load_gear_buckets()

    print("\nRebuilding training frame (no race_speed_labels needed)...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    keys = pd.Series(list(zip(full["horse_id"], full["date"])), index=full.index)
    full["gear_bucket"] = keys.map(gear_map)

    print("\nMerging race result (won) from toprate_runners.csv by (horse_id, date) - "
          "NOT run_id, which is not a per-row race key (see merge_won_by_horse_date)...")
    full = merge_won_by_horse_date(full)

    full = add_base(full)
    non_tb_terms = [t for t in wpr.ADJ_TERMS if t not in ("track_barrier", "closing_merit")]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance", "gear_bucket"])
    print(f"\nScoped rows: {len(full):,}")
    print(full["gear_bucket"].value_counts())

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"\nH1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    h1_d1, h2_d1 = h1.copy(), h2.copy()
    add_track_barrier(h1_d1, [h1_d1, h2_d1])
    add_closing_merit([h1_d1, h2_d1], h1["date"].max())
    lookup1 = fit_gear_lookup(h1_d1)
    print(f"\ngear lookup (fit on H1): {lookup1}")
    h1_d1["gear_change"] = h1_d1["gear_bucket"].map(lookup1).fillna(0.0)
    h2_d1["gear_change"] = h2_d1["gear_bucket"].map(lookup1).fillna(0.0)

    h1_d2, h2_d2 = h1.copy(), h2.copy()
    add_track_barrier(h2_d2, [h1_d2, h2_d2])
    add_closing_merit([h1_d2, h2_d2], h2["date"].max())
    lookup2 = fit_gear_lookup(h2_d2)
    print(f"gear lookup (fit on H2): {lookup2}")
    h1_d2["gear_change"] = h1_d2["gear_bucket"].map(lookup2).fillna(0.0)
    h2_d2["gear_change"] = h2_d2["gear_bucket"].map(lookup2).fillna(0.0)

    for d in (h1_d1, h2_d1, h1_d2, h2_d2):
        d["proj_base"] = proj_of(d, [])
        d["proj_gear"] = proj_of(d, ["gear_change"])

    print("\n=== H1-fit/H2-validate direction ===")
    b_r1, b_k1, b_n1 = top1_strike_rate(h1_d1, "proj_base")
    b_r2, b_k2, b_n2 = top1_strike_rate(h2_d1, "proj_base")
    c_r1, c_k1, c_n1 = top1_strike_rate(h1_d1, "proj_gear")
    c_r2, c_k2, c_n2 = top1_strike_rate(h2_d1, "proj_gear")
    b_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_base"])
    c_mae2 = mean_absolute_error(h2_d1["target"], h2_d1["proj_gear"])
    print(f"  top-1 strike:  baseline H1={b_k1}/{b_n1}={b_r1:.2f}%  H2(held-out)={b_k2}/{b_n2}={b_r2:.2f}%")
    print(f"  top-1 strike:  +gear_change H1={c_k1}/{c_n1}={c_r1:.2f}%  H2(held-out)={c_k2}/{c_n2}={c_r2:.2f}%")
    print(f"  held-out MAE:  baseline={b_mae2:.4f}  +gear_change={c_mae2:.4f}")

    print("\n=== H2-fit/H1-validate direction ===")
    b_r2b, b_k2b, b_n2b = top1_strike_rate(h2_d2, "proj_base")
    b_r1b, b_k1b, b_n1b = top1_strike_rate(h1_d2, "proj_base")
    c_r2b, c_k2b, c_n2b = top1_strike_rate(h2_d2, "proj_gear")
    c_r1b, c_k1b, c_n1b = top1_strike_rate(h1_d2, "proj_gear")
    b_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_base"])
    c_mae1 = mean_absolute_error(h1_d2["target"], h1_d2["proj_gear"])
    print(f"  top-1 strike:  baseline H2={b_k2b}/{b_n2b}={b_r2b:.2f}%  H1(held-out)={b_k1b}/{b_n1b}={b_r1b:.2f}%")
    print(f"  top-1 strike:  +gear_change H2={c_k2b}/{c_n2b}={c_r2b:.2f}%  H1(held-out)={c_k1b}/{c_n1b}={c_r1b:.2f}%")
    print(f"  held-out MAE:  baseline={b_mae1:.4f}  +gear_change={c_mae1:.4f}")

    strike_improved = (c_r2 > b_r2) and (c_r1b > b_r1b)
    mae_improved = (c_mae2 < b_mae2) and (c_mae1 < b_mae1)
    print(f"\nTop-1 strike rate improved in BOTH held-out directions: {strike_improved} "
          f"(H2: {b_r2:.2f}% -> {c_r2:.2f}%, H1: {b_r1b:.2f}% -> {c_r1b:.2f}%)")
    print(f"Held-out MAE improved in BOTH directions: {mae_improved} "
          f"(H2: {b_mae2:.4f} -> {c_mae2:.4f}, H1: {b_mae1:.4f} -> {c_mae1:.4f})")
    if strike_improved:
        print("\ngear_change clears the strike-rate bar in both directions - a real, "
              "adoptable effect worth a full recalibrated rebuild before shipping.")
    else:
        print("\ngear_change does NOT clear the strike-rate bar in both directions - not "
              "adoptable on this test.")


if __name__ == "__main__":
    run()
