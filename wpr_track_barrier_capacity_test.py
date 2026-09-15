"""
wpr_track_barrier_capacity_test.py - tests whether track_barrier's model
just needs more tree capacity to represent real per-track barrier effects.

WHY THIS EXISTS (see chat, Sep 2026): a user question ("do we factor in
horses drawn wide covering extra ground") led to real data digging. Raw
win rate by barrier position, at real venues, showed roughly a THIRD of
tracks with real volume have WIDE barriers doing BETTER than inside (the
opposite of the population-average pattern) - confirmed NOT a confound of
horse quality (controlled for via market-price-rank-implied expected
finish, the "wide is better" pattern held at all 9/9 tracks checked after
deconfounding). But the LIVE track_barrier model predicts "inside is
better" at literally every track tested, including those 9 - several
tracks even produce byte-identical prediction curves (Kalgoorlie ==
Flemington, Goulburn == Grafton), which is not a real per-track pattern,
it's the model folding distinct tracks into the same output.

Root cause found: track_barrier shares _fit_simple_adj_model's generic
hyperparameters (LightGBM, max_depth=3, num_leaves=8, n_estimators=150) -
fine for the OTHER population terms (2-3 continuous features), but
track_code is a ~500-category identity feature here. feature_importances_
showed track_code gets the MOST splits (376, more than distance/barrier/
field_size) but the LEAST total gain (951 vs 2867 for distance) - it's
being split on constantly but each split barely helps, because a depth-3,
8-leaf tree simply cannot carve out a genuine barrier-by-track interaction
for ~500 distinct tracks. This tests a DEEPER variant (more leaves/depth)
against the current shallow one.

THREE CHECKS, leak-free bidirectional half-split (same H1/H2 pattern
every test tonight uses):
  1. Held-out MAE (does deeper track_barrier still generalise, or overfit
     on the extra capacity - this codebase's own adoption bar).
  2. Held-out top-1 strike rate (this session's second adoption metric).
  3. THE DIRECT CHECK: for the specific 16 tracks already identified (9
     where real deconfounded data says wide is better, 7 where it says
     wide is worse), does the DEEPER model's barrier1-vs-barrier12 sweep
     actually reverse sign at the 9 "wide is better" tracks, unlike the
     current shallow model (which predicted "inside better" at ALL 16)?
     This is the most direct test of whether more capacity fixes the
     actual problem, not just a proxy (aggregate MAE could barely move
     even if this specific, important case is fixed or still broken).

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
import lightgbm as lgb

import wpr_projection as wpr
from wpr_own_pace_backtest import add_base, merge_won_by_horse_date

FORM_CSV = "wpr_form_history.csv.gz"

WIDE_BETTER_TRACKS = ["Townsville", "Ballarat", "Wangaratta", "Goulburn", "Port Macquarie",
                      "Cairns", "Grafton", "Bendigo", "Swan Hill"]
WIDE_WORSE_TRACKS = ["Northam", "Kalgoorlie", "Sandown", "Flemington"]  # the 4/7 that held up deconfounded

# current shipped hyperparameters (see _fit_simple_adj_model)
BASELINE_PARAMS = dict(n_estimators=150, max_depth=3, learning_rate=0.05,
                       num_leaves=8, random_state=42, verbosity=-1,
                       objective="quantile", alpha=0.5)
# candidate: enough leaves/depth to let a ~500-category identity feature
# actually interact with barrier, still regularised (learning_rate lower,
# more estimators to compensate) so it doesn't just overfit noise
CANDIDATE_PARAMS = dict(n_estimators=400, max_depth=6, learning_rate=0.03,
                        num_leaves=63, min_child_samples=30, random_state=42,
                        verbosity=-1, objective="quantile", alpha=0.5)


def fit_track_barrier(trn, params):
    track_categories = sorted(trn["track"].dropna().unique())
    track_code_map = {t: i for i, t in enumerate(track_categories)}
    trn = trn.copy()
    trn["track_code"] = trn["track"].map(track_code_map).fillna(-1).astype(int)
    d = trn.dropna(subset=wpr._TRACK_BARRIER_FEATURES + ["target", "career_avg"])
    if len(d) < 200:
        return None, track_code_map
    model = lgb.LGBMRegressor(**params)
    model.fit(d[wpr._TRACK_BARRIER_FEATURES], d["target"] - d["career_avg"])
    return model, track_code_map


def apply_track_barrier(frame, model, track_code_map):
    frame["track_barrier"] = [
        wpr._track_barrier_term(trk, dist, bar, fs, track_code_map, model)
        for trk, dist, bar, fs in zip(frame["track"], frame["cur_distance"],
                                       frame["barrier"], frame["field_size"])
    ]


def top1_strike_rate(frame, proj_col):
    f = frame.copy()
    f["rank"] = f.groupby("race_id")[proj_col].rank(ascending=False, method="first")
    top1 = f[f["rank"] == 1]
    return float(top1["won"].mean() * 100), len(top1)


def proj_of(frame):
    terms = list(wpr.ADJ_TERMS)
    return frame["_base"].to_numpy() + wpr._cap_adj_sum(frame[terms].to_numpy()).sum(axis=1)


def run():
    print("Rebuilding training frame...")
    full = wpr.build_training_frame(FORM_CSV, verbose=True, n_jobs=-1)
    full["date"] = pd.to_datetime(full["date"])
    full = merge_won_by_horse_date(full)
    full = add_base(full)

    non_tb_terms = [t for t in wpr.ADJ_TERMS if t != "track_barrier"]
    full = full.dropna(subset=["target", "_base", "career_avg"] + non_tb_terms +
                        ["barrier", "field_size", "track", "cur_distance", "race_id"])
    print(f"Scoped rows: {len(full):,} ({full['race_id'].nunique():,} races)")

    mid = full["date"].quantile(0.5)
    h1, h2 = full[full["date"] < mid].copy(), full[full["date"] >= mid].copy()
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})")

    results = {"baseline": {"mae": [], "strike_n": [], "strike_k": []},
               "candidate": {"mae": [], "strike_n": [], "strike_k": []}}
    sweep_rows = []

    for fit_h, held_h, label in [(h1, h2, "H1->H2"), (h2, h1, "H2->H1")]:
        fit_half, held_out = fit_h.copy(), held_h.copy()
        for name, params in [("baseline", BASELINE_PARAMS), ("candidate", CANDIDATE_PARAMS)]:
            print(f"\n{label}: fitting {name} track_barrier ({params.get('max_depth')}d/"
                  f"{params.get('num_leaves')}leaves)...")
            model, code_map = fit_track_barrier(fit_half, params)
            ho = held_out.copy()
            apply_track_barrier(ho, model, code_map)
            proj = proj_of(ho)
            mae = float(np.abs(ho["target"].to_numpy() - proj).mean())
            ho["proj"] = proj
            strike, n = top1_strike_rate(ho, "proj")
            k = int(round(strike / 100 * n))
            print(f"  held-out n={len(ho):,}  MAE={mae:.4f}  top1 strike={strike:.2f}% (n={n})")
            results[name]["mae"].append((mae, len(ho)))
            results[name]["strike_n"].append(n)
            results[name]["strike_k"].append(k)

            # direct per-track sweep check
            for trk in WIDE_BETTER_TRACKS + WIDE_WORSE_TRACKS:
                if trk not in code_map:
                    continue
                v1 = wpr._track_barrier_term(trk, 1400, 1, 12, code_map, model)
                v12 = wpr._track_barrier_term(trk, 1400, 12, 12, code_map, model)
                sweep_rows.append({"direction": label, "model": name, "track": trk,
                                   "real_pattern": "wide_better" if trk in WIDE_BETTER_TRACKS else "wide_worse",
                                   "barrier1": v1, "barrier12": v12, "gap_1_minus_12": v1 - v12})

    print("\n" + "=" * 78)
    print("MAE / STRIKE RATE: baseline (current shallow) vs candidate (deeper)")
    print("=" * 78)
    for name in ("baseline", "candidate"):
        total_n = sum(n for _, n in results[name]["mae"])
        pooled_mae = sum(m * n for m, n in results[name]["mae"]) / total_n
        total_k = sum(results[name]["strike_k"])
        total_sn = sum(results[name]["strike_n"])
        print(f"{name:>10s}: pooled held-out MAE={pooled_mae:.4f}   "
              f"top1 strike={total_k/total_sn*100:.2f}% (n={total_sn})")

    print("\n" + "=" * 78)
    print("DIRECT CHECK: per-track barrier1-vs-barrier12 sign, baseline vs candidate")
    print("(real_pattern from deconfounded market-adjusted data, Sep 2026 chat)")
    print("=" * 78)
    sweep = pd.DataFrame(sweep_rows)
    for trk in WIDE_BETTER_TRACKS + WIDE_WORSE_TRACKS:
        d = sweep[sweep["track"] == trk]
        if len(d) == 0:
            continue
        real = d["real_pattern"].iloc[0]
        b_gap = d[d["model"] == "baseline"]["gap_1_minus_12"].mean()
        c_gap = d[d["model"] == "candidate"]["gap_1_minus_12"].mean()
        # gap = barrier1 - barrier12 adjustment. Positive gap = model says inside better.
        # real_pattern "wide_better" means the model SHOULD show a negative gap to match reality.
        expected_sign = -1 if real == "wide_better" else 1
        b_matches = "MATCH" if np.sign(b_gap) == expected_sign else "mismatch"
        c_matches = "MATCH" if np.sign(c_gap) == expected_sign else "mismatch"
        print(f"  {trk:16s} (real: {real:12s}): baseline gap={b_gap:+.2f} [{b_matches}]   "
              f"candidate gap={c_gap:+.2f} [{c_matches}]")


if __name__ == "__main__":
    run()
