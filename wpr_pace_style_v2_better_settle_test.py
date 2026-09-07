"""
wpr_pace_style_v2_better_settle_test.py - re-tests the pace_style ADJ_TERM
candidate (predicted pace x predicted running style -> a population-level
WPR rating adjustment), which FAILED in wpr_pace_style_adj_term_test.py
(worse held-out MAE in both directions, every K tried).

WHY RE-TEST RATHER THAN ACCEPT THE EARLIER REJECTION: the earlier failure
was attributed to BOTH inputs being too noisy pre-race predictions -
race_speed_estimate.py's pace model (+0.29 held-out correlation, honestly
documented as low-confidence) and cur_settle_band (wpr_projection.py's
OWN internal running-style prediction, a simple run_style_tendency +
barrier_nudge formula, MAE ~0.207-0.215). Since that test, the SETTLE
side was materially improved (settling_estimate.py's Sep 2026 rebuild:
an 8-feature trained model, MAE ~0.197) - but that improved model was
NEVER wired into wpr_projection.py's cur_settle_band (deliberately out of
scope at the time, since nothing downstream was live). This script tests
pace_style AGAIN, using the NEW, better settle-style predictor instead of
the old formula, to see whether the earlier rejection was really about
the architecture being unworkable, or just about feeding it two noisy
inputs when a better one for one side now exists. The PACE side is
UNCHANGED (still race_speed_estimate.py's own +0.29-correlation model) -
this only improves half of the original problem.

DESIGN: identical population-level shrunk lookup to the original
pace_style test (residual = target - career_avg, grouped by predicted
pace label then by predicted settle band, shrunk toward the global mean
per band, centred per pace-label group) - only the SOURCE of the settle
band changes (settling_estimate's trained model instead of
wpr_projection's cur_settle_band formula). Leak-safe: the settle model's
predicted band for any historical row uses ONLY that horse's own PRIOR
history (trailing_* features, all shift(1)-based) - same discipline as
settling_estimate.train() itself, and the same "use an already-validated
model as a fixed input" pattern the original test already used for
race_speed_estimate's pace labels via build_race_speed_labels().

Validated bidirectionally, same K sweep (100/300/600) as the original.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd
from sklearn.metrics import mean_absolute_error

import wpr_projection as wpr
import settling_estimate as se
from wpr_own_pace_backtest import build_race_speed_labels
from wpr_void_expansion_bidirectional_test import fit_track_barrier, fit_pace_baseline_reversed, additive_predict

FORM_CSV = "wpr_form_history.csv.gz"
SETTLE_BANDS = ["Leader", "On-pace", "Midfield", "Back"]
K_VALUES = [100.0, 300.0, 600.0]


def build_settle_band_lookup(since):
    """Predicted settle band for every historical row in the settling
    model's own training window, keyed by (horse_lc, date) - mirrors
    settling_estimate.train()'s exact feature computation (leak-safe,
    all trailing_* via shift(1)), then runs the ALREADY-TRAINED, shipped
    settling model (settling_estimate.MODEL) to predict and band each
    row. Using the already-validated model as a fixed input here is the
    same pattern the original pace_style test used for race_speed_
    estimate's pace labels via build_race_speed_labels()."""
    print("Building predicted-settle-band lookup from the trained settling model...")
    fh = se._load_form()
    fh = fh[fh["date"] >= pd.Timestamp(since)].copy()
    fh = fh.sort_values(["horse_lc", "date"]).reset_index(drop=True)
    print(f"  {len(fh):,} rows in settle-feature window")

    settle = pd.to_numeric(fh["positionSettled"], errors="coerce")
    fh["field_size"] = pd.to_numeric(fh["field_size"], errors="coerce")
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)
    g = fh["horse_lc"]

    csum_incl = rel_valid.fillna(0).groupby(g).cumsum()
    ccount_incl = valid.astype(int).groupby(g).cumsum()
    fh["run_style_tendency"] = (csum_incl.groupby(g).shift(1) /
                                ccount_incl.groupby(g).shift(1).replace(0, np.nan))

    fh["_rel_for_roll"] = rel_valid
    fh["last5_tendency"] = fh.groupby("horse_lc")["_rel_for_roll"].transform(
        lambda s: s.rolling(5, min_periods=1).mean().shift(1))
    fh = fh.drop(columns=["_rel_for_roll"])

    sect_raw = pd.to_numeric(fh["sect_i_early"], errors="coerce")
    sect_clipped = sect_raw.clip(se.SECT_EARLY_LO, se.SECT_EARLY_HI)
    sect_valid = sect_clipped.notna()
    sect_valid_vals = sect_clipped.where(sect_valid)
    sect_csum = sect_valid_vals.fillna(0).groupby(g).cumsum()
    sect_ccount = sect_valid.astype(int).groupby(g).cumsum()
    fh["trailing_sect_i_early"] = (sect_csum.groupby(g).shift(1) /
                                   sect_ccount.groupby(g).shift(1).replace(0, np.nan))

    fh["barrier"] = pd.to_numeric(fh["barrier"], errors="coerce")
    fh["raceNumber"] = pd.to_numeric(fh["raceNumber"], errors="coerce")
    fh["_race_key"] = fh["track"].astype(str) + "|" + fh["date"].astype(str) + "|" + fh["raceNumber"].astype(str)
    fh["sect_rank_in_race"] = fh.groupby("_race_key")["trailing_sect_i_early"].rank(pct=True, na_option="keep")

    for col, out_col, lo, hi in [
        ("sect_ld_early", "trailing_sect_ld_early", se.SECT_LD_EARLY_LO, se.SECT_LD_EARLY_HI),
        ("sect_i_to800", "trailing_sect_i_to800", se.SECT_I_TO800_LO, se.SECT_I_TO800_HI),
        ("margin800m", "trailing_margin800m", se.MARGIN800M_LO, se.MARGIN800M_HI),
    ]:
        raw = pd.to_numeric(fh[col], errors="coerce")
        clipped = raw.clip(lo, hi)
        v = clipped.notna()
        v_vals = clipped.where(v)
        csum = v_vals.fillna(0).groupby(g).cumsum()
        ccount = v.astype(int).groupby(g).cumsum()
        fh[out_col] = csum.groupby(g).shift(1) / ccount.groupby(g).shift(1).replace(0, np.nan)

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    fh["sect_signal"] = (fh["sect_rank_in_race"] - 0.5) * 2

    se._load_model()
    features = se._CFG["features"]
    has_tend = fh["run_style_tendency"].notna()
    print(f"  rows with a usable run_style_tendency: {has_tend.sum():,} / {len(fh):,}")
    med = se._CFG["medians"]
    feat_df = fh[features].apply(lambda col: col.fillna(med.get(col.name, 0.0)))
    pred = se._MODEL.predict(feat_df)
    pred = np.clip(pred, 0.0, 1.0)
    band = pd.Series(pred, index=fh.index).apply(se._band)
    band = band.where(has_tend)

    lookup = {}
    for hlc, date, b in zip(fh["horse_lc"], fh["date"], band):
        if pd.notna(b):
            lookup[(hlc, date)] = b
    print(f"  built lookup for {len(lookup):,} (horse, date) rows")
    return lookup


def fit_pace_style(trn, k):
    resid = trn["target"] - trn["career_avg"]
    frame = pd.DataFrame({
        "pace": trn["cur_race_speed_label"], "band": trn["settle_band"], "residual": resid,
    }).dropna(subset=["pace", "band", "residual"])
    global_by_band = frame.groupby("band")["residual"].mean().to_dict()
    lookup = {}
    for pace_val, g in frame.groupby("pace"):
        stats = g.groupby("band")["residual"].agg(["mean", "count"])
        shrunk = {}
        for b in SETTLE_BANDS:
            if b in stats.index:
                n, m = stats.loc[b, "count"], stats.loc[b, "mean"]
                shrunk[b] = (n * m + k * global_by_band.get(b, 0.0)) / (n + k)
            else:
                shrunk[b] = global_by_band.get(b, 0.0)
        center = float(np.mean(list(shrunk.values())))
        lookup[pace_val] = {
            b: float(max(-wpr._OWN_DELTA_CAP, min(wpr._OWN_DELTA_CAP, shrunk[b] - center))) for b in shrunk
        }
    return lookup


def pace_style_term(pace_val, band_val, lookup):
    if pace_val is None or band_val is None or (isinstance(pace_val, float) and pd.isna(pace_val)):
        return 0.0
    return float(lookup.get(pace_val, {}).get(band_val, 0.0))


def prepare_frame(race_id_to_label, settle_band_lookup):
    print("  building training frame (build_features, with race_speed_labels)...")
    D = wpr.build_training_frame(FORM_CSV, n_jobs=-1, race_speed_labels=race_id_to_label) \
        .dropna(subset=["target", "date"]).sort_values("date")
    print(f"  {len(D):,} training rows")

    D["cur_race_speed_label"] = D["race_id"].map(race_id_to_label)

    _name_map, _tj_lookup = wpr._load_trainer_jockey_by_horse_date(FORM_CSV)
    _tj_dates = D["date"].dt.strftime("%Y-%m-%d")
    _tj_names = D["horse_id"].map(_name_map)
    _tj_vals = [_tj_lookup.get((n, d), (np.nan, np.nan)) for n, d in zip(_tj_names, _tj_dates)]
    D["trainer_win_pct_365d"] = [t for t, j in _tj_vals]
    D["jockey_win_pct_90d"] = [j for t, j in _tj_vals]

    D["horse_lc"] = _tj_names.astype(str).str.lower()
    D["settle_band"] = [settle_band_lookup.get((h, d)) for h, d in zip(D["horse_lc"], D["date"])]
    print(f"  cur_race_speed_label coverage: {D['cur_race_speed_label'].notna().mean()*100:.1f}%")
    print(f"  settle_band (new model) coverage: {D['settle_band'].notna().mean()*100:.1f}%")

    from wpr_void import void_from_comment_only
    cv = D["comments_video"] if "comments_video" in D.columns else None
    cs = D["comments_steward"] if "comments_steward" in D.columns else None
    if cv is not None or cs is not None:
        cv = cv if cv is not None else [None] * len(D)
        cs = cs if cs is not None else [None] * len(D)
        void_mask = [void_from_comment_only(a, b)[0] for a, b in zip(cv, cs)]
        n_void = int(sum(void_mask))
        D = D[[not v for v in void_mask]].copy()
        print(f"  void filter: excluded {n_void:,} compromised runs, {len(D):,} rows remain")

    if "going" in D.columns:
        g_ = D["going"].astype(str).str.strip().str.lower()
        blank_going = D["going"].isna() | g_.isin(["", "nan", "none", "<na>"])
        n_blank = int(blank_going.sum())
        if n_blank:
            D = D[~blank_going].copy()
            print(f"  surface filter: excluded {n_blank:,} blank-going rows, {len(D):,} remain")

    D["_base"] = wpr._BASE_BLEND_ALPHA * D["wpr_nett"] + (1 - wpr._BASE_BLEND_ALPHA) * D["ewm5"]
    D["_base"] = D["_base"].fillna(D["wpr_nett"]).fillna(D["ewm5"]).fillna(D["avg_last3"]).fillna(D["career_avg"])
    D = D.dropna(subset=["_base"]).copy()
    return D


def held_out_mae_both_directions(D, k):
    trainer_edges, trainer_lookup = wpr._fit_merit_lookup(D, "trainer_win_pct_365d")
    jockey_edges, jockey_lookup = wpr._fit_merit_lookup(D, "jockey_win_pct_90d")

    results = {}
    for direction, (trn, te) in [
        ("A: forward (oldest 70% trn, newest 15% te)",
         (D[D["date"] < D["date"].quantile(0.70)],
          D[D["date"] >= D["date"].quantile(0.85)])),
        ("B: reversed (newest 70% trn, oldest 15% te)",
         (D[D["date"] > D["date"].quantile(0.30)],
          D[D["date"] <= D["date"].quantile(0.15)])),
    ]:
        te = te.copy()
        tb_lookup = fit_track_barrier(trn)
        te["track_barrier"] = [
            wpr._track_barrier_term(trk, dist, bar, fs, tb_lookup)
            for trk, dist, bar, fs in zip(te["track"], te["cur_distance"], te["barrier"], te["field_size"])
        ]
        te["trainer_merit"] = [wpr._merit_term(wpr._merit_bucket(v, trainer_edges), trainer_lookup)
                                for v in te["trainer_win_pct_365d"]]
        te["jockey_merit"] = [wpr._merit_term(wpr._merit_bucket(v, jockey_edges), jockey_lookup)
                               for v in te["jockey_win_pct_90d"]]
        cutoff = trn["date"].min() if "reversed" in direction else trn["date"].max()
        pace_lookup_fn = fit_pace_baseline_reversed if "reversed" in direction else \
            (lambda c: wpr._fit_pace_baseline(FORM_CSV, c))
        pb_lookup = pace_lookup_fn(cutoff)
        te["closing_merit"] = [wpr._closing_merit_term(p, pb_lookup) for p in te["closing_pairs"]]

        pace_style_lookup = fit_pace_style(trn, k)
        te["pace_style"] = [
            pace_style_term(pv, bv, pace_style_lookup)
            for pv, bv in zip(te["cur_race_speed_label"], te["settle_band"])
        ]

        scored = te.dropna(subset=["_base"] + wpr.ADJ_TERMS)
        baseline_mae = mean_absolute_error(scored["target"], additive_predict(scored))

        scored2 = scored.copy()
        candidate_terms = wpr.ADJ_TERMS + ["pace_style"]
        cand_pred = scored2["_base"].to_numpy() + wpr._cap_adj_sum(
            scored2[candidate_terms].to_numpy()).sum(axis=1)
        candidate_mae = mean_absolute_error(scored2["target"], cand_pred)

        print(f"  [k={k:.0f}] direction {direction}: n_trn={len(trn):,} n_te={len(scored):,} "
              f"baseline={baseline_mae:.4f} candidate={candidate_mae:.4f} "
              f"({'better' if candidate_mae < baseline_mae else 'worse'}, {candidate_mae - baseline_mae:+.4f})")
        results[direction] = (baseline_mae, candidate_mae)
    return results


def run():
    since = (pd.Timestamp.today() - pd.Timedelta(days=365)).strftime("%Y-%m-%d")
    print("Building leak-safe historical race-speed labels (unchanged from the original test)...")
    race_id_to_label = build_race_speed_labels(since)

    settle_band_lookup = build_settle_band_lookup(since)

    print("\nPreparing training frame...")
    D = prepare_frame(race_id_to_label, settle_band_lookup)

    since_ts = pd.Timestamp(since)
    n_before = len(D)
    D = D[D["date"] >= since_ts].copy()
    print(f"  bounded D to the labeled window ({since} onward): {n_before:,} -> {len(D):,} rows")
    print(f"  cur_race_speed_label coverage within bounded D: {D['cur_race_speed_label'].notna().mean()*100:.1f}%")
    print(f"  settle_band (new model) coverage within bounded D: {D['settle_band'].notna().mean()*100:.1f}%")

    print("\n=== pace_style v2 (better settle predictor): K sweep, both directions ===")
    for k in K_VALUES:
        print(f"\n--- K={k:.0f} ---")
        res = held_out_mae_both_directions(D, k)
        both_better = all(c < b for b, c in res.values())
        print(f"  {'BOTH DIRECTIONS IMPROVED' if both_better else 'not both improved'}")

    print("\nDone.")


if __name__ == "__main__":
    run()
