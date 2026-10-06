"""
wpr_settle_barrier_nudge_calibration_test.py - tests whether
settling_estimate.py's barrier_nudge can be materially improved.

WHY THIS EXISTS: settling_estimate.py's own docstring is explicit that its
model is "deliberately simple" - predicted_rel = run_style_tendency +
barrier_nudge, where barrier_nudge's magnitude (BARRIER_MAX_NUDGE = 0.12)
is a HARD-CODED CONSTANT, never fit or validated against real outcomes -
just a guessed "small effect" value. Its own --validate command confirms
real but limited accuracy on today's data: MAE 0.214, band hit rate 38.3%
(vs ~25% random). This directly matters beyond settling_estimate.py itself
- cur_settle_band (which feeds wpr_projection.py's own_settle, the
just-rejected pace_style candidate, and any future work in this vein) IS
this same run_style_tendency + barrier_nudge formula.

RESULT (Sep 2026): REJECTED, both candidates - but informatively so. First
run caught a real bug in this script itself before trusting any number:
the vectorized trailing-mean leaked SAME-DATE duplicate scrape rows into
each other's "prior" window (this session's own documented finding - 42%
of (horse, date) pairs are duplicated from a re-scrape issue - MUST be
deduped before any trailing computation; this script initially skipped
that mandatory step). Caught by verify_against_slow_method() disagreeing
with settling_estimate's own reference implementation; fixed by adding
the standard dedup, re-verified to match exactly (max diff 0.000000).

With that fixed, the real result: the fitted slope (~0.08) is genuinely
different from the hardcoded 0.12 (confirming the constant WAS never
properly calibrated) - but it makes almost no practical difference.
Direction A: baseline MAE 0.2092 -> fitted 0.2093 (worse, +0.0001).
Direction B: baseline MAE 0.2176 -> fitted 0.2174 (better, -0.0001).
Adding the same-day running barrier tally on top changes nothing further
(fitted C coefficient is tiny and flips sign between directions - noise).
Both candidates fail this codebase's bidirectional bar, but the honest
takeaway is sharper than a typical rejection: settling_estimate.py's
simple heuristic was ALREADY close to as good as a properly-fit linear
model gets with the SAME two ingredients (own history + barrier draw).
The ceiling here isn't calibration, it's information - same-day track
bias evidently affects WHO WINS more than it affects WHERE a horse
physically settles in transit (settling position is mostly mechanical:
this horse's own tendency + its immediate barrier), which is a coherent
reason the tally helped WPR's miss-explanation work earlier today but
doesn't help this different question. A materially better running-style
predictor would need a genuinely new input (in-running vision/GPS data,
jockey pre-race intentions, etc.), not a better fit of the two inputs
already used.

TWO CANDIDATES, tested bidirectionally against the current fixed-0.12
baseline:
  1. FITTED nudge magnitude: same linear form (nudge proportional to how
     far off-centre the draw is), but with the slope actually fit via OLS
     against real (actual_rel - run_style_tendency) residuals, instead of
     guessed.
  2. FITTED nudge + a same-day running barrier-bias tally (the ONE
     candidate that survived being made genuinely pre-race-safe in
     wpr_track_bias_running_tally_v1.py earlier today - Inside-drawn
     horses' miss improved monotonically as a running inside-tally, built
     from ONLY races already run earlier that meeting, rose) as a SECOND
     input to the same linear model - does knowing "today's meeting has
     been running to the rail so far" add real information on top of the
     horse's own barrier position alone?

EFFICIENCY NOTE: settling_estimate.py's own --validate does an O(n) filter
of the full history PER TEST ROW (a few minutes for just 2,000 rows - too
slow to run at the scale needed for a real train/test split). This script
computes each horse's trailing run_style_tendency via a vectorized
groupby-cumsum-shift instead (verified against the slow method on a
sample before trusting it at scale).

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from wpr_projection import _barrier_band
import settling_estimate as se

FORM_CSV = "wpr_form_history.csv.gz"


def load_and_prep():
    fh = pd.read_csv(FORM_CSV, dtype={"horse": str, "horse_id": str}, low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    if "isBarrierTrial" in fh.columns:
        fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
    for c in ["positionSettled", "field_size", "barrier", "raceNumber"]:
        fh[c] = pd.to_numeric(fh[c], errors="coerce")

    # MANDATORY dedup (this session's own established finding, re-verified
    # here the hard way): 42% of (horse, date) row-pairs are duplicated (a
    # WPR rebaseline re-scrape issue). BUG FOUND running this script
    # without it: the vectorized trailing-mean's groupby-cumsum-shift
    # leaks SAME-DATE duplicate rows into each other's "prior" window
    # (sort-order neighbours sharing one date each get a nonzero shift
    # position, even though neither is strictly BEFORE the other) -
    # caught by verify_against_slow_method() disagreeing with
    # settling_estimate's own filter (which correctly excludes same-date
    # rows via "date < row_date", not sort position). Deduping first
    # removes the duplicate dates entirely, fixing this at the source
    # rather than patching the symptom.
    n_raw = len(fh)
    fh = fh.sort_values("scrape_date").drop_duplicates(subset=["horse_lc", "date", "track"], keep="last")
    print(f"  dedup: {n_raw:,} -> {len(fh):,} rows")

    since = fh["date"].max() - pd.Timedelta(days=730)
    n_before = len(fh)
    fh = fh[fh["date"] >= since].copy()
    print(f"  bounded to last 2 years ({since.date()} onward): {n_before:,} -> {len(fh):,} rows")
    return fh.sort_values(["horse_lc", "date"]).reset_index(drop=True)


def add_trailing_run_style(fh):
    """Vectorized trailing (strictly prior) mean relative settle per horse -
    same definition as settling_estimate.run_style_tendency, computed via
    groupby-cumsum-shift instead of settling_estimate's own O(n) per-row
    filter (verified to match it on a sample before trusting at scale)."""
    settle = fh["positionSettled"]
    fs = fh["field_size"]
    valid = (settle > 0) & (fs > 0)
    rel = (settle / fs).clip(0, 1)
    rel_valid = rel.where(valid)

    g = fh["horse_lc"]
    csum_incl = rel_valid.fillna(0).groupby(g).cumsum()
    ccount_incl = valid.astype(int).groupby(g).cumsum()
    csum_prior = csum_incl.groupby(g).shift(1)
    ccount_prior = ccount_incl.groupby(g).shift(1)

    fh["run_style_tendency"] = csum_prior / ccount_prior.replace(0, np.nan)
    fh["n_prior_runs"] = ccount_prior.fillna(0)
    fh["actual_rel"] = rel_valid
    return fh


def verify_against_slow_method(fh, n_check=25):
    """Spot-check the vectorized trailing mean against settling_estimate's
    own slow, definitely-correct O(n) method, on a random sample, before
    trusting the fast version at scale."""
    sample = fh[fh["n_prior_runs"] >= 1].sample(n=min(n_check, len(fh)), random_state=42)
    max_diff = 0.0
    for _, row in sample.iterrows():
        prior = fh[(fh["horse_lc"] == row["horse_lc"]) & (fh["date"] < row["date"])]
        slow_tendency, slow_n = se.run_style_tendency(prior)
        fast_tendency = row["run_style_tendency"]
        if slow_tendency is None or pd.isna(fast_tendency):
            continue
        diff = abs(slow_tendency - fast_tendency)
        max_diff = max(max_diff, diff)
    print(f"  verification: max |fast - slow| over {len(sample)} spot-checks = {max_diff:.6f}")
    if max_diff > 1e-6:
        raise RuntimeError("Vectorized trailing mean does not match settling_estimate's own "
                           "slow method - do not trust results until this is fixed.")


def add_running_barrier_tally(fh):
    """Running (pre-race-safe) inside-barrier tally: fraction of WINNERS so
    far today at this (track, date) meeting drawn Inside, using only races
    already run earlier that meeting - the same design
    wpr_track_bias_running_tally_v1.py validated as a real, surviving
    effect (unlike the same-day speed-style version, which did not
    survive being made pre-race-safe).

    "winner" is the WINNING HORSE'S NAME (repeated on every row of that
    race), not a boolean flag - confirmed by inspection before writing
    this (a first draft wrongly compared it to True)."""
    is_winner_row = fh["horse_lc"] == fh["winner"].astype(str).str.strip().str.lower()
    winners = fh[is_winner_row]
    race_meta = (winners.groupby(["track", "date", "raceNumber"])
                        .agg(winner_barrier=("barrier", "first"),
                             field_size=("field_size", "first"))
                        .reset_index())
    race_meta["barrier_band"] = [_barrier_band(b, f) for b, f in
                                 zip(race_meta["winner_barrier"], race_meta["field_size"])]
    race_meta = race_meta.sort_values(["track", "date", "raceNumber"])

    tally = {}
    for (track, date), g in race_meta.groupby(["track", "date"]):
        g = g.sort_values("raceNumber")
        vals = []
        for _, row in g.iterrows():
            key = (row["track"], row["date"], row["raceNumber"])
            n_valid = len([v for v in vals if not pd.isna(v)])
            tally[key] = float(np.mean([v for v in vals if not pd.isna(v)])) if n_valid >= 2 else np.nan
            vals.append(1.0 if row["barrier_band"] == "Inside" else
                       (0.0 if row["barrier_band"] == "Wide" else np.nan))

    fh["_tally_key"] = list(zip(fh["track"], fh["date"], fh["raceNumber"]))
    fh["inside_tally_so_far"] = fh["_tally_key"].map(tally)
    return fh


def fit_ols(X, y):
    """Simple OLS via lstsq, X: (n, k) array (no intercept - residuals are
    already centred by construction, matching barrier_nudge's own centred-
    at-0.5 design), y: (n,) array."""
    coef, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
    return coef


def run():
    print("Loading and preparing form history...")
    fh = load_and_prep()
    fh = add_trailing_run_style(fh)
    verify_against_slow_method(fh)
    fh = add_running_barrier_tally(fh)
    print(f"  inside_tally_so_far coverage: {fh['inside_tally_so_far'].notna().mean()*100:.1f}%")

    fh["draw_frac"] = ((fh["barrier"] - 1) / (fh["field_size"] - 1)).clip(0, 1)
    fh["draw_signal"] = (fh["draw_frac"] - 0.5) * 2
    fh["tally_signal"] = (fh["inside_tally_so_far"] - 0.5) * 2

    usable = fh.dropna(subset=["run_style_tendency", "actual_rel", "draw_signal"]).copy()
    usable["residual"] = usable["actual_rel"] - usable["run_style_tendency"]
    print(f"\nUsable rows (have trailing tendency + actual outcome + barrier): {len(usable):,}")

    def evaluate(trn, te, label):
        # Candidate A: fit draw_signal slope only.
        Xa = trn[["draw_signal"]].to_numpy()
        ya = trn["residual"].to_numpy()
        (b_fit,) = fit_ols(Xa, ya)

        # Candidate B: fit draw_signal + tally_signal jointly (rows lacking
        # a tally just get 0 contribution from that term, same "unseen ->
        # 0" convention as everywhere else in this codebase).
        trn_b = trn.dropna(subset=["tally_signal"])
        Xb = trn_b[["draw_signal", "tally_signal"]].to_numpy()
        yb = trn_b["residual"].to_numpy()
        b_fit2, c_fit = fit_ols(Xb, yb)

        def predict(frame, nudge_fn):
            pred = frame["run_style_tendency"] + frame.apply(nudge_fn, axis=1)
            return pred.clip(0, 1)

        baseline_pred = predict(te, lambda r: r["draw_signal"] * se.BARRIER_MAX_NUDGE)
        a_pred = predict(te, lambda r: r["draw_signal"] * b_fit)
        b_pred = predict(te, lambda r: r["draw_signal"] * b_fit2 +
                         (r["tally_signal"] * c_fit if not pd.isna(r["tally_signal"]) else 0.0))

        mae_base = (baseline_pred - te["actual_rel"]).abs().mean()
        mae_a = (a_pred - te["actual_rel"]).abs().mean()
        mae_b = (b_pred - te["actual_rel"]).abs().mean()
        print(f"  [{label}] n_trn={len(trn):,} n_te={len(te):,} "
              f"fitted_B={b_fit:.4f} (vs hardcoded 0.12)  fitted_B2={b_fit2:.4f} fitted_C={c_fit:.4f}")
        print(f"    baseline (B=0.12) MAE={mae_base:.4f}  "
              f"fitted-B-only MAE={mae_a:.4f} ({'better' if mae_a < mae_base else 'worse'}, {mae_a - mae_base:+.4f})  "
              f"fitted-B+tally MAE={mae_b:.4f} ({'better' if mae_b < mae_base else 'worse'}, {mae_b - mae_base:+.4f})")
        return mae_base, mae_a, mae_b

    q70, q85 = usable["date"].quantile([0.70, 0.85])
    trn_a = usable[usable["date"] < q70]
    te_a = usable[usable["date"] >= q85]
    q30, q15 = usable["date"].quantile([0.30, 0.15])
    trn_b = usable[usable["date"] > q30]
    te_b = usable[usable["date"] <= q15]

    print("\n=== Direction A (forward: oldest 70% trn, newest 15% te) ===")
    res_a = evaluate(trn_a, te_a, "A")
    print("\n=== Direction B (reversed: newest 70% trn, oldest 15% te) ===")
    res_b = evaluate(trn_b, te_b, "B")

    print("\n=== SUMMARY ===")
    labels = ["fitted-B-only", "fitted-B+tally"]
    for i, label in enumerate(labels, start=1):
        da = res_a[i] - res_a[0]
        db = res_b[i] - res_b[0]
        both = da < 0 and db < 0
        print(f"  {label}: direction A {da:+.4f}, direction B {db:+.4f}  "
              f"{'BOTH IMPROVED' if both else 'not both improved'}")

    print("\nDone.")


if __name__ == "__main__":
    run()
