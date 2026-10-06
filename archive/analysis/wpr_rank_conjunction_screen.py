"""
wpr_rank_conjunction_screen.py - tests conjunctive RANK-based betting
screens (e.g. "WPR top 3 in field AND sect_i_time top 3 in field AND a
good jockey"), as opposed to wpr_sectional_merit_strike_eval.py's approach
(a continuous-value decile-bucketed ADJ_TERM added to the point
projection). This is the same shape of idea as the existing Signal Watch
feature (frontend/src/lib/signalWatch.ts: edge threshold + price cap +
jockey/trainer win-pct cutoffs) - a runner-level qualifying screen, not a
change to the projection itself.

WHY toprate_runners.csv, NOT build_training_frame()
  build_training_frame() takes ~15-20 min to rebuild (no cache for this
  script) and its own avg_sect_i_time/avg_sect_i_early are per-horse-
  history features computed inside build_features(), same population-
  matching concern the true race-speed calibration fix ran into earlier
  this session: toprate_runners.csv is the REAL served population, and
  is what a live screen would actually run against. So: read jockey_win_
  pct_90d/trainer_win_pct_365d/wpr_nett/wprp_proj/won/finish_position
  straight from toprate_runners.csv (leak-safe already - these are the
  point-in-time values captured when each row was originally fetched,
  not a re-derived history), and compute my own trailing sectional
  average (last 6 prior runs' sect_i_time/sect_i_early, shifted so no
  leakage) directly from wpr_form_history.csv.gz - much lighter than a
  full build_features() call per horse.

METHODOLOGY
  For each candidate rule (a conjunction of rank/threshold conditions),
  find every QUALIFYING RUNNER (not just the race's #1 pick - a race can
  have 0, 1, 2+ qualifiers). Split chronologically into H1/H2 halves and
  report, independently for EACH half: n qualifiers, win strike rate, and
  ROI under the standard proportional-stake convention (stake = round(4/
  price, 2) units, clamped [0.25u, 4u], $50/unit - same as toprate_html_v3.
  py's documented convention, same as wpr_signal_watch_daily_pnl.py used
  earlier this session). A rule is only worth reporting if BOTH halves
  show a real, sample-size-supported edge (same "both directions" bar as
  every ADJ_TERM candidate this session) - a rule that only looks good in
  one half is exactly the multiple-comparisons trap this discipline
  exists to catch.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"
UNIT_DOLLARS = 50
RETURN_UNITS = 4
MIN_STAKE_UNITS = 0.25
MAX_STAKE_UNITS = 4.0


def stake_units(price):
    return np.clip(np.round(RETURN_UNITS / price, 2), MIN_STAKE_UNITS, MAX_STAKE_UNITS)


def load_trailing_sect(form_csv):
    print("Loading form history for trailing sectional averages...")
    fh = pd.read_csv(form_csv, usecols=["horse", "date", "sect_i_time", "sect_i_early"],
                     low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"]).sort_values(["horse_lc", "date"])
    # trailing mean of the last 6 PRIOR runs (shift(1) first so the
    # current row's own value is never included - no leakage)
    g = fh.groupby("horse_lc", sort=False)
    fh["avg_sect_i_time"] = g["sect_i_time"].transform(lambda s: s.shift(1).rolling(6, min_periods=1).mean())
    fh["avg_sect_i_early"] = g["sect_i_early"].transform(lambda s: s.shift(1).rolling(6, min_periods=1).mean())
    return fh[["horse_lc", "date", "avg_sect_i_time", "avg_sect_i_early"]]


def run():
    print("Loading toprate_runners.csv...")
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    resulted = pd.to_numeric(df.get("resulted"), errors="coerce") == 1
    scratched = pd.to_numeric(df.get("scratched"), errors="coerce").fillna(0) == 1
    df = df[resulted & ~scratched].copy()
    df["horse_lc"] = df["horse"].astype(str).str.strip().str.lower()
    print(f"  {len(df):,} resulted, non-scratched runner rows")

    sect = load_trailing_sect(FORM_CSV)
    df = df.merge(sect, on=["horse_lc", "date"], how="left")
    print(f"  sect coverage after merge: {df['avg_sect_i_time'].notna().mean()*100:.1f}%")

    df["won"] = pd.to_numeric(df["won"], errors="coerce").fillna(0).astype(int)
    df["market_price"] = pd.to_numeric(df.get("fixed_win_price"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("starting_price_sp"), errors="coerce")) \
        .combine_first(pd.to_numeric(df.get("price_top"), errors="coerce"))
    df["jockey_win_pct_90d"] = pd.to_numeric(df.get("jockey_win_pct_90d"), errors="coerce")
    df["trainer_win_pct_365d"] = pd.to_numeric(df.get("trainer_win_pct_365d"), errors="coerce")
    df["wpr_nett"] = pd.to_numeric(df.get("wpr_nett"), errors="coerce")

    # within-race ranks (1 = best); NaN signal -> rank goes to the bottom
    df["wpr_rank"] = df.groupby("race_id")["wpr_nett"].rank(ascending=False, method="first")
    df["sect_time_rank"] = df.groupby("race_id")["avg_sect_i_time"].rank(ascending=False, method="first")
    df["sect_early_rank"] = df.groupby("race_id")["avg_sect_i_early"].rank(ascending=False, method="first")

    df = df.sort_values("date").reset_index(drop=True)
    mid = df["date"].quantile(0.5)
    h1 = df[df["date"] < mid]
    h2 = df[df["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    def eval_rule(mask_col_builder, label, min_n=50):
        results = {}
        for name, half in (("H1", h1), ("H2", h2)):
            mask = mask_col_builder(half)
            sub = half[mask & half["market_price"].notna() & (half["market_price"] > 1.0)]
            n = len(sub)
            if n < min_n:
                results[name] = (n, None, None, None)
                continue
            strike = sub["won"].mean() * 100
            units = stake_units(sub["market_price"])
            stake_dollars = units * UNIT_DOLLARS
            payout = np.where(sub["won"] == 1, stake_dollars * sub["market_price"], 0.0)
            pnl = (payout - stake_dollars).sum()
            roi = pnl / stake_dollars.sum() * 100
            results[name] = (n, strike, pnl, roi)
        n1, s1, p1, r1 = results["H1"]
        n2, s2, p2, r2 = results["H2"]
        ok = n1 >= min_n and n2 >= min_n
        both_positive_roi = ok and r1 is not None and r2 is not None and r1 > 0 and r2 > 0
        flag = "  <-- BOTH HALVES POSITIVE ROI" if both_positive_roi else ""
        s1s = f"{s1:.1f}%" if s1 is not None else "n/a"
        s2s = f"{s2:.1f}%" if s2 is not None else "n/a"
        r1s = f"{r1:+.1f}%" if r1 is not None else "n/a"
        r2s = f"{r2:+.1f}%" if r2 is not None else "n/a"
        print(f"{label:<60} H1: n={n1:<5} strike={s1s:<7} ROI={r1s:<8}  "
              f"H2: n={n2:<5} strike={s2s:<7} ROI={r2s:<8}{flag}")
        return both_positive_roi

    print("=== Baseline (no filter) ===")
    eval_rule(lambda h: pd.Series(True, index=h.index), "ALL RUNNERS (baseline)", min_n=1000)
    print()

    print("=== Single-signal rank screens ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["wpr_rank"] <= n, f"WPR rank top-{topn}")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["sect_time_rank"] <= n, f"sect_i_time rank top-{topn}")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["sect_early_rank"] <= n, f"sect_i_early rank top-{topn}")
    print()

    print("=== Conjunctions: WPR top-N AND sect_i_time top-N ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= n) & (h["sect_time_rank"] <= n),
                  f"WPR top-{topn} AND sect_i_time top-{topn}")
    print()

    print("=== Conjunctions: WPR top-3 AND sect_i_time top-3 AND jockey/trainer cutoff ===")
    for jcut in (10, 15, 16.9, 20):
        eval_rule(lambda h, jc=jcut: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3)
                  & (h["jockey_win_pct_90d"] >= jc),
                  f"WPR top-3 AND sect_time top-3 AND jockey>={jcut}%")
    for tcut in (10, 15, 17.3, 20):
        eval_rule(lambda h, tc=tcut: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3)
                  & (h["trainer_win_pct_365d"] >= tc),
                  f"WPR top-3 AND sect_time top-3 AND trainer>={tcut}%")
    print()

    print("=== Jockey/trainer cutoff alone (no rank condition) ===")
    for jcut in (10, 15, 16.9, 20):
        eval_rule(lambda h, jc=jcut: h["jockey_win_pct_90d"] >= jc, f"jockey>={jcut}% alone")
    for tcut in (10, 15, 17.3, 20):
        eval_rule(lambda h, tc=tcut: h["trainer_win_pct_365d"] >= tc, f"trainer>={tcut}% alone")

    print("\nDone.")


if __name__ == "__main__":
    run()
