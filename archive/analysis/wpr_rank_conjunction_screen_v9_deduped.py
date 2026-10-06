"""
wpr_rank_conjunction_screen_v9_deduped.py - re-runs the core rank-
conjunction search from v1-v8 with a critical fix: wpr_form_history.csv.gz
is properly DEDUPLICATED before computing any trailing average from it.

Found live (Sep 2026, while wiring this rule into the dashboard): 42% of
(horse, date) row-pairs in wpr_form_history.csv.gz appear 2-9 times, often
with meaningfully different wpr values for what is the same race (a WPR
rebaseline re-scrape - toprate_daily.py's own form_lookup already dedupes
this the same way for the Race tab's form-history display, but NONE of
v1-v8 did). Left undeduplicated, a trailing ewm5/sect_time average is
computed over noise, not signal - checked directly: deduplicating alone,
with every other part of the methodology held identical, flips the
credible "form top-1 AND jockey/trainer>=15%" tier from +18.0% ROI to
-7.7% ROI on the real last 30 days.

This script does NOT assume the earlier search's conclusions (form beats
WPR/sect_time, jockey/trainer>=15% is the right cutoff, etc still hold -
it re-derives them from scratch on clean data:
  1. each signal alone (WPR rank, sect_i_time rank, ewm5/form rank)
  2. jockey/trainer cutoffs alone
  3. the best-looking combos found last time, re-checked
  4. an ablation on whichever combo looks best here

Same chronological H1/H2 split, same proportional-stake convention, same
both-directions-positive-ROI bar as v1-v8, so results are comparable.

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


def load_trailing_form_deduped(form_csv):
    print("Loading form history for trailing ewm5/sect_i_time (DEDUPLICATED)...")
    fh = pd.read_csv(form_csv, usecols=["horse", "date", "wpr", "sect_i_time", "track", "scrape_date"],
                      low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
    fh = fh.dropna(subset=["date"])
    before = len(fh)
    fh = fh.sort_values("scrape_date", kind="stable")
    fh = fh.drop_duplicates(subset=["horse_lc", "date", "track"], keep="last")
    print(f"  {before:,} rows -> {len(fh):,} after dedup ({(1 - len(fh)/before)*100:.1f}% were duplicates)")
    fh = fh.sort_values(["horse_lc", "date"])
    g = fh.groupby("horse_lc", sort=False)
    fh["ewm5"] = g["wpr"].transform(lambda s: s.shift(1).ewm(span=5).mean())
    fh["avg_sect_i_time"] = g["sect_i_time"].transform(lambda s: s.shift(1).rolling(6, min_periods=1).mean())
    return fh[["horse_lc", "date", "ewm5", "avg_sect_i_time"]]


def run():
    print("Loading toprate_runners.csv...")
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    resulted = pd.to_numeric(df.get("resulted"), errors="coerce") == 1
    scratched = pd.to_numeric(df.get("scratched"), errors="coerce").fillna(0) == 1
    df = df[resulted & ~scratched].copy()
    df["horse_lc"] = df["horse"].astype(str).str.strip().str.lower()
    print(f"  {len(df):,} resulted, non-scratched runner rows")

    form = load_trailing_form_deduped(FORM_CSV)
    df = df.merge(form, on=["horse_lc", "date"], how="left")

    df["won"] = pd.to_numeric(df["won"], errors="coerce").fillna(0).astype(int)
    df["finish_position"] = pd.to_numeric(df.get("finish_position"), errors="coerce")
    df["market_price"] = pd.to_numeric(df.get("fixed_win_price"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("starting_price_sp"), errors="coerce")) \
        .combine_first(pd.to_numeric(df.get("price_top"), errors="coerce"))
    df["jockey_win_pct_90d"] = pd.to_numeric(df.get("jockey_win_pct_90d"), errors="coerce")
    df["trainer_win_pct_365d"] = pd.to_numeric(df.get("trainer_win_pct_365d"), errors="coerce")
    df["wpr_nett"] = pd.to_numeric(df.get("wpr_nett"), errors="coerce")

    df["wpr_rank"] = df.groupby("race_id")["wpr_nett"].rank(ascending=False, method="first")
    df["sect_time_rank"] = df.groupby("race_id")["avg_sect_i_time"].rank(ascending=False, method="first")
    df["form_rank"] = df.groupby("race_id")["ewm5"].rank(ascending=False, method="first")

    df = df.sort_values("date").reset_index(drop=True)
    mid = df["date"].quantile(0.5)
    h1 = df[df["date"] < mid]
    h2 = df[df["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    def eval_rule(mask_col_builder, label, min_n=20):
        results = {}
        for name, half in (("H1", h1), ("H2", h2)):
            mask = mask_col_builder(half)
            sub = half[mask & half["market_price"].notna() & (half["market_price"] > 1.0)]
            n = len(sub)
            if n < min_n:
                results[name] = (n, None, None)
                continue
            strike = sub["won"].mean() * 100
            units = stake_units(sub["market_price"])
            stake_dollars = units * UNIT_DOLLARS
            payout = np.where(sub["won"] == 1, stake_dollars * sub["market_price"], 0.0)
            pnl = (payout - stake_dollars).sum()
            roi = pnl / stake_dollars.sum() * 100
            results[name] = (n, strike, roi)
        n1, s1, r1 = results["H1"]
        n2, s2, r2 = results["H2"]
        ok = n1 >= min_n and n2 >= min_n
        both_positive = ok and r1 is not None and r2 is not None and r1 > 0 and r2 > 0
        flag = "  <-- BOTH HALVES POSITIVE ROI" if both_positive else ""
        s1s = f"{s1:.1f}%" if s1 is not None else "n/a"
        s2s = f"{s2:.1f}%" if s2 is not None else "n/a"
        r1s = f"{r1:+.1f}%" if r1 is not None else "n/a"
        r2s = f"{r2:+.1f}%" if r2 is not None else "n/a"
        print(f"{label:<60} H1: n={n1:<5} strike={s1s:<7} ROI={r1s:<8}  "
              f"H2: n={n2:<5} strike={s2s:<7} ROI={r2s:<8}{flag}")
        return both_positive

    print("=== Each signal ALONE (no jockey/trainer condition) ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["wpr_rank"] <= n, f"WPR rank top-{topn} alone")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["sect_time_rank"] <= n, f"sect_time rank top-{topn} alone")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["form_rank"] <= n, f"form (ewm5) rank top-{topn} alone")
    print()

    print("=== jockey/trainer cutoffs ALONE ===")
    for cut in (10, 15, 20):
        eval_rule(lambda h, c=cut: (h["jockey_win_pct_90d"] >= c) & (h["trainer_win_pct_365d"] >= c),
                  f"jockey/trainer>={cut}% alone")
    print()

    print("=== form rank + jockey/trainer (the previously-reported best combo) ===")
    for cut in (15, 20):
        for topn in (1, 2, 3):
            eval_rule(lambda h, n=topn, c=cut: (h["form_rank"] <= n)
                      & (h["jockey_win_pct_90d"] >= c) & (h["trainer_win_pct_365d"] >= c),
                      f"form top-{topn} AND jockey/trainer>={cut}%")
    print()

    print("=== WPR rank + jockey/trainer ===")
    for cut in (15, 20):
        for topn in (1, 2, 3):
            eval_rule(lambda h, n=topn, c=cut: (h["wpr_rank"] <= n)
                      & (h["jockey_win_pct_90d"] >= c) & (h["trainer_win_pct_365d"] >= c),
                      f"WPR top-{topn} AND jockey/trainer>={cut}%")
    print()

    print("=== sect_time rank + jockey/trainer ===")
    for cut in (15, 20):
        for topn in (1, 2, 3):
            eval_rule(lambda h, n=topn, c=cut: (h["sect_time_rank"] <= n)
                      & (h["jockey_win_pct_90d"] >= c) & (h["trainer_win_pct_365d"] >= c),
                      f"sect_time top-{topn} AND jockey/trainer>={cut}%")
    print()

    print("=== Full combo: WPR + sect_time + form, all top-3, AND jockey/trainer>=15% ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3) & (h["form_rank"] <= 3)
              & (h["jockey_win_pct_90d"] >= 15) & (h["trainer_win_pct_365d"] >= 15),
              "WPR+sect_time+form top-3 AND jockey/trainer>=15%")
    print()

    print("Done.")


if __name__ == "__main__":
    run()
