"""
wpr_rank_conjunction_screen_v7.py - ablation test: does the credible
(large-sample) 5-signal combo from v5 (WPR/sect_time/form top-3 AND
jockey>=15% AND trainer>=15%, H1 n=209 +13.9% ROI, H2 n=352 +7.5% ROI)
actually NEED both wpr_nett rank and ewm5 (form) rank, or is one of them
doing all the work and the other just adding complexity for no real gain?

v1 already showed wpr_nett rank is NEGATIVE alone, while ewm5 (form)
rank alone is solidly positive (v2) - so this checks directly whether
dropping wpr_nett from the combo costs anything, at the SAME (15%
cutoff, credible-sample) tier v5 used, not the tiny-sample 20% tier v5's
"drop WPR" section used.

Same chronological H1/H2 split, same proportional-stake convention, same
both-directions-positive-ROI bar as v1-v6.

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


def load_trailing_form(form_csv):
    print("Loading form history for trailing ewm5 and sect_i_time...")
    fh = pd.read_csv(form_csv, usecols=["horse", "date", "wpr", "sect_i_time"], low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
    fh = fh.dropna(subset=["date"]).sort_values(["horse_lc", "date"])
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

    form = load_trailing_form(FORM_CSV)
    df = df.merge(form, on=["horse_lc", "date"], how="left")

    df["won"] = pd.to_numeric(df["won"], errors="coerce").fillna(0).astype(int)
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
        print(f"{label:<65} H1: n={n1:<5} strike={s1s:<7} ROI={r1s:<8}  "
              f"H2: n={n2:<5} strike={s2s:<7} ROI={r2s:<8}{flag}")

    JC, TC = 15, 15  # the credible-tier cutoffs from v5

    print(f"=== Reference: full combo (WPR + sect_time + form, top-3, jockey/trainer>={JC}%) ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3) & (h["form_rank"] <= 3)
              & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "WPR+sect_time+form top-3 (all three ranks)")
    print()

    print("=== Drop WPR rank (keep sect_time + form + jockey + trainer) ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["sect_time_rank"] <= n) & (h["form_rank"] <= n)
                  & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
                  f"sect_time+form top-{topn} (no WPR)")
    print()

    print("=== Drop sect_time rank (keep WPR + form + jockey + trainer) ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= n) & (h["form_rank"] <= n)
                  & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
                  f"WPR+form top-{topn} (no sect_time)")
    print()

    print("=== Drop BOTH WPR and sect_time (form + jockey + trainer only) ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["form_rank"] <= n)
                  & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
                  f"form only top-{topn} (no WPR, no sect_time)")
    print()

    print("=== Drop form rank (keep WPR + sect_time + jockey + trainer) - the reverse ablation ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= n) & (h["sect_time_rank"] <= n)
                  & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
                  f"WPR+sect_time top-{topn} (no form)")

    print("\nDone.")


if __name__ == "__main__":
    run()
