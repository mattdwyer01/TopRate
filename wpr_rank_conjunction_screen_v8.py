"""
wpr_rank_conjunction_screen_v8.py - adds PLACE (top-3 finish) strike
rate alongside win strike rate, for the rules identified in v7 as the
best-performing (form/ewm5 rank alone, or combined with WPR/sect_time),
each AND jockey_win_pct_90d>=15% AND trainer_win_pct_365d>=15%.

Place strike rate is read directly from finish_position (<=3, and >0 so
a missing/DNF value does not count as a false top-3) - no ROI computed
here (place dividends are not captured in toprate_runners.csv, only win
prices), so this is strike rate only, same chronological H1/H2 split as
v1-v7.

NO EM DASHES policy: hyphens only in this file.
"""
import numpy as np
import pandas as pd

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"


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
    df["finish_position"] = pd.to_numeric(df.get("finish_position"), errors="coerce")
    df["placed"] = ((df["finish_position"] >= 1) & (df["finish_position"] <= 3)).astype(int)
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
    print(f"Baseline (all runners): H1 place%={h1['placed'].mean()*100:.1f}%  "
          f"H2 place%={h2['placed'].mean()*100:.1f}%\n")

    def eval_rule(mask_col_builder, label, min_n=20):
        for name, half in (("H1", h1), ("H2", h2)):
            mask = mask_col_builder(half)
            sub = half[mask & half["market_price"].notna() & (half["market_price"] > 1.0)]
            n = len(sub)
            if n < min_n:
                print(f"  {name}: n={n} (too few)")
                continue
            win_sr = sub["won"].mean() * 100
            place_sr = sub["placed"].mean() * 100
            print(f"  {name}: n={n:<5} win%={win_sr:>5.1f}%  place%={place_sr:>5.1f}%")
        print(f"{label}")
        print()

    JC, TC = 15, 15

    print("=== form (ewm5) rank top-1 AND jockey/trainer>=15% ===")
    eval_rule(lambda h: (h["form_rank"] <= 1) & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "form top-1 AND jockey/trainer>=15%")

    print("=== form (ewm5) rank top-2 AND jockey/trainer>=15% ===")
    eval_rule(lambda h: (h["form_rank"] <= 2) & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "form top-2 AND jockey/trainer>=15%")

    print("=== form (ewm5) rank top-3 AND jockey/trainer>=15% ===")
    eval_rule(lambda h: (h["form_rank"] <= 3) & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "form top-3 AND jockey/trainer>=15%")

    print("=== sect_time + form top-3 AND jockey/trainer>=15% (no WPR) ===")
    eval_rule(lambda h: (h["sect_time_rank"] <= 3) & (h["form_rank"] <= 3)
              & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "sect_time+form top-3 (no WPR)")

    print("=== full combo: WPR + sect_time + form top-3 AND jockey/trainer>=15% ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3) & (h["form_rank"] <= 3)
              & (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "WPR+sect_time+form top-3 (full combo)")

    print("=== jockey/trainer>=15% alone (no rank condition) ===")
    eval_rule(lambda h: (h["jockey_win_pct_90d"] >= JC) & (h["trainer_win_pct_365d"] >= TC),
              "jockey/trainer>=15% alone")

    print("Done.")


if __name__ == "__main__":
    run()
