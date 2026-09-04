"""
wpr_rank_conjunction_screen_v2.py - follow-up to wpr_rank_conjunction_
screen.py, testing whether adding "form factor" (ewm5 - recency-weighted
recent form, the OTHER half of the base blend alongside wpr_nett, not
tested in the first pass) improves the rank-conjunction screens found
there.

Computes a lightweight trailing ewm5 (own recent-form average, matching
_compute_base's own ewm5 definition: pandas .ewm(span=5).mean() over the
horse's own prior WPR values, shifted so the current run is never
included) directly from wpr_form_history.csv.gz - same lightweight
approach as the first script's trailing sectional average, avoiding the
15-20 min build_training_frame() rebuild.

Same both-directions-positive-ROI bar, same chronological H1/H2 split,
same proportional-stake convention as wpr_rank_conjunction_screen.py.

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
    print("Loading form history for trailing ewm5 (and sect_i_time)...")
    fh = pd.read_csv(form_csv, usecols=["horse", "date", "wpr", "sect_i_time"], low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
    fh = fh.dropna(subset=["date"]).sort_values(["horse_lc", "date"])

    def _ewm5_shifted(s):
        return s.shift(1).ewm(span=5).mean()

    g = fh.groupby("horse_lc", sort=False)
    fh["ewm5"] = g["wpr"].transform(_ewm5_shifted)
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
    print(f"  ewm5 coverage: {df['ewm5'].notna().mean()*100:.1f}%  "
          f"sect coverage: {df['avg_sect_i_time'].notna().mean()*100:.1f}%")

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
        print(f"{label:<65} H1: n={n1:<5} strike={s1s:<7} ROI={r1s:<8}  "
              f"H2: n={n2:<5} strike={s2s:<7} ROI={r2s:<8}{flag}")
        return both_positive_roi

    print("=== Form factor (ewm5 rank) alone ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["form_rank"] <= n, f"ewm5 (form) rank top-{topn}")
    print()

    print("=== Does form factor improve WPR top-3 AND sect_time top-3 AND jockey>=20%? ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3) & (h["jockey_win_pct_90d"] >= 20),
              "baseline: WPR top-3 AND sect_time top-3 AND jockey>=20% (no form)")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3)
                  & (h["jockey_win_pct_90d"] >= 20) & (h["form_rank"] <= n),
                  f"+ form rank top-{topn}")
    print()

    print("=== Does form factor improve trainer>=20% alone? ===")
    eval_rule(lambda h: h["trainer_win_pct_365d"] >= 20, "baseline: trainer>=20% alone (no form)")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["trainer_win_pct_365d"] >= 20) & (h["form_rank"] <= n),
                  f"trainer>=20% AND form rank top-{topn}")
    print()

    print("=== Form factor swapped IN for sect_time (WPR top-N AND form top-N) ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= n) & (h["form_rank"] <= n),
                  f"WPR top-{topn} AND form top-{topn}")
    print()

    print("=== WPR top-3 AND form top-3 AND jockey>=20% (form instead of sect_time) ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["form_rank"] <= 3) & (h["jockey_win_pct_90d"] >= 20),
              "WPR top-3 AND form top-3 AND jockey>=20%")

    print("\nDone.")


if __name__ == "__main__":
    run()
