"""
wpr_rank_conjunction_screen_v3.py - follow-up correcting a misread: "form
factor" meant the "fm" data point (form_string - the traditional last-4-
finishes racing form figure, e.g. "3-1-7-2", stored directly in
toprate_runners.csv - see toprate_daily.py's own comment "Form string:
last 4 finishing positions, most recent first"), NOT ewm5 (tested in
wpr_rank_conjunction_screen_v2.py, a different, WPR-based recent-form
signal - kept as a separate, valid comparison point below).

FORM FACTOR CONSTRUCTION
  form_string is 4 hyphen-separated tokens, most recent first: a digit
  1-9 (finishing position, 9 = "9th or worse" per the capture code), 'x'
  (unplaced/scratched-equivalent), or '?' (unknown). Turned into a single
  recency-weighted score:
    points(1)=4, points(2)=3, points(3)=2, points(4..9)=1, points('x')=0,
    '?' excluded entirely (neither rewarded nor penalised - missing data,
    not a bad run).
    weight = [4,3,2,1] (most recent run weighted highest).
    form_factor = weighted average of points over only the KNOWN tokens
    (excludes '?'), so a horse with fewer runs shown isn't penalised
    purely for having less history.
  Point-in-time safety: form_string is written once, at the same
  toprate_daily.py new_rows-creation step as jockey_win_pct_90d/
  trainer_win_pct_365d (see the leak-check conversation this session) -
  captured from that horse's OWN prior runs as of race day, never
  touched again for an existing row.

Same chronological H1/H2 split, same proportional-stake convention, same
both-directions-positive-ROI bar as the first two screens.

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

WEIGHTS = [4, 3, 2, 1]


def points(token):
    if token == "x":
        return 0.0
    if token == "?":
        return np.nan
    try:
        p = int(token)
    except (TypeError, ValueError):
        return np.nan
    if p == 1:
        return 4.0
    if p == 2:
        return 3.0
    if p == 3:
        return 2.0
    return 1.0  # 4th-9th ("9" = 9th-or-worse per the capture code)


def form_factor(form_string):
    if not isinstance(form_string, str) or not form_string:
        return np.nan
    tokens = form_string.split("-")
    num, den = 0.0, 0.0
    for w, t in zip(WEIGHTS, tokens):
        p = points(t)
        if p == p:  # not NaN
            num += w * p
            den += w
    return num / den if den > 0 else np.nan


def stake_units(price):
    return np.clip(np.round(RETURN_UNITS / price, 2), MIN_STAKE_UNITS, MAX_STAKE_UNITS)


def load_trailing_sect(form_csv):
    fh = pd.read_csv(form_csv, usecols=["horse", "date", "sect_i_time"], low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.dropna(subset=["date"]).sort_values(["horse_lc", "date"])
    g = fh.groupby("horse_lc", sort=False)
    fh["avg_sect_i_time"] = g["sect_i_time"].transform(lambda s: s.shift(1).rolling(6, min_periods=1).mean())
    return fh[["horse_lc", "date", "avg_sect_i_time"]]


def run():
    print("Loading toprate_runners.csv...")
    df = pd.read_csv(RUNNERS_CSV, dtype={"run_id": str, "race_id": str}, low_memory=False)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    resulted = pd.to_numeric(df.get("resulted"), errors="coerce") == 1
    scratched = pd.to_numeric(df.get("scratched"), errors="coerce").fillna(0) == 1
    df = df[resulted & ~scratched].copy()
    df["horse_lc"] = df["horse"].astype(str).str.strip().str.lower()
    print(f"  {len(df):,} resulted, non-scratched runner rows")

    df["form_factor"] = df["form_string"].apply(form_factor)
    print(f"  form_factor coverage: {df['form_factor'].notna().mean()*100:.1f}%")

    print("Loading form history for trailing sect_i_time (for comparison combos)...")
    sect = load_trailing_sect(FORM_CSV)
    df = df.merge(sect, on=["horse_lc", "date"], how="left")

    df["won"] = pd.to_numeric(df["won"], errors="coerce").fillna(0).astype(int)
    df["market_price"] = pd.to_numeric(df.get("fixed_win_price"), errors="coerce") \
        .combine_first(pd.to_numeric(df.get("starting_price_sp"), errors="coerce")) \
        .combine_first(pd.to_numeric(df.get("price_top"), errors="coerce"))
    df["jockey_win_pct_90d"] = pd.to_numeric(df.get("jockey_win_pct_90d"), errors="coerce")
    df["trainer_win_pct_365d"] = pd.to_numeric(df.get("trainer_win_pct_365d"), errors="coerce")
    df["wpr_nett"] = pd.to_numeric(df.get("wpr_nett"), errors="coerce")

    df["wpr_rank"] = df.groupby("race_id")["wpr_nett"].rank(ascending=False, method="first")
    df["sect_time_rank"] = df.groupby("race_id")["avg_sect_i_time"].rank(ascending=False, method="first")
    df["form_rank"] = df.groupby("race_id")["form_factor"].rank(ascending=False, method="first")

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

    print("=== form_string-derived form_factor alone ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["form_rank"] <= n, f"form_factor rank top-{topn}")
    print()

    print("=== trainer>=20% AND form_factor rank ===")
    eval_rule(lambda h: h["trainer_win_pct_365d"] >= 20, "baseline: trainer>=20% alone")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["trainer_win_pct_365d"] >= 20) & (h["form_rank"] <= n),
                  f"trainer>=20% AND form_factor top-{topn}")
    print()

    print("=== WPR top-3 AND sect_time top-3 AND jockey>=20% AND form_factor ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3) & (h["jockey_win_pct_90d"] >= 20),
              "baseline (no form_factor)")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3)
                  & (h["jockey_win_pct_90d"] >= 20) & (h["form_rank"] <= n),
                  f"+ form_factor top-{topn}")

    print("\nDone.")


if __name__ == "__main__":
    run()
