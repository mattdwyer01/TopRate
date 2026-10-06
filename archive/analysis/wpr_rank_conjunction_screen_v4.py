"""
wpr_rank_conjunction_screen_v4.py - follow-up correcting a second misread:
"form factor" meant "pfm" (pfm_score/pfm_score_rank - a separate external
performance score/rank from TopRate's own API, probed 21 Aug 2026 as
pfmScore/pfmScoreRank in get_race_detail), NOT ewm5 (v2) or form_string
(v3).

pfm_score was already tried ONCE this project's history, as part of the
OLD edge-score blend (average of z-scores of wprp_proj + trailing
jockey/trainer form + pfm_score - see wpr_projection.py's compute_edge_
scores docstring) - that blend lost to "WPR's own price ALONE" on ROI at
every threshold tested, so pfm_score was dropped from the edge design
entirely. This is a DIFFERENT test: pfm_score as a rank-conjunction
FILTER condition (same shape as WPR rank / sect_i_time rank), not as a
blended continuous score - never tested this way before.

Coverage is much lower than the other signals (38%, vs 88-96% for
sect_i_time/form_string) - fewer meetings/runners carry a pfm_score at
all, so sample sizes here will be smaller by construction. Own within-
race rank computed via groupby (not trusting pfm_score_rank's own scope,
since its raw values go up to 103 - larger than any real field, so it is
NOT reliably race-scoped as provided).

Same chronological H1/H2 split, same proportional-stake convention, same
both-directions-positive-ROI bar as the first three screens.

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

    df["pfm_score"] = pd.to_numeric(df.get("pfm_score"), errors="coerce")
    print(f"  pfm_score coverage: {df['pfm_score'].notna().mean()*100:.1f}%")

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
    df["pfm_rank"] = df.groupby("race_id")["pfm_score"].rank(ascending=False, method="first")

    df = df.sort_values("date").reset_index(drop=True)
    mid = df["date"].quantile(0.5)
    h1 = df[df["date"] < mid]
    h2 = df[df["date"] >= mid]
    print(f"H1: {len(h1):,} rows (< {mid.date()}), H2: {len(h2):,} rows (>= {mid.date()})\n")

    # pfm_score has ZERO coverage before 2026-07-24 (a newer field) - the
    # global 50/50 H1/H2 split above puts pfm_score entirely in H2, which
    # cannot support a genuine two-direction check. Re-split ONLY the
    # pfm_score-covered rows into their own chronological halves instead.
    pfm_covered = df[df["pfm_score"].notna()]
    pfm_mid = pfm_covered["date"].quantile(0.5)
    pfm_h1 = df[(df["date"] < pfm_mid) & (df["date"] >= pfm_covered["date"].min())]
    pfm_h2 = df[df["date"] >= pfm_mid]
    print(f"pfm-only split: pfm_H1: {len(pfm_h1):,} rows ({pfm_covered['date'].min().date()} to "
          f"{pfm_mid.date()}), pfm_H2: {len(pfm_h2):,} rows (>= {pfm_mid.date()})\n")

    def eval_rule(mask_col_builder, label, min_n=30, halves=None):
        results = {}
        use_h1, use_h2 = halves if halves is not None else (h1, h2)
        for name, half in (("H1", use_h1), ("H2", use_h2)):
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

    pfm_halves = (pfm_h1, pfm_h2)

    print("=== pfm_score rank alone (pfm-only chronological split) ===")
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: h["pfm_rank"] <= n, f"pfm_score rank top-{topn}", halves=pfm_halves)
    print()

    print("=== trainer>=20% AND pfm_score rank (pfm-only split) ===")
    eval_rule(lambda h: h["trainer_win_pct_365d"] >= 20, "baseline: trainer>=20% alone", halves=pfm_halves)
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["trainer_win_pct_365d"] >= 20) & (h["pfm_rank"] <= n),
                  f"trainer>=20% AND pfm_score top-{topn}", halves=pfm_halves)
    print()

    print("=== WPR top-3 AND sect_time top-3 AND jockey>=20% AND pfm_score (pfm-only split) ===")
    eval_rule(lambda h: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3) & (h["jockey_win_pct_90d"] >= 20),
              "baseline (no pfm_score)", halves=pfm_halves)
    for topn in (1, 2, 3):
        eval_rule(lambda h, n=topn: (h["wpr_rank"] <= 3) & (h["sect_time_rank"] <= 3)
                  & (h["jockey_win_pct_90d"] >= 20) & (h["pfm_rank"] <= n),
                  f"+ pfm_score top-{topn}", halves=pfm_halves)

    print("\nDone.")


if __name__ == "__main__":
    run()
