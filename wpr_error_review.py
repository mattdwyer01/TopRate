"""
wpr_error_review.py - where did the projections go wrong?

A post-mortem over every resulted runner the dashboard has projected. Aggregate
MAE hides failure modes; this finds them by surfacing the worst misses and
grouping the error by condition. Read-only, changes nothing.

WHAT IT REPORTS
  1. Worst individual misses with full context (the tail - usually race-day
     disasters, not fixable model error, shown so they are not mistaken for one).
  2. Mean miss and |error| by venue, going, distance, field size, class - the
     segments the model handles worst.
  3. Confidence calibration - does a low confidence score actually flag the bad
     projections? (Use it as a skip filter if so.)
  4. Race-level scale effect - group residuals by race and compare the
     race-to-race spread against what individual noise alone would produce. A
     larger spread means whole fields move together, a per-race condition the
     model is not capturing. Reports the implied real race-level SD.
  5. Betting outcomes for the model's top projected runner (rank 1): win/place
     rate, mean finish, and where it bombs.
  6. Data-quality flag: resulted runners with finish_position = 0 (likely a
     capture or join gap, not a real finish).

HOW TO READ IT
  Negative bias in a segment = the model OVER-projects there (actual below
  projection). The bush-track / heavy-going / maiden segments over-project most;
  that is a case for a segment-specific calibration rather than one flat offset.
  A segment fix must still beat 60-day walk-forward before shipping.

USAGE
  python wpr_error_review.py
  python wpr_error_review.py --offset 2.57 --worst 15
  python wpr_error_review.py --runners toprate_runners.csv

NO EM DASHES policy: hyphens only.
"""

import sys
import numpy as np
import pandas as pd


def main():
    args = sys.argv
    def opt(flag, default):
        return args[args.index(flag) + 1] if flag in args else default
    runners_csv = opt("--runners", "toprate_runners.csv")
    offset = float(opt("--offset", "2.57"))
    n_worst = int(opt("--worst", "12"))

    d = pd.read_csv(runners_csv, low_memory=False)
    for c, n in [("wprp_proj", "proj"), ("wpr_actual", "act"), ("wprp_conf", "conf"),
                 ("wprp_rank", "prank"), ("finish_position", "fin"),
                 ("starting_price_sp", "sp"), ("distance", "dist")]:
        if c in d.columns:
            d[n] = pd.to_numeric(d[c], errors="coerce")
    d = d.dropna(subset=["proj", "act"]).copy()
    d["resid"] = d["act"] - (d["proj"] + offset)
    d["abserr"] = d["resid"].abs()
    if "race_id" in d.columns:
        d["fsize"] = d.groupby("race_id")["race_id"].transform("size")
    print(f"resulted runners: {len(d):,}   offset {offset:+.2f}   "
          f"mean|err|={d['abserr'].mean():.2f}")

    print(f"\n== {n_worst} worst individual misses (context) ==")
    w = d.reindex(d["abserr"].sort_values(ascending=False).index).head(n_worst)
    for _, r in w.iterrows():
        sp = ("$" + format(r["sp"], ".1f")) if pd.notna(r.get("sp")) else ""
        fin = f"{int(r['fin']):>3}" if pd.notna(r.get("fin")) else "  ?"
        print(f"   {str(r.get('venue',''))[:11]:11s} "
              f"{(str(int(r['dist']))+'m') if pd.notna(r.get('dist')) else '':>6} "
              f"{str(r.get('going',''))[:7]:7s} proj{r['proj']:5.1f} act{r['act']:5.1f} "
              f"miss{r['resid']:+6.1f} conf{(r['conf'] if pd.notna(r.get('conf')) else 0):3.0f} "
              f"{sp:>7} fin{fin}")

    def seg(col, bins=None, top=8, minn=30):
        if col not in d.columns:
            return
        print(f"\n== mean miss + |err| by {col} (n>={minn}) ==")
        grp = d.groupby(pd.cut(d[col], bins) if bins else d[col])
        t = grp.agg(n=("resid", "size"), bias=("resid", "mean"),
                    mae=("abserr", "mean"))
        t = t[t["n"] >= minn].sort_values("mae", ascending=False)
        for k, row in t.head(top).iterrows():
            print(f"   {str(k)[:18]:18s} n={int(row['n']):5d} "
                  f"bias={row['bias']:+5.2f} mae={row['mae']:5.2f}")

    seg("venue")
    seg("going")
    seg("dist", bins=[0, 1100, 1400, 1700, 2100, 4000])
    seg("fsize", bins=[0, 7, 9, 12, 24])
    seg("race_class")

    print("\n== confidence calibration (does high conf mean low error?) ==")
    for lo, hi in [(80, 200), (60, 80), (40, 60), (0, 40)]:
        g = d[(d["conf"] >= lo) & (d["conf"] < hi)] if "conf" in d.columns else d.iloc[0:0]
        if len(g):
            print(f"   conf {lo:3d}-{(hi if hi < 200 else 'max'):<3} n={len(g):5d} "
                  f"mae={g['abserr'].mean():.2f} bias={g['resid'].mean():+.2f}")

    if "race_id" in d.columns:
        rl = d.groupby("race_id").agg(n=("resid", "size"), rbias=("resid", "mean"))
        rl = rl[rl["n"] >= 5]
        if len(rl):
            ind_sd = d["resid"].std()
            avg_n = rl["n"].mean()
            expected = ind_sd / np.sqrt(avg_n)          # race-mean SD from indiv noise alone
            observed = rl["rbias"].std()
            real = np.sqrt(max(observed ** 2 - expected ** 2, 0))
            print(f"\n== race-level scale effect (mean residual per race, n>=5) ==")
            print(f"   races={len(rl)}  observed race-mean SD={observed:.2f}  "
                  f"expected from indiv noise={expected:.2f}")
            print(f"   implied REAL race-level SD={real:.2f}  "
                  f"(whole fields move together by this much)")
            print(f"   entire field >+3 over: {(rl['rbias']>3).mean()*100:.1f}%  |  "
                  f"<-3 under: {(rl['rbias']<-3).mean()*100:.1f}%")

    if "prank" in d.columns and "fin" in d.columns:
        r1 = d[d["prank"] == 1].dropna(subset=["fin"])
        r1 = r1[r1["fin"] > 0]
        if len(r1):
            print(f"\n== model rank-1 (top projected) outcomes, n={len(r1)} ==")
            print(f"   win%={(r1['fin']==1).mean()*100:.1f}  "
                  f"place%(<=3)={(r1['fin']<=3).mean()*100:.1f}  "
                  f"mean fin={r1['fin'].mean():.2f}  "
                  f"bombs(fin>=6)={(r1['fin']>=6).mean()*100:.1f}%")

    if "fin" in d.columns:
        z = d[d["fin"].isna() | (d["fin"] == 0)]
        print(f"\n== data-quality flag ==")
        print(f"   resulted runners with missing/zero finish_position: {len(z)} "
              f"({len(z)/len(d)*100:.1f}%) - check result ingest for these")
        if len(z) and "venue" in z.columns:
            vm = z.groupby("venue").size().sort_values(ascending=False).head(5)
            print("   top venues affected:", dict(vm))

    # Void-aware decontamination. Once comments are captured (comments_video /
    # comments_steward columns), exclude compromised runs and show how much
    # the error stats improve. Uses the shared wpr_void direction rule.
    if "comments_video" in d.columns or "comments_steward" in d.columns:
        try:
            from wpr_void import is_void
            cv = d["comments_video"] if "comments_video" in d.columns else None
            cs = d["comments_steward"] if "comments_steward" in d.columns else None
            cv = cv if cv is not None else pd.Series([None] * len(d), index=d.index)
            cs = cs if cs is not None else pd.Series([None] * len(d), index=d.index)
            void = pd.Series(
                [is_void(m, a, b)[0] for m, a, b in zip(d["resid"], cv, cs)],
                index=d.index)
            n_void = int(void.sum())
            print(f"\n== void-aware decontamination ==")
            if n_void:
                keep = d[~void]
                allm = d["resid"]
                km = keep["resid"]
                print(f"   all resulted:    n={len(d):5d} mean miss {allm.mean():+.2f} MAE {allm.abs().mean():.2f}")
                print(f"   excluding {n_void} voids: n={len(keep):5d} mean miss {km.mean():+.2f} MAE {km.abs().mean():.2f}")
                print("   (voids = vet/eased/checked/etc on underperformances - not model error)")
            else:
                print("   no void runs flagged (comments may not be captured yet)")
        except ImportError:
            pass


if __name__ == "__main__":
    main()
