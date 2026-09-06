"""
wpr_track_bias_pace_review_v1.py - post-meeting review of sectionals and
in-running positions, in direct response to: "review sectionals & in-run
positions following a meeting to determine if there was any track bias on
the day, or if there was pace impacts on races which explain why certain
horses ran a certain WPR."

This is a sharper, more direct version of wpr_miss_review_v1.py's Q4 (which
only used overall miss DIRECTION + mean barrier as an indirect proxy for
track bias, and came back weak/inconclusive). This version uses the REAL
in-running data instead of a proxy:

  - toprate_runners.csv's "_settling" column: the ACTUAL settling position
    band (leader/on-pace/midfield/backmarker) for THAT specific run - not a
    prediction, not the horse's own trailing history, the real thing that
    happened, already captured live.
  - wpr_form_history.csv.gz's "raceShapeEarly"/"raceShapeMid"/"raceShapeLate":
    the REAL, POST-race early/mid/late tempo numbers race_speed_estimate.py
    tries (with only +0.27 held-out correlation - a modest, low-confidence
    PRE-race estimate) to predict. Using the real values here is legitimate
    for DIAGNOSIS (explaining what already happened) even though they can
    never be used as a live PRE-race feature (leak-unsafe by definition -
    the race hasn't been run yet at serving time).

PART A - TRACK BIAS BY MEETING
  For every (venue, date) meeting, compare the ACTUAL win/place rate by
  settling band (and by barrier band, via wpr_projection.py's own
  _barrier_band()) against the GLOBAL population base rate for that band.
  A meeting where front-runners win far more (or less) than the global
  base rate, consistently across multiple races that day, is a real,
  same-day, track-specific speed bias - something the existing
  track_barrier ADJ_TERM (a STATIC, all-time historical lookup) cannot
  represent by construction.

PART B - PACE IMPACT ON INDIVIDUAL MISSES
  For every runner, cross its ACTUAL settling band for that run against
  the race's ACTUAL raceShapeEarly (tercile: Slow/Even/Hot run early
  tempo) and look at the mean WPR miss in each of the 4x3 cells. The
  textbook racing pattern (leaders helped by an uncontested/slow pace,
  hurt by a genuinely hot one; backmarkers the mirror image) should show
  up as a clean, monotonic pattern in the miss if pace mismatch is a real,
  material driver of WPR's errors - not just noise.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from wpr_projection import _barrier_band

pd.set_option("display.width", 140)

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"


def load_runners():
    df = pd.read_csv(RUNNERS_CSV, low_memory=False)
    df = df[(df["resulted"] == 1) & (df["scratched"] != 1)].copy()
    df["wprp_proj"] = pd.to_numeric(df["wprp_proj"], errors="coerce")
    df["wpr_actual"] = pd.to_numeric(df["wpr_actual"], errors="coerce")
    df["miss"] = df["wpr_actual"] - df["wprp_proj"]
    df["barrier"] = pd.to_numeric(df["barrier"], errors="coerce")
    df["won"] = pd.to_numeric(df["won"], errors="coerce")
    df["placed"] = pd.to_numeric(df["placed"], errors="coerce")
    df["horse_lc"] = df["horse"].astype(str).str.lower()
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    # field_size proxy: count of resulted runners in this race_id (the
    # official field size isn't a toprate_runners.csv column; this proxy is
    # only used for barrier banding, which is tolerant of small differences).
    df["field_size"] = df.groupby("race_id")["horse"].transform("count")
    return df


def load_form_shape():
    fh = pd.read_csv(FORM_CSV, usecols=[
        "horse", "date", "track", "scrape_date",
        "raceShapeEarly", "raceShapeMid", "raceShapeLate",
    ], low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.sort_values("scrape_date").drop_duplicates(
        subset=["horse_lc", "date", "track"], keep="last")
    return fh[["horse_lc", "date", "track", "raceShapeEarly", "raceShapeMid", "raceShapeLate"]]


def run():
    df = load_runners()
    print(f"Resulted, non-scratched runner rows: {len(df):,}")

    print("\n=== PART A: track bias by meeting (settling band + barrier band) ===")
    global_settle = df.groupby("_settling").agg(
        win_rate=("won", "mean"), place_rate=("placed", "mean"), n=("won", "size"))
    print("Global base rates by settling band:")
    print(global_settle)

    df["barrier_band"] = [
        _barrier_band(b, f) for b, f in zip(df["barrier"], df["field_size"])
    ]
    global_barrier = df.groupby("barrier_band").agg(
        win_rate=("won", "mean"), place_rate=("placed", "mean"), n=("won", "size"))
    print("\nGlobal base rates by barrier band:")
    print(global_barrier)

    meet_rows = []
    for (venue, date), g in df.dropna(subset=["venue", "date"]).groupby(["venue", "date"]):
        if len(g) < 30:  # need several races' worth of runners for a meaningful meeting-level read
            continue
        row = {"venue": venue, "date": date, "n": len(g)}
        for band in ["leader", "on-pace", "midfield", "backmarker"]:
            sub = g[g["_settling"] == band]
            if len(sub) >= 5:
                base = global_settle.loc[band, "win_rate"] if band in global_settle.index else np.nan
                row[f"{band}_win"] = sub["won"].mean()
                row[f"{band}_n"] = len(sub)
                row[f"{band}_dev"] = sub["won"].mean() - base
        meet_rows.append(row)
    meets = pd.DataFrame(meet_rows)
    print(f"\nMeetings with >=30 resulted runners: {len(meets):,}")

    # Rank meetings by the clearest, most interpretable single signal: how
    # much MORE leaders won than the global base rate (classic "speed bias
    # day" direction) - both extremes reported (biggest speed-favouring and
    # biggest speed-killing days).
    lm = meets.dropna(subset=["leader_dev"]).sort_values("leader_dev", ascending=False)
    print("\nTop 8 meetings where LEADERS won far MORE than their global base rate "
          "(possible speed-favouring bias):")
    print(lm[["venue", "date", "n", "leader_win", "leader_n", "leader_dev"]].head(8).to_string(index=False))
    print("\nTop 8 meetings where LEADERS won far LESS than their global base rate "
          "(possible speed-killing / hold-up bias):")
    print(lm[["venue", "date", "n", "leader_win", "leader_n", "leader_dev"]].tail(8).to_string(index=False))

    print(f"\nStd dev of leader_dev across meetings: {lm['leader_dev'].std():.3f} "
          f"(global leader win rate: {global_settle.loc['leader', 'win_rate']:.3f})")

    # Does a meeting's speed-bias magnitude correlate with WPR getting MORE
    # material misses that day? (a real bias should show up as WORSE model
    # performance on days it's strongest, since WPR has no same-day signal
    # for it at all)
    df["material"] = df["wprp_miss_category"].notna()
    meet_material = df.dropna(subset=["venue", "date"]).groupby(["venue", "date"]).agg(
        material_rate=("material", "mean"), mean_abs_miss=("miss", lambda s: s.abs().mean()))
    lm2 = lm.set_index(["venue", "date"]).join(meet_material)
    corr = lm2["leader_dev"].abs().corr(lm2["mean_abs_miss"])
    print(f"\nCorrelation between |leader_dev| (bias magnitude) and mean |miss| that day: {corr:.3f}")

    print("\n=== PART B: pace impact on individual misses ===")
    shape = load_form_shape()
    merged = df.merge(shape, on=["horse_lc", "date"], how="inner", suffixes=("", "_fh"))
    # venue vs track naming can differ for the same meeting on rare rows;
    # keep only rows where they agree, to avoid a wrong-race mismatch.
    merged = merged[merged["venue"] == merged["track"]]
    print(f"Runners matched to a form-history raceShapeEarly value: {len(merged):,} "
          f"of {len(df):,} ({len(merged) / len(df) * 100:.1f}%)")

    merged = merged.dropna(subset=["raceShapeEarly", "miss", "_settling"])
    merged["pace_tercile"] = pd.qcut(merged["raceShapeEarly"], 3, labels=["Slow early", "Even early", "Hot early"])

    print("\nMean WPR miss by (actual settling band) x (actual early-pace tercile):")
    pivot = merged.pivot_table(index="_settling", columns="pace_tercile", values="miss", aggfunc="mean")
    pivot = pivot.reindex(["leader", "on-pace", "midfield", "backmarker"])
    print(pivot.round(2))

    print("\nSample sizes for the same cells:")
    pivot_n = merged.pivot_table(index="_settling", columns="pace_tercile", values="miss", aggfunc="size")
    pivot_n = pivot_n.reindex(["leader", "on-pace", "midfield", "backmarker"])
    print(pivot_n)

    print("\nDone.")


if __name__ == "__main__":
    run()
