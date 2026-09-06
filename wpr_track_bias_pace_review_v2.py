"""
wpr_track_bias_pace_review_v2.py - corrects a real gap in v1's track-bias
test, per direct user feedback.

v1's Part A tested whether a meeting's bias MAGNITUDE correlated with its
overall miss MAGNITUDE (an aggregate, direction-blind test) - and found
essentially nothing (r=0.031). That is NOT the same question as: "did an
individual runner get forgiven for underperforming its WPR projection
because ITS running style clashed with THAT DAY'S dominant winning style?"
This script tests the real hypothesis directly, mirroring the cross-tab
design that worked cleanly for pace in v1's Part B:

  1. Classify each meeting by its ACTUAL winner profile that day - what
     fraction of races were won by on-speed runners (leader/on-pace) vs
     off-speed (midfield/backmarker), and separately what fraction were won
     by Inside/Mid/Wide barriers (wpr_projection._barrier_band) - tercile
     meetings into speed-biased / neutral / hold-up-biased (and
     inside-biased / neutral / wide-biased).
  2. Cross each INDIVIDUAL RUNNER's own settling band (and own barrier
     band) against that day's bias tercile and report mean WPR miss per
     cell. If the "forgiveness" hypothesis is right: off-speed runners on a
     speed-biased day should show a MORE NEGATIVE miss (systematically
     forgivable underperformance) than off-speed runners on a hold-up-
     biased or neutral day - and the mirror pattern for on-speed runners.
  3. Also pulls ACTUAL in-running position at the 800m/400m marks
     (wpr_form_history's position800m/position400m, normalised by field
     size so races of different field sizes are comparable) for a finer-
     grained read than the 4-bucket settling band alone.

Meeting bias classification uses ONLY the winner of each race (the
clearest, least noisy signal - one runner per race, no room for "how
strongly did it settle there" ambiguity), which needs >=6 races/meeting
to be worth classifying at all (fewer than that and the tercile split
itself is mostly noise, the exact problem v1's leader-only version had).

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from wpr_projection import _barrier_band

pd.set_option("display.width", 140)

RUNNERS_CSV = "toprate_runners.csv"
FORM_CSV = "wpr_form_history.csv.gz"

ON_SPEED = {"leader", "on-pace"}
OFF_SPEED = {"midfield", "backmarker"}


def load_runners():
    df = pd.read_csv(RUNNERS_CSV, low_memory=False)
    df = df[(df["resulted"] == 1) & (df["scratched"] != 1)].copy()
    df["wprp_proj"] = pd.to_numeric(df["wprp_proj"], errors="coerce")
    df["wpr_actual"] = pd.to_numeric(df["wpr_actual"], errors="coerce")
    df["miss"] = df["wpr_actual"] - df["wprp_proj"]
    df["barrier"] = pd.to_numeric(df["barrier"], errors="coerce")
    df["won"] = pd.to_numeric(df["won"], errors="coerce")
    df["horse_lc"] = df["horse"].astype(str).str.lower()
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df["field_size"] = df.groupby("race_id")["horse"].transform("count")
    df["barrier_band"] = [_barrier_band(b, f) for b, f in zip(df["barrier"], df["field_size"])]
    df["speed_group"] = np.where(df["_settling"].isin(ON_SPEED), "on-speed",
                          np.where(df["_settling"].isin(OFF_SPEED), "off-speed", None))
    return df


def load_form_positions():
    fh = pd.read_csv(FORM_CSV, usecols=[
        "horse", "date", "track", "scrape_date", "field_size",
        "position800m", "position400m",
    ], low_memory=False)
    fh["horse_lc"] = fh["horse"].astype(str).str.lower()
    fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
    fh = fh.sort_values("scrape_date").drop_duplicates(
        subset=["horse_lc", "date", "track"], keep="last")
    return fh[["horse_lc", "date", "track", "field_size", "position800m", "position400m"]]


def classify_meetings(df, winner_col_values, label_pos, label_neg, min_races=6):
    """winner_col_values: Series aligned to the winners-only frame, True/False/None
    (True = counts toward the 'positive' bias direction, False = toward 'negative',
    None = ignored e.g. an unclassifiable barrier). Returns a (venue,date) -> bias
    tercile label lookup, using only meetings with >= min_races classified winners."""
    w = pd.DataFrame({"venue": df["venue"], "date": df["date"], "flag": winner_col_values})
    w = w.dropna(subset=["flag"])
    g = w.groupby(["venue", "date"])
    frac = g["flag"].mean()
    n = g["flag"].size()
    frac = frac[n >= min_races]
    if len(frac) < 6:
        return {}
    lo, hi = frac.quantile([1 / 3, 2 / 3])
    labels = {}
    for key, v in frac.items():
        if v >= hi:
            labels[key] = label_pos
        elif v <= lo:
            labels[key] = label_neg
        else:
            labels[key] = "neutral"
    return labels


def run():
    df = load_runners()
    print(f"Resulted, non-scratched runner rows: {len(df):,}")
    winners = df[df["won"] == 1].copy()
    print(f"Winners (one per race): {len(winners):,}")

    print("\n=== Meeting classification: speed profile of the day's winners ===")
    is_on_speed = winners["speed_group"].map({"on-speed": True, "off-speed": False})
    speed_bias = classify_meetings(winners, is_on_speed, "speed-biased", "holdup-biased")
    vc = pd.Series(list(speed_bias.values())).value_counts()
    print(vc)

    print("\n=== Meeting classification: barrier profile of the day's winners ===")
    is_inside = winners["barrier_band"].map({"Inside": True, "Wide": False})
    barrier_bias = classify_meetings(winners, is_inside, "inside-biased", "wide-biased")
    vc2 = pd.Series(list(barrier_bias.values())).value_counts()
    print(vc2)

    df["meeting_key"] = list(zip(df["venue"], df["date"]))
    df["speed_bias_day"] = df["meeting_key"].map(speed_bias)
    df["barrier_bias_day"] = df["meeting_key"].map(barrier_bias)

    print("\n=== Cross-tab 1: runner's own settling band x day's speed-bias classification ===")
    print("(mean WPR miss per cell - the 'forgiveness' hypothesis predicts off-speed runners")
    print(" should be MORE negative on a speed-biased day than on a holdup-biased day, and")
    print(" the mirror pattern for on-speed runners)")
    sub = df.dropna(subset=["speed_bias_day", "_settling"])
    pivot = sub.pivot_table(index="_settling", columns="speed_bias_day", values="miss", aggfunc="mean")
    pivot = pivot.reindex(["leader", "on-pace", "midfield", "backmarker"])
    cols_order = [c for c in ["holdup-biased", "neutral", "speed-biased"] if c in pivot.columns]
    print(pivot[cols_order].round(2))
    n_pivot = sub.pivot_table(index="_settling", columns="speed_bias_day", values="miss", aggfunc="size")
    print("\nsample sizes:")
    print(n_pivot.reindex(["leader", "on-pace", "midfield", "backmarker"])[cols_order])

    print("\n=== Cross-tab 2: runner's own barrier band x day's barrier-bias classification ===")
    sub2 = df.dropna(subset=["barrier_bias_day", "barrier_band"])
    pivot2 = sub2.pivot_table(index="barrier_band", columns="barrier_bias_day", values="miss", aggfunc="mean")
    pivot2 = pivot2.reindex(["Inside", "Mid", "Wide"])
    cols_order2 = [c for c in ["wide-biased", "neutral", "inside-biased"] if c in pivot2.columns]
    print(pivot2[cols_order2].round(2))
    n_pivot2 = sub2.pivot_table(index="barrier_band", columns="barrier_bias_day", values="miss", aggfunc="size")
    print("\nsample sizes:")
    print(n_pivot2.reindex(["Inside", "Mid", "Wide"])[cols_order2])

    print("\n=== Finer-grained check: actual in-running position at 800m/400m ===")
    pos = load_form_positions()
    merged = df.merge(pos, on=["horse_lc", "date"], how="inner", suffixes=("", "_fh"))
    merged = merged[merged["venue"] == merged["track"]]
    merged["rel_pos_800"] = pd.to_numeric(merged["position800m"], errors="coerce") / merged["field_size_fh"]
    merged["rel_pos_400"] = pd.to_numeric(merged["position400m"], errors="coerce") / merged["field_size_fh"]
    print(f"Matched rows with usable position data: {merged['rel_pos_800'].notna().sum():,} / {len(merged):,}")

    m2 = merged.dropna(subset=["rel_pos_800", "speed_bias_day"])
    print("\nMean WPR miss by rel_pos_800 quartile x day's speed-bias classification "
          "(rel_pos 0 = led at 800m, 1 = last at 800m):")
    m2 = m2.copy()
    m2["pos800_q"] = pd.qcut(m2["rel_pos_800"], 4, labels=["Q1 (forward)", "Q2", "Q3", "Q4 (back)"])
    p3 = m2.pivot_table(index="pos800_q", columns="speed_bias_day", values="miss", aggfunc="mean")
    cols_order3 = [c for c in ["holdup-biased", "neutral", "speed-biased"] if c in p3.columns]
    print(p3[cols_order3].round(2))
    n3 = m2.pivot_table(index="pos800_q", columns="speed_bias_day", values="miss", aggfunc="size")
    print("\nsample sizes:")
    print(n3[cols_order3])

    print("\nDone.")


if __name__ == "__main__":
    run()
