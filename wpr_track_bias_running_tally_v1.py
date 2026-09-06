"""
wpr_track_bias_running_tally_v1.py - turns the track-bias finding from
wpr_track_bias_pace_review_v2.py into something that could actually be used
LIVE, not just diagnosed after the fact.

v2's cross-tabs used the WHOLE day's winner profile (including races not
yet run) to classify a meeting as speed-biased/holdup-biased or inside/
wide-biased - a real, oracle-only diagnostic. This script tests whether a
RUNNING TALLY - built from ONLY races that have ALREADY been run earlier
that same day - carries the same signal. If it does, it's pre-race-safe for
every race but the first one or two on a card (exactly the same leak-safe
"same-day, cross-race, earlier-race-only" design already proven by the
existing pace_scenario/contested_pace features - just extended from
single-race to whole-meeting scope).

METHOD
  Within each (venue, date) meeting, order races by start_time. For race k,
  compute the running tally using ONLY races 1..k-1 at that meeting:
    - speed_tally_so_far: fraction of those earlier winners that were
      on-speed (leader/on-pace) vs off-speed (midfield/backmarker)
    - inside_tally_so_far: fraction of those earlier winners from an
      Inside barrier vs Wide (wpr_projection._barrier_band)
  Race k needs >=2 completed EARLIER races at that meeting to get a tally
  at all (fewer than that is mostly noise - one race tells you nothing
  about a "day", per the same small-sample problem v1's naive test hit).
  Every runner in race k then carries that SAME pre-k, meeting-level tally
  value (it does not know its own race's outcome, only what already
  happened earlier that day).

  Cross each runner's own settling band / barrier band against the
  RUNNING tally (tercile-bucketed) and report mean WPR miss per cell -
  the same test as v2, but using only genuinely pre-race-available
  information this time.

NO EM DASHES policy: hyphens only.
"""
import numpy as np
import pandas as pd

from wpr_projection import _barrier_band

pd.set_option("display.width", 140)

RUNNERS_CSV = "toprate_runners.csv"
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
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df["start_time"] = pd.to_datetime(df["start_time"], errors="coerce")
    df["field_size"] = df.groupby("race_id")["horse"].transform("count")
    df["barrier_band"] = [_barrier_band(b, f) for b, f in zip(df["barrier"], df["field_size"])]
    df["speed_group"] = np.where(df["_settling"].isin(ON_SPEED), "on-speed",
                          np.where(df["_settling"].isin(OFF_SPEED), "off-speed", None))
    return df


def build_running_tallies(df):
    """Per race_id, the pre-race running tally from EARLIER races at the
    SAME (venue, date) meeting only, using each earlier race's winner."""
    winners = df[df["won"] == 1].dropna(subset=["venue", "date", "start_time"]).copy()
    winners = winners.sort_values(["venue", "date", "start_time"])
    winners["is_on_speed"] = winners["speed_group"].map({"on-speed": 1.0, "off-speed": 0.0})
    winners["is_inside"] = winners["barrier_band"].map({"Inside": 1.0, "Wide": 0.0})

    tallies = []
    for (venue, date), g in winners.groupby(["venue", "date"]):
        g = g.sort_values("start_time")
        speed_vals, inside_vals = [], []
        for _, row in g.iterrows():
            n_speed = len([v for v in speed_vals if not pd.isna(v)])
            n_inside = len([v for v in inside_vals if not pd.isna(v)])
            speed_tally = np.nanmean(speed_vals) if n_speed >= 2 else np.nan
            inside_tally = np.nanmean(inside_vals) if n_inside >= 2 else np.nan
            tallies.append({"race_id": row["race_id"], "speed_tally_so_far": speed_tally,
                             "inside_tally_so_far": inside_tally, "races_so_far": len(speed_vals)})
            speed_vals.append(row["is_on_speed"])
            inside_vals.append(row["is_inside"])
    return pd.DataFrame(tallies)


def bucket(s, labels):
    valid = s.dropna()
    if len(valid) < 30:
        return pd.Series(index=s.index, dtype=object)
    lo, hi = valid.quantile([1 / 3, 2 / 3])
    out = pd.Series(index=s.index, dtype=object)
    out[s <= lo] = labels[0]
    out[(s > lo) & (s < hi)] = labels[1]
    out[s >= hi] = labels[2]
    return out


def run():
    df = load_runners()
    print(f"Resulted, non-scratched runner rows: {len(df):,}")

    tallies = build_running_tallies(df)
    df = df.merge(tallies, on="race_id", how="left")
    have_tally = df["speed_tally_so_far"].notna()
    print(f"Runners with a usable running speed-tally (>=2 earlier races that day): "
          f"{have_tally.sum():,} ({have_tally.mean() * 100:.1f}%)")

    df["speed_tally_bucket"] = bucket(df["speed_tally_so_far"], ["holdup-so-far", "neutral", "speed-so-far"])
    df["inside_tally_bucket"] = bucket(df["inside_tally_so_far"], ["wide-so-far", "neutral", "inside-so-far"])

    print("\n=== Cross-tab: runner's own settling band x RUNNING speed-tally (pre-race-safe) ===")
    sub = df.dropna(subset=["speed_tally_bucket", "_settling"])
    piv = sub.pivot_table(index="_settling", columns="speed_tally_bucket", values="miss", aggfunc="mean")
    piv = piv.reindex(["leader", "on-pace", "midfield", "backmarker"])
    cols = [c for c in ["holdup-so-far", "neutral", "speed-so-far"] if c in piv.columns]
    print(piv[cols].round(2))
    n = sub.pivot_table(index="_settling", columns="speed_tally_bucket", values="miss", aggfunc="size")
    print("\nsample sizes:")
    print(n.reindex(["leader", "on-pace", "midfield", "backmarker"])[cols])

    print("\n=== Cross-tab: runner's own barrier band x RUNNING inside-tally (pre-race-safe) ===")
    sub2 = df.dropna(subset=["inside_tally_bucket", "barrier_band"])
    piv2 = sub2.pivot_table(index="barrier_band", columns="inside_tally_bucket", values="miss", aggfunc="mean")
    piv2 = piv2.reindex(["Inside", "Mid", "Wide"])
    cols2 = [c for c in ["wide-so-far", "neutral", "inside-so-far"] if c in piv2.columns]
    print(piv2[cols2].round(2))
    n2 = sub2.pivot_table(index="barrier_band", columns="inside_tally_bucket", values="miss", aggfunc="size")
    print("\nsample sizes:")
    print(n2.reindex(["Inside", "Mid", "Wide"])[cols2])

    print("\nDone.")


if __name__ == "__main__":
    run()
