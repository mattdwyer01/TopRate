"""Join racing.com results (data/gps/rc_results_runs_<year>.parquet, see rc_results_ingest.py) to our runners.

Race numbers do NOT line up between racing.com and our runners file (racing.com can number a trial or extra
race first, so a 9-race card appears as 10), so the key is (local date, normalised horse name). A horse runs
once a day, so that is almost always unique; the few duplicates are resolved by venue, then by distance.

  python -m own_ratings.rc_join                 summary of the match against the runners file
"""
import glob, re
import pandas as pd

GPS_GLOB = "data/gps/rc_results_runs_*.parquet"
_SPONSOR = re.compile(r"^(sportsbet|bet365|apiam|ladbrokes|tab|neds|pointsbet|picklebet|southside|thoroughbred club|"
                      r"aquis|thomas farms( rc)?)[\s-]+(park[\s-]+)?", re.I)


def norm_horse(s) -> str:
    """'Lucy Lulu (NZ)' -> 'lucylulu'."""
    return re.sub(r"[^a-z0-9]", "", re.sub(r"\s*\([a-z]{2,3}\)\s*$", "", str(s).lower()))


def norm_venue(s) -> str:
    n = _SPONSOR.sub("", str(s).strip().lower())
    n = re.sub(r"[^a-z0-9]+", " ", n).strip()
    return re.sub(r"^mount ", "mt ", n)


def load_rc_results(pattern: str = GPS_GLOB) -> pd.DataFrame:
    parts = [pd.read_parquet(p) for p in sorted(glob.glob(pattern))]
    if not parts:
        return pd.DataFrame()
    d = pd.concat(parts, ignore_index=True)
    d = d.drop_duplicates(["meeting_code", "race_no", "horse_code", "horse"])
    d["h"] = d.horse.map(norm_horse)
    d["v"] = d.venue.map(norm_venue)
    return d


def match_runners(runners: pd.DataFrame, rc: pd.DataFrame) -> pd.DataFrame:
    """One row per matched runner: run_id plus rc finish, margin_l, weight_kg, sp, race_distance, going.

    `runners` needs date, venue, horse, run_id (distance optional). Unmatched runners are simply absent.
    """
    r = runners[["run_id", "date", "venue", "horse"] + (["distance"] if "distance" in runners else [])].copy()
    r["d"] = r["date"].astype(str).str[:10]
    r["h"] = r.horse.map(norm_horse)
    r["v"] = r.venue.map(norm_venue)
    keep = ["race_date", "h", "v", "race_no", "race_distance", "finish", "margin_l", "weight_kg", "sp", "going",
            "barrier", "meeting_code"]
    m = r.merge(rc[keep], left_on=["d", "h"], right_on=["race_date", "h"], how="inner", suffixes=("", "_rc"))
    if m.empty:
        return m
    # resolve duplicates: same venue first, then same distance
    m["score"] = (m.v == m.v_rc).astype(int) * 2
    if "distance" in m:
        m["score"] += (pd.to_numeric(m.distance, errors="coerce") == m.race_distance).astype(int)
    m = m.sort_values("score", ascending=False).drop_duplicates("run_id")
    # a duplicate that only matched by name on a different venue is not trusted
    ambiguous = m.duplicated(["race_date", "h", "meeting_code"], keep=False)
    return m[~ambiguous | (m.score >= 2)].drop(columns=["race_date", "v_rc", "score"], errors="ignore")


def main():
    import runners_io
    rc = load_rc_results()
    if rc.empty:
        print("no rc results files"); return
    r = runners_io.read_runners()
    r = r[(r["date"].astype(str).str[:10] >= rc.race_date.min()) & (r["date"].astype(str).str[:10] <= rc.race_date.max())]
    m = match_runners(r, rc)
    sc = r["scratched"].fillna(0) if "scratched" in r else pd.Series(0, index=r.index)
    live = r[sc == 0]
    print(f"rc rows {len(rc)}, our runners in window {len(r)} (non-scratched {len(live)})")
    print(f"matched {m.run_id.nunique()} ({m.run_id.nunique() / len(r):.1%} of all, "
          f"{live.run_id.isin(m.run_id).mean():.1%} of non-scratched)")


if __name__ == "__main__":
    main()
