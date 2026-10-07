"""Per-horse ATW offset (see compute_atw_offsets). Shared by toprate_daily.py (payload) and projection/run.py (frozen into the projection log)."""
from pathlib import Path

import pandas as pd


def compute_atw_offsets(fh):
    """Per-horse ATW offset: how far the form feed's rating sits above the results files' rating for the same runs.

    The form feed (wpr_form_history.csv.gz, what the dashboard's Recent runs table and form chart show) is ATW, each run's rating adjusted
    to the weight carried in the horse's upcoming race. The results files (race_results_*.csv.gz, what the projection model trains on and
    predicts) hold the plain WPR. For one scrape the gap is the same constant on every run of a horse (about -0.65 WPR per kg above 57.7kg), so
    the median over the horse's runs that appear in both is its offset. Used by the frontend to draw the projection and the winning line on the
    chart's own (ATW) scale. Only the horse's latest scrape is used (older scrapes carry an older weight); a horse with no matched run gets no
    offset (nothing to adjust, it stays on the plain rating). Fail-safe: any error returns {} (no shift).
    """
    try:
        files = sorted(Path(__file__).parent.glob("race_results_20*.csv.gz"))[-2:]
        res = pd.concat([pd.read_csv(p, usecols=["horse_id", "date", "wpr"], low_memory=False) for p in files], ignore_index=True)
        res["wpr"] = pd.to_numeric(res["wpr"], errors="coerce")
        res["date"] = pd.to_datetime(res["date"], errors="coerce")
        res["horse_id"] = pd.to_numeric(res["horse_id"], errors="coerce")
        res = res.dropna(subset=["horse_id", "date", "wpr"]).drop_duplicates(["horse_id", "date"], keep="last")
        f = fh[["horse_lc", "horse_id", "date", "wpr", "scrape_date"]].copy()
        f["horse_id"] = pd.to_numeric(f["horse_id"], errors="coerce")
        f = f[f["date"] >= res["date"].min()]
        f = f[f["scrape_date"] == f.groupby("horse_lc")["scrape_date"].transform("max")]
        m = f.merge(res, on=["horse_id", "date"], suffixes=("_form", "_res"))
        m["d"] = m["wpr_form"] - m["wpr_res"]
        g = m.groupby("horse_lc")["d"].agg(["median", "std", "count"])
        # One matched run is a real measurement (the gap is one constant per horse per scrape). Two or more with a steady gap use the median. Two or
        # more whose gap moves (about 1%) differ because the weight-for-age scale depends on the horse's age, the time of year and the distance, so
        # the offset for today is the gap of the horse's most recent matched run, the closest in time.
        latest = m.sort_values("date").groupby("horse_lc")["d"].last()
        steady = (g["count"] == 1) | (g["std"].fillna(0) <= 0.6)
        g["median"] = g["median"].where(steady, latest)
        return {h: round(float(v), 1) for h, v in g["median"].items()}
    except Exception as e:
        print(f"  ATW offsets skipped: {e}")
        return {}


def load_offsets(horses, form_history_csv):
    """{lowercased horse name: offset} for the given horses, read straight from the form history file."""
    try:
        want = {str(h).strip().lower() for h in horses}
        fh = pd.read_csv(form_history_csv, dtype={"horse": str, "horse_id": str})
        fh["horse_lc"] = fh["horse"].astype(str).str.strip().str.lower()
        fh = fh[fh["horse_lc"].isin(want)]
        fh["wpr"] = pd.to_numeric(fh["wpr"], errors="coerce")
        fh["date"] = pd.to_datetime(fh["date"], errors="coerce")
        fh = fh.dropna(subset=["date", "wpr"])
        if "isBarrierTrial" in fh.columns:
            fh = fh[fh["isBarrierTrial"].fillna(0).astype(int) == 0]
        keys = ["horse_lc", "date"] + (["track"] if "track" in fh.columns else [])
        if "scrape_date" not in fh.columns or "horse_id" not in fh.columns:
            return {}
        fh = fh.sort_values("scrape_date", kind="stable").drop_duplicates(subset=keys, keep="last")
        return compute_atw_offsets(fh)
    except Exception as e:
        print(f"  ATW offsets skipped: {e}")
        return {}
