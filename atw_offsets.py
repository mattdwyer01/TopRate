"""Per-horse ATW offset (see compute_atw_offsets). Shared by toprate_daily.py (payload) and projection/run.py (frozen into the projection log)."""
from pathlib import Path

import pandas as pd


def compute_atw_offsets(fh):
    """Per-horse ATW offset: how far the form feed's rating sits above the results files' rating for the same runs.

    The form feed (wpr_form_history.csv.gz, what the dashboard's Recent runs table and form chart show) is ATW, each run's rating adjusted
    to the weight carried in the horse's upcoming race. The results files (race_results_*.csv.gz, what the projection model trains on and
    predicts) hold the plain WPR. For one scrape the gap is the same constant on every run of a horse (about -0.65 WPR per kg above 57.7kg), so
    the median over the horse's runs that appear in both (all years of results, so a horse whose only rated runs are old still matches) is its offset. Used by the frontend to draw the projection and the winning line on the
    chart's own (ATW) scale. Only the horse's latest scrape is used (older scrapes carry an older weight); a horse with no matched run gets no
    offset (nothing to adjust, it stays on the plain rating). Fail-safe: any error returns {} (no shift).

    13 Oct 2026: DISABLED. The form history now holds our own plain WPR for every run (own_ratings/replace_form_ratings.py), not TopRate's
    form-feed rating at the next start's weight, so there is no gap to measure; comparing it with the (still TopRate) results ratings
    would only measure the difference between the two rating systems. Returns {} (no shift) until the results files are re-rated too.
    """
    if True:
        return {}
    try:
        files = sorted(Path(__file__).parent.glob("race_results_20*.csv.gz"))
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
        # The median of every matched run: one matched run is a real measurement, and the median ignores a stray run. The gap is one constant per
        # horse per scrape; the ~1.5% of horses that looked unsteady (std > 0.6) had ONE odd run, nearly always the horse's most recent, whose results
        # rating differs from the feed (araminta: 37 runs at +2.4, the latest at +10.0). Following the latest run, as an earlier version did, picked
        # that outlier; the median of the other runs is the offset.
        g = m.groupby("horse_lc")["d"].agg(["median"])
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


# 16 Oct 2026: display offset from TopRate's own runner pages. The race table's Nett and L3 are TopRate figures rated at the weight the horse carries next
# start, while the projection is on the plain results scale, so Proj looked low beside them (Caulfield Cup R9: Proj 5.3 below L3 as shown, 1.3 below on the
# plain scale). The offset is the median gap between the runner-page rating and the results files' plain wpr over the runs both have (the same measure as
# projection/features.tr_lookup). It is for DISPLAY only: the dashboard shows Proj + offset in the table, ranking, gap lines, prices and the projection log
# stay on the plain scale (ranking on the weight-adjusted scale picked winners worse, 7 Oct 2026 test). Not used by projection/run.py.
TR_CUTOFF = "2026-10-09"   # results files carry TopRate's raw wpr only before this (racing.com results after)


def compute_tr_offsets(root=None, since="2025-01-01"):
    """{lowercased horse name: offset}, runner-page rating minus results-file plain wpr, median per horse. Fail-safe: any error returns {} (no shift)."""
    import glob
    import gzip
    import json
    try:
        root = Path(root) if root else Path(__file__).parent
        rows = []
        for f in sorted(glob.glob(str(root / "data" / "tr_form" / "*.json.gz"))):
            with gzip.open(f, "rt") as fh:
                for r in json.load(fh).get("runs", {}).values():
                    if r.get("isBarrierTrial") or r.get("isJumpout") or r.get("wpr") is None:
                        continue
                    rows.append((r.get("horse_id"), r.get("date"), r["wpr"], str(r.get("horse") or "").strip().lower()))
        t = pd.DataFrame(rows, columns=["horse_id", "date", "tr", "name"])
        t["horse_id"] = pd.to_numeric(t["horse_id"], errors="coerce")
        t["date"] = pd.to_datetime(t["date"], errors="coerce")
        t["tr"] = pd.to_numeric(t["tr"], errors="coerce")
        t = t.dropna(subset=["horse_id", "date", "tr"]).drop_duplicates(["horse_id", "date"], keep="last")
        files = [p for p in sorted(glob.glob(str(root / "race_results_20*.csv.gz"))) if int(Path(p).name[13:17]) >= int(since[:4])]
        res = pd.concat([pd.read_csv(p, usecols=lambda c: c in ("horse_id", "date", "wpr"), low_memory=False) for p in files], ignore_index=True)
        res["date"] = pd.to_datetime(res["date"], errors="coerce")
        res["horse_id"] = pd.to_numeric(res["horse_id"], errors="coerce")
        res["wpr"] = pd.to_numeric(res["wpr"], errors="coerce")
        res = res[res["date"] < pd.Timestamp(TR_CUTOFF)].dropna(subset=["horse_id", "date", "wpr"]).drop_duplicates(["horse_id", "date"], keep="last")
        m = t.merge(res, on=["horse_id", "date"])
        m["d"] = m["tr"] - m["wpr"]
        med = m.groupby("horse_id")["d"].median()
        names = t[t["name"] != ""].drop_duplicates("horse_id", keep="last").set_index("horse_id")["name"]
        out = {}
        for hid, v in med.items():
            n = names.get(hid)
            if n:
                out[n] = round(float(v), 1)
        return out
    except Exception as e:
        print(f"  TopRate ATW offsets skipped: {e}")
        return {}
