"""runners_io.py -- toprate_runners.csv split into a live file + a gzipped archive (Oct 2026).

Why: toprate_runners.csv grows ~20MB a month (every runner since 26 Apr 2026) and reached GitHub's 100MB per-file
limit on 30 Sep / 1 Oct 2026: every Daily fetch push that added the next day's fields was rejected
("GH001: Large files detected", toprate_runners.csv 100.03MB), so tomorrow's races never reached the dashboard.

Layout:
  toprate_runners.csv              live file: races in the last LIVE_DAYS days (Melbourne date) plus every future
                                   race. This is what the 5-minute jobs rewrite and commit.
  toprate_runners_archive.csv.gz   older races (same columns), gzipped. Rewritten only when races age past the cutoff
                                   (save_split), so it is committed about once a day, not every few minutes.

Readers that need the whole history (toprate_daily.load_runners, wpr_projection's trainer/jockey and wpr_nett joins)
use read_runners(), which returns archive + live with the live row winning on a duplicate run_id. Readers that only
need recent / upcoming races (price refresh, merge_remote_weights, speedmap_jockey_tracker) can keep reading the live
file directly. Same pattern as wpr_form_history.csv.gz.
"""
from datetime import datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import pandas as pd

DIR = Path(__file__).parent
LIVE_CSV = DIR / "toprate_runners.csv"
ARCHIVE_CSV = DIR / "toprate_runners_archive.csv.gz"
LIVE_DAYS = 60
# deterministic gzip (no timestamp in the header): an unchanged archive rewrites to identical bytes
GZIP = {"method": "gzip", "mtime": 0}


def archive_for(path):
    """The archive that belongs with a runners CSV path (None for any other file, e.g. the backtest CSV)."""
    path = Path(path)
    return path.with_name(ARCHIVE_CSV.name) if path.name == LIVE_CSV.name else None


def read_runners(path=LIVE_CSV, **kw):
    """Archive + live runners file as one frame (pandas.read_csv kwargs pass through, e.g. usecols / dtype).
    Rows are archive first, live last, so drop_duplicates(keep="last") prefers the live copy."""
    path = Path(path)
    arc = archive_for(path)
    parts = []
    if arc is not None and arc.exists():
        parts.append(pd.read_csv(arc, **kw))
    if path.exists():
        parts.append(pd.read_csv(path, **kw))
    if not parts:
        raise FileNotFoundError(path)
    return pd.concat(parts, ignore_index=True) if len(parts) > 1 else parts[0]


def cutoff_date(today=None):
    """First race date kept in the live file (Melbourne calendar)."""
    today = today or datetime.now(ZoneInfo("Australia/Melbourne")).date()
    return (today - timedelta(days=LIVE_DAYS)).isoformat()


def save_split(df, live_path=LIVE_CSV, today=None):
    """Write df (archive + live rows, deduplicated) as live file + archive. Rows dated before the cutoff go to the
    archive; the archive is only rewritten when it gains run_ids it did not have (rows that just aged out)."""
    live_path = Path(live_path)
    arc = archive_for(live_path)
    date = df["date"].astype(str).str[:10]
    old = date.lt(cutoff_date(today)) & df["date"].notna()
    if arc is not None and old.any():
        have = (set(pd.read_csv(arc, usecols=["run_id"], dtype={"run_id": str})["run_id"])
                if arc.exists() else set())
        old_rows = df[old]
        if not old_rows["run_id"].astype(str).isin(have).all():
            prev = pd.read_csv(arc, dtype={"run_id": str, "race_id": str}) if arc.exists() else old_rows.iloc[:0]
            merged = pd.concat([prev, old_rows], ignore_index=True)
            merged = merged.drop_duplicates(subset=["run_id"], keep="last")
            merged = merged.sort_values(["date", "race_id", "run_id"], kind="mergesort")
            merged.reindex(columns=list(df.columns) + [c for c in merged.columns if c not in df.columns]) \
                .to_csv(arc, index=False, compression=GZIP)
            print(f"  Archived {(~old_rows['run_id'].astype(str).isin(have)).sum():,} runner rows before "
                  f"{cutoff_date(today)} -> {arc.name} ({len(merged):,} rows)")
        df = df[~old]
    elif arc is None:
        old[:] = False
    df.to_csv(live_path, index=False)
    return int(old.sum())
