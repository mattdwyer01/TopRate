"""
supabase_sync.py - push dataframes to Supabase from the daily pipeline.

Additive and FAIL-SAFE: every function is wrapped so a Supabase problem logs a
warning and returns without raising - the daily run must never break because
of a sync issue. Runs ALONGSIDE the existing CSV pipeline (does not replace
it), so Supabase is a parallel copy we can verify before cutting over.

Key comes from the SUPABASE_SERVICE_KEY env var (a GitHub Actions secret in
the workflow) or, locally, from supabase_key.txt. Never hard-code it.
"""
import os
import json
import time
import pandas as pd
import requests

SUPABASE_URL = "https://lvhgcduztkwkibrrkyqp.supabase.co"
KEY_FILE = "supabase_key.txt"
BATCH = 500


def _key():
    k = os.environ.get("SUPABASE_SERVICE_KEY", "").strip()
    if k:
        return k
    if os.path.exists(KEY_FILE):
        return open(KEY_FILE).read().strip()
    return None


def _upsert(table, df, label):
    """Upsert every row of df into `table`. Fail-safe: logs and returns on any
    error rather than raising. Column names are lowercased to match Postgres."""
    key = _key()
    if not key:
        print(f"  [supabase] no key (SUPABASE_SERVICE_KEY / {KEY_FILE}); "
              f"skipping {label}")
        return
    if df is None or len(df) == 0:
        print(f"  [supabase] {label}: nothing to sync")
        return
    df = df.copy()
    df.columns = [c.lower() for c in df.columns]
    df = df.astype(object).where(pd.notnull(df), None)
    headers = {
        "apikey": key,
        "Authorization": f"Bearer {key}",
        "Content-Type": "application/json",
        "Prefer": "resolution=merge-duplicates,return=minimal",
    }
    endpoint = f"{SUPABASE_URL}/rest/v1/{table}"
    n = len(df)
    sent = 0
    t0 = time.time()
    try:
        for i in range(0, n, BATCH):
            chunk = df.iloc[i:i + BATCH]
            recs = json.loads(json.dumps(chunk.to_dict(orient="records"),
                                         default=str))
            r = requests.post(endpoint, headers=headers, json=recs, timeout=60)
            if r.status_code not in (200, 201, 204):
                print(f"  [supabase] {label}: HTTP {r.status_code} at row {i} "
                      f"- {r.text[:200]}")
                return
            sent += len(recs)
        print(f"  [supabase] {label}: {sent:,} rows upserted "
              f"({time.time()-t0:.0f}s)")
    except Exception as e:
        print(f"  [supabase] {label}: sync error ({e}) - continuing")


def sync_runners(runners_df):
    """Upsert the day's runners to toprate_runners (key run_id)."""
    _upsert("toprate_runners", runners_df, "runners")


def sync_form_history(new_df):
    """Upsert newly-captured form rows to wpr_form_history (key run_id,date).
    Pass the NEW rows from this run, not the full accumulated history, so the
    push stays small and fast."""
    if new_df is None or len(new_df) == 0:
        return
    df = new_df.copy()
    df.columns = [c.lower() for c in df.columns]
    if "run_id" in df.columns and "date" in df.columns:
        df = df.drop_duplicates(subset=["run_id", "date"], keep="last")
    _upsert("wpr_form_history", df, "form_history")
