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
import re
import json
import time
import pandas as pd
import requests

SUPABASE_URL = "https://lvhgcduztkwkibrrkyqp.supabase.co"
KEY_FILE = "supabase_key.txt"
SCHEMA_FILE = os.path.join(os.path.dirname(__file__), "supabase_schema.sql")
BATCH = 500

_schema_columns_cache = {}


def _key():
    k = os.environ.get("SUPABASE_SERVICE_KEY", "").strip()
    if k:
        return k
    if os.path.exists(KEY_FILE):
        return open(KEY_FILE).read().strip()
    return None


def _schema_columns(table):
    """Column names supabase_schema.sql declares for `table` - the repo's own
    authoritative record of the live schema (see its header comment). Used
    to filter outgoing rows so a CSV column the table doesn't have yet can't
    take down the whole day's sync (see the Aug 2026 migration note in that
    file: exactly this happened, silently, for weeks - PostgREST rejects an
    upsert containing any unknown column, at the level of the whole request,
    not just that column)."""
    if table in _schema_columns_cache:
        return _schema_columns_cache[table]
    cols = None
    try:
        sql = open(SCHEMA_FILE).read()
        block = sql.split(f"create table if not exists {table} (")[1].split(");")[0]
        cols = set(re.findall(r"^\s*([a-zA-Z_][a-zA-Z0-9_]*)\s+\w", block, re.M))
    except Exception as e:
        print(f"  [supabase] couldn't read {table}'s schema from "
              f"{SCHEMA_FILE} ({e}) - not filtering columns")
    _schema_columns_cache[table] = cols
    return cols


def _upsert(table, df, label):
    """Upsert every row of df into `table`. Fail-safe: logs and returns on any
    error rather than raising. Column names are lowercased to match Postgres.
    Columns the table's schema (supabase_schema.sql) doesn't declare are
    dropped before sending, rather than letting them fail the whole batch."""
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

    known = _schema_columns(table)
    if known:
        extra = [c for c in df.columns if c not in known]
        if extra:
            print(f"  [supabase] {label}: dropping {len(extra)} column(s) not "
                  f"in {table}'s schema ({', '.join(extra[:8])}"
                  f"{'...' if len(extra) > 8 else ''}) - add them to "
                  f"supabase_schema.sql to sync")
            df = df.drop(columns=extra)

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
    failed_batches = []
    t0 = time.time()
    try:
        for i in range(0, n, BATCH):
            chunk = df.iloc[i:i + BATCH]
            recs = json.loads(json.dumps(chunk.to_dict(orient="records"),
                                         default=str))
            r = requests.post(endpoint, headers=headers, json=recs, timeout=60)
            if r.status_code not in (200, 201, 204):
                failed_batches.append(i)
                print(f"  [supabase] {label}: HTTP {r.status_code} at row {i} "
                      f"- {r.text[:200]}")
                # Don't abort the whole sync over one bad batch - a single
                # transient error (or one bad row) used to zero out every
                # other row for the day too. Move on to the next batch.
                continue
            sent += len(recs)
        status = "OK" if not failed_batches else f"{len(failed_batches)} batch(es) failed"
        print(f"  [supabase] {label}: {sent:,}/{n:,} rows upserted "
              f"({time.time()-t0:.0f}s) - {status}")
    except Exception as e:
        print(f"  [supabase] {label}: sync error ({e}) after {sent:,}/{n:,} "
              f"rows - continuing")


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
    # formnumber is an `integer` column in Postgres, but pandas upgrades it
    # to float64 the moment any row is missing one (NaN forces the whole
    # column to float) - it then serializes as "1.0", and Postgres's integer
    # input parser rejects the decimal point outright ("invalid input syntax
    # for type integer"), which used to fail this table's entire sync.
    # Nullable Int64 keeps real NaNs as null while writing whole numbers.
    if "formnumber" in df.columns:
        df["formnumber"] = pd.array(df["formnumber"], dtype="Int64")
    _upsert("wpr_form_history", df, "form_history")
