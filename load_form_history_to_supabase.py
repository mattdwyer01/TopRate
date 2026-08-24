"""
load_form_history_to_supabase.py - bulk-load wpr_form_history.csv.gz into the
Supabase table `wpr_form_history`, in batches, with progress, using upsert on
run_id (safe to re-run: existing rows update, new rows insert).

Uses only `requests` (no supabase client needed) against the PostgREST API.

SETUP (one time):
  Your service_role key is a SECRET. Do NOT paste it anywhere public or commit
  it. Put it in a local file the repo ignores. From the TopRate folder:

    (create a file called  supabase_key.txt  containing ONLY the
     service_role key on a single line - get it from
     Supabase > Settings > API > service_role)

  Make sure supabase_key.txt is gitignored (this script checks and warns).

RUN:
  python load_form_history_to_supabase.py
"""
import os
import sys
import json
import time
import pandas as pd
import requests

SUPABASE_URL = "https://lvhgcduztkwkibrrkyqp.supabase.co"
TABLE = "wpr_form_history"
CSV = "wpr_form_history.csv.gz"
KEY_FILE = "supabase_key.txt"
BATCH = 500

# ── load the secret key from the local file (never hard-coded) ──
if not os.path.exists(KEY_FILE):
    sys.exit(f"Missing {KEY_FILE}. Create it containing ONLY your service_role "
             f"key (Supabase > Settings > API). Keep it out of git.")
service_key = open(KEY_FILE).read().strip()
if not service_key or len(service_key) < 20:
    sys.exit(f"{KEY_FILE} does not look like a valid key.")

# gentle gitignore safety check
if os.path.exists(".gitignore"):
    gi = open(".gitignore").read()
    if KEY_FILE not in gi:
        print(f"WARNING: {KEY_FILE} is not in .gitignore. Add it so your secret "
              f"key is never committed. Continuing anyway.")

headers = {
    "apikey": service_key,
    "Authorization": f"Bearer {service_key}",
    "Content-Type": "application/json",
    # upsert: on primary-key conflict, update the row instead of erroring
    "Prefer": "resolution=merge-duplicates,return=minimal",
}
endpoint = f"{SUPABASE_URL}/rest/v1/{TABLE}"

print(f"Reading {CSV} ...", flush=True)
df = pd.read_csv(CSV, low_memory=False)
# Postgres folded the column names to lowercase at table creation, so match that
df.columns = [c.lower() for c in df.columns]
n_raw = len(df)
# The unique key is (run_id, date): each run_id is a horse's form-capture event
# that dumps one row per historical race date. Dedupe to one row per
# (run_id, date), keeping the last occurrence, so the upsert's ON CONFLICT key
# is respected and no batch contains the same key twice.
df = df.drop_duplicates(subset=["run_id", "date"], keep="last").reset_index(drop=True)
n = len(df)
print(f"  {n_raw:,} rows -> {n:,} after dedup on (run_id, date), "
      f"{len(df.columns)} columns", flush=True)

# Integer/bigint columns in the Postgres schema. pandas has no nullable-int
# dtype by default, so a column with even one missing value anywhere in the
# 444k rows gets read as float64 for the WHOLE column - a real barrier of 1
# becomes numpy.float64(1.0). json.dumps can't serialise a numpy float, so
# the `default=str` fallback below stringifies it to "1.0" - which Postgres
# then rejects for an integer column ("1.0" is not valid integer syntax,
# it wants "1"). Cast these explicitly to Python int (or None) so they
# serialise as plain JSON numbers instead.
INT_COLS = ["run_id", "horse_id", "formnumber", "racenumber", "distance", "barrier"]


def _to_int_or_none(v):
    if v is None or (isinstance(v, float) and v != v):  # NaN
        return None
    try:
        return int(float(v))
    except (TypeError, ValueError):
        return None


for col in INT_COLS:
    if col in df.columns:
        df[col] = df[col].apply(_to_int_or_none)

# pandas NaN -> None so it becomes SQL NULL in JSON
df = df.astype(object).where(pd.notnull(df), None)

t0 = time.time()
sent = 0
fails = []
for i in range(0, n, BATCH):
    chunk = df.iloc[i:i + BATCH]
    records = chunk.to_dict(orient="records")
    # json can't serialise numpy types cleanly in edge cases; coerce via json
    payload = json.loads(json.dumps(records, default=str))
    r = requests.post(endpoint, headers=headers, json=payload, timeout=60)
    if r.status_code not in (200, 201, 204):
        fails.append((i, r.status_code, r.text[:300]))
        print(f"  batch {i}: HTTP {r.status_code} - {r.text[:200]}", flush=True)
        # stop on the first error so we can diagnose rather than spam failures
        if len(fails) >= 1:
            print("\nStopping on first error so we can fix it. Nothing above this "
                  "batch is lost - upsert makes re-running safe.")
            break
    else:
        sent += len(records)
    if (i // BATCH) % 10 == 0:
        print(f"  ... {sent:,}/{n:,} rows ({time.time()-t0:.0f}s)", flush=True)

print(f"\nDone: {sent:,}/{n:,} rows upserted in {time.time()-t0:.0f}s.")
if fails:
    print(f"{len(fails)} batch error(s). First: {fails[0]}")
    print("Fix the cause and re-run - upsert means already-loaded rows are "
          "just updated, not duplicated.")
else:
    print("No errors. Verify in Supabase: select count(*) from wpr_form_history;")
