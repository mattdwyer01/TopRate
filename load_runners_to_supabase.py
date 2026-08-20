"""
load_runners_to_supabase.py - bulk-load toprate_runners.csv into the Supabase
table `toprate_runners`, in batches, upsert on run_id (safe to re-run).

Uses only `requests`. Reads the service_role key from supabase_key.txt (same
secret file as the form-history loader - keep it gitignored).

RUN:  python load_runners_to_supabase.py
"""
import os
import sys
import json
import time
import pandas as pd
import requests

SUPABASE_URL = "https://lvhgcduztkwkibrrkyqp.supabase.co"
TABLE = "toprate_runners"
CSV = "toprate_runners.csv"
KEY_FILE = "supabase_key.txt"
BATCH = 500

if not os.path.exists(KEY_FILE):
    sys.exit(f"Missing {KEY_FILE} (service_role key, one line, gitignored).")
service_key = open(KEY_FILE).read().strip()
if not service_key or len(service_key) < 20:
    sys.exit(f"{KEY_FILE} does not look like a valid key.")

headers = {
    "apikey": service_key,
    "Authorization": f"Bearer {service_key}",
    "Content-Type": "application/json",
    "Prefer": "resolution=merge-duplicates,return=minimal",
}
endpoint = f"{SUPABASE_URL}/rest/v1/{TABLE}"

print(f"Reading {CSV} ...", flush=True)
df = pd.read_csv(CSV, dtype=str, low_memory=False)   # read as text; Postgres casts
df.columns = [c.lower() for c in df.columns]
n_raw = len(df)
df = df.drop_duplicates(subset=["run_id"], keep="last").reset_index(drop=True)
n = len(df)
print(f"  {n_raw:,} rows -> {n:,} after dedup on run_id, {len(df.columns)} columns",
      flush=True)

# empty string -> None (SQL NULL); pandas read everything as str so NaN are the
# genuinely-missing cells
df = df.where(pd.notnull(df), None)
df = df.replace({"": None})

t0 = time.time()
sent = 0
fails = []
for i in range(0, n, BATCH):
    chunk = df.iloc[i:i + BATCH]
    records = json.loads(json.dumps(chunk.to_dict(orient="records"), default=str))
    r = requests.post(endpoint, headers=headers, json=records, timeout=60)
    if r.status_code not in (200, 201, 204):
        fails.append((i, r.status_code, r.text[:300]))
        print(f"  batch {i}: HTTP {r.status_code} - {r.text[:220]}", flush=True)
        print("\nStopping on first error so we can fix it. Upsert makes re-run safe.")
        break
    sent += len(records)
    if (i // BATCH) % 10 == 0:
        print(f"  ... {sent:,}/{n:,} rows ({time.time()-t0:.0f}s)", flush=True)

print(f"\nDone: {sent:,}/{n:,} rows upserted in {time.time()-t0:.0f}s.")
if fails:
    print(f"First error: {fails[0]}")
else:
    print("No errors. Verify: select count(*) from toprate_runners;")
