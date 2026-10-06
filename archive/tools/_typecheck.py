"""_typecheck.py - print each column's inferred type + sample values.

Run:  python _typecheck.py
Paste the whole output back so the Supabase table can be typed correctly
in one pass (no stop-and-fix on load).
"""
import pandas as pd

CSV = "toprate_runners.csv"
d = pd.read_csv(CSV, dtype=str, low_memory=False)
print(f"{len(d):,} rows, {len(d.columns)} columns\n")

for c in d.columns:
    v = d[c].dropna()
    v = v[v.str.strip() != ""]
    if len(v) == 0:
        print(f"{c:24} | EMPTY (all null)")
        continue
    num = pd.to_numeric(v, errors="coerce").notna().all()
    # detect integer-only vs float
    kind = "text"
    if num:
        asf = pd.to_numeric(v, errors="coerce")
        kind = "int" if (asf.dropna() % 1 == 0).all() else "float"
    # detect boolean
    lowset = set(v.str.lower().unique())
    if lowset <= {"true", "false"}:
        kind = "bool"
    print(f"{c:24} | {kind:5} | {list(v.unique()[:3])}")
