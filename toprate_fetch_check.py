"""Read-only check of toprate_race_fetch.py output (14 Oct 2026): field completeness, why wpr_nett is blank, and how the rows join to runners.csv.
Usage: python toprate_fetch_check.py [data/tr_fields]"""
import json
import re
import sys
from pathlib import Path

import pandas as pd

src = Path(sys.argv[1] if len(sys.argv) > 1 else "data/tr_fields")
rows = []
for f in sorted(src.glob("*.json")):
    rows += json.loads(f.read_text())["rows"]
t = pd.DataFrame(rows).drop(columns=["last_start", "accepted_at"], errors="ignore")
print(f"{len(t)} runners, {t.race_id.nunique()} races, dates {sorted(t.date.unique())}")
live = t[~t.scratched]
print("not scratched:", len(live))

print("\ncompleteness (non-null share of non-scratched runners):")
for c in ["wpr_nett", "speed_rating", "toprate_rating", "pfm_score", "jockey_rating", "handicap_rating", "fixed_win_price",
          "fixed_win_opening", "dslr", "is_spell", "runs_from_spell", "weight", "barrier", "career_starts"]:
    print(f"  {c:18s} {live[c].notna().mean():6.1%}")

blank = live[live.wpr_nett.isna()]
print(f"\nwpr_nett blank: {len(blank)} of {len(live)}")
print("  of those, career_starts == 0:", int((blank.career_starts == 0).sum()),
      "| career_starts null:", int(blank.career_starts.isna().sum()),
      "| speed_rating 0/null:", int((blank.speed_rating.fillna(0) == 0).sum()),
      "| toprate_rating null:", int(blank.toprate_rating.isna().sum()))
have = live[live.wpr_nett.notna()]
print("  wpr_nett range (have):", have.wpr_nett.min(), have.wpr_nett.max(), "| mean", round(have.wpr_nett.mean(), 1))
print("  having wpr_nett but career_starts == 0:", int((have.career_starts == 0).sum()))


def norm(s):
    return re.sub(r"[^a-z0-9]", "", str(s).lower())


r = pd.read_csv("runners.csv", low_memory=False)
r = r[r.date.isin(t.date.unique())].copy()
r["k"] = r.date + "|" + r.venue.map(norm) + "|" + r.race.astype(int).astype(str) + "|" + r.horse.map(norm)
t["k"] = t.date + "|" + t.venue.map(norm) + "|" + t.race_no.astype(int).astype(str) + "|" + t.horse.map(norm)
print(f"\njoin to runners.csv: {len(r)} live rows, {len(t)} toprate rows")
m = t.merge(r[["k", "tab_number", "scratched"]], on="k", how="left", suffixes=("", "_live"), indicator=True)
print("  toprate rows matched:", int((m._merge == "both").sum()), f"({(m._merge == 'both').mean():.1%})")
print("  live rows matched   :", int(r.k.isin(t.k).sum()), f"({r.k.isin(t.k).mean():.1%})")
mm = m[m._merge == "both"]
print("  tab_number agrees   :", f"{(mm.tab_number == mm.tab_number_live).mean():.1%}")
tv, rv = set(t.venue.map(norm)), set(r.venue.map(norm))
print("  venues only in toprate:", sorted(tv - rv), "| only in live:", sorted(rv - tv))
um = m[m._merge == "left_only"]
print("  unmatched toprate by venue:", um.venue.value_counts().head(8).to_dict())
