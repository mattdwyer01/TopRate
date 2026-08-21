"""One-off check: how much history does Autumn Glow have captured now,
after the wpr_form_history depth backfill and scrape_date fix.

NO EM DASHES policy: hyphens only in this file.
"""
import pandas as pd

df = pd.read_csv('wpr_form_history.csv.gz', dtype={'horse_id': str})
ag = df[df['horse'] == 'Autumn Glow'][['date', 'wpr', 'track', 'scrape_date']].sort_values('date')
print(ag.to_string(index=False))
print(f"\n{len(ag)} runs captured")
print(f"distinct scrape_date values: {sorted(ag['scrape_date'].unique())}")
