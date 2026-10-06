# Trip map

Projected running line (gap behind the leader, width from the rail, about 800m from home) for upcoming races at
GPS-tracked courses (VIC, SA, QLD). Shown in the Race tab as the "Trip map" pill next to Grid / Bar.

- `build_trip_map.py` builds `trip_map.json` at the repo root. Run it after the daily GPS job; it needs
  `data/gps/*.parquet`, `race_results_*.csv.gz` and `toprate_runners.csv`. About 8 minutes. It is NOT yet wired
  into any GitHub workflow, so `trip_map.json` only refreshes when the script is run and the file committed.
- The page reads `trip_map.json` (`frontend/src/lib/tripMap.ts`) and draws it in `frontend/src/features/race/TripMap.tsx`.
  A race without declared barriers, or at a course with no GPS history, simply has no Trip map pill.

Held-out check (train before 2025, score 2025 onward, fields of 8+): within-race correlation of forecast vs measured
gap is 0.51 (QLD) and 0.50 (VIC/SA); width 0.71 (QLD, width at 800m) and 0.42 (VIC/SA, whole-run average width).
Typical single-horse error about 2.6 lengths; width error 1.6m (QLD) and 3.5m (VIC/SA).

What it is not: it does not feed Proj or Combo. In testing, the position forecasts added nothing to the rating model
beyond a tiny gain, and nothing to winner selection beyond the market price.
