# Archive

Files that nothing live depends on any more. Moved here (with `git mv`, so history is kept) rather than deleted. Nothing in
`.github/workflows/` (daily, price_refresh, tab_results, gps_daily, projection_daily, the backfill_* jobs, field_discovery),
`projection/`, the frontend build or `.mcp.json` imports or runs anything in this folder.

| Folder | What it holds |
|---|---|
| `analysis/` | One-off experiments, sweeps and backtests (`wpr_*_test.py`, `wpr_*_sweep.py`, `neural_score_v*.py`, `scratch_*`, etc.) that fed decisions recorded in CLAUDE.md. Includes `signal_watch_full_period_daily_pnl.csv`. |
| `one_off_backfills/` | Backfills and fixes for the previous projection model or for data that has already been repaired. |
| `probes/` | Field probes and ad-hoc checks. |
| `tools/` | Misc helpers (`_typecheck.py`). |
| `workflows/` | Disabled or one-off workflows: the unused root `daily.yml`, the disabled `toprate_daily.yml`, `joint_model_kfold_eval.yml`, `settle_shape_check.yml`. To bring one back, copy it to `.github/workflows/`. |
| `trackers/` | The High Volume / Low Volume speed-map and jockey trackers retired 7 Oct 2026: `speedmap_jockey_tracker.py`, `tracker_history_cleanup.py` and their two CSV logs. The jobs were removed from `daily.yml`, `tab_results.yml` and `tab_results_poller.py`. Scripts in `analysis/` that import the tracker need `archive/trackers` on `PYTHONPATH`. |
| `frontend/` | Components no longer reachable from `main.tsx`: the Trackers tab (`TrackersTab.tsx`, `trackerRules.ts`), `PriceMovementChart.tsx`, `density.ts`. |

## Running an archived script

Scripts import live modules (`toprate_daily`, `wpr_projection`, `runners_io`...) and read data files by relative path, so run them from
the repo root with the root and the script's own folder on the path:

```
PYTHONPATH=.:archive/analysis python archive/analysis/<script>.py
```

CLAUDE.md entries from before this move name these scripts without the `archive/<folder>/` prefix.
