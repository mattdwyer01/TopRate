# bet_log (retired Oct 2026)

`bet_log.py` was the live paper-betting log (bets frozen before the jump, settled on TAB dividends), driven by the old Racing Model's
`racing_model.json` and the old 3/5 gap lines. Retired because the new projection model does not beat the market (see CLAUDE.md), so the
rules it tested no longer apply. Files here: the script, `bets_log.csv/json`, `value_log.csv`, and the last `racing_model.json`.

To run it again: copy `bet_log.py` and `racing_model.json` back to the repo root and re-add the import and `bet_log.update(...)` call in
`tab_results_poller.py` plus the staging lines in `tab_results.yml` (see git history before this change).

The racing-model repo's `dashboard.yml` may still commit a fresh `racing_model.json` to the repo root; nothing reads it. Disable that job
in the racing-model repo to stop it.
