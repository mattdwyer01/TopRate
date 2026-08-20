# CLAUDE.md — TopRate project guide

Orientation for Claude Code working in this repo. Read this before making changes.

## What this project is

TopRate is a personal horse-racing analytics and betting dashboard for Australian
thoroughbred racing (TAB markets). It fetches race data, projects a Win Probability
Rating (WPR) per runner, and presents it in a single-file web dashboard. It is a
solo side project. Bet selection is manual.

Live dashboard: https://mattdwyer01.github.io/TopRate/toprate_live.html

## File map (the important ones)

- `toprate_daily.py` (~3,100 lines) — the pipeline. Fetches race data, updates
  results, flushes form history, computes WPR projection, rebuilds the HTML,
  publishes. Entry point is `main()`. Run daily by the GitHub Action.
- `toprate_html_v3.py` (~16,500 lines) — the dashboard generator. `render_html()`
  builds the HTML string plus the external data JSON. The front-end JS app lives
  inside this file as a big raw string assigned to `_JS_APP = r"""..."""`.
- `wpr_projection.py` — the WPR projection model (scikit-learn
  HistGradientBoostingRegressor, ~57 features). `build_training_frame()`,
  `project_race()`, `train_wpr_projection()`.
- `toprate_json_capture.py` — rich per-runner form capture (SvelteKit __data.json).
- `supabase_sync.py` — pushes runners + form history to Supabase each run.
- `.github/workflows/daily.yml` — the GitHub Action. THIS is the workflow that
  runs. There is a duplicate `daily.yml` in the repo ROOT that is NOT used —
  ignore it (or delete it); only `.github/workflows/daily.yml` matters.

## Data files

- `wpr_form_history.csv.gz` — accumulating per-run form history, gzipped (it
  crossed GitHub's 100MB limit as raw CSV). pandas reads/writes `.gz`
  transparently. Committed to git so it persists across Action runs.
- `toprate_runners.csv` — current runner set (one row per runner per race).
- `toprate_data.json` — the dashboard's data payload, RACES windowed to the last
  45 days (via `TOPRATE_RACES_WINDOW_DAYS`) to stay under 100MB.

## Conventions (follow these)

- NO em dashes anywhere, in code, comments, or output. Use commas or parentheses.
- Validate Python before considering a change done: `python -c "import ast;
  ast.parse(open('FILE.py').read())"`.
- Validate the dashboard JS: extract the `_JS_APP = r"""..."""` raw string to a
  file and run `node --check` on it. A syntax error there breaks the whole
  dashboard silently, so always check after editing JS.
- 1 unit = $50 in the UI.
- Keep changes minimal and targeted; this is a large single-file generator and
  broad edits are risky. Prefer small `str_replace`-style edits over rewrites.
- After editing `toprate_html_v3.py`, rebuild to verify:
  `python toprate_daily.py --rebuild-only` (rebuilds HTML from existing CSVs,
  no network fetch). Check it completes and `toprate_data.json` stays under 100MB.

## Deploy

- HTML-only changes: `deploy_html.bat`
- Full data refresh: `deploy.bat`
- Both do: git add, commit, `git pull --rebase` before push, then push.
- On rebase conflicts on generated files (`toprate_runners.csv`,
  `toprate_data.json`, `toprate_live.html`, `wpr_form_history.csv.gz`), take the
  incoming version: `git checkout --theirs <file>` then add and continue. Only
  discard generated data files, never code.

## Secrets — never commit these

- `supabase_key.txt` (service_role key) is gitignored. Never read it into output,
  never commit it, never print it. The Action uses the `SUPABASE_SERVICE_KEY`
  GitHub secret instead.
- Never print or echo any key, token, or password in output.

## Current state (migration in progress)

- The data is being migrated to Supabase (Postgres). Two tables exist and are
  loaded: `wpr_form_history` (composite key run_id+date) and `toprate_runners`
  (key run_id). The daily Action now writes to Supabase in parallel with the CSVs
  (see `supabase_sync.py` calls in `toprate_daily.py`). Schema is in
  `supabase_schema.sql`.
- The dashboard still reads `toprate_data.json` (not Supabase yet). Repointing
  the dashboard to read from Supabase is a planned future step.
- The WPR projection model is at its accuracy ceiling; extensive feature and
  structural experiments found no improvement beyond noise. Do not add model
  complexity without a fundamentally new data source. The unexplored lever is
  bet selection, not prediction accuracy.

## What to be careful about

- The dashboard is live; a broken build takes it down. Validate and rebuild
  before deploying.
- `toprate_html_v3.py` is huge. When editing the embedded JS, watch for
  brace/bracket balance; an unterminated block breaks the entire app.
- OneDrive (the repo lives in a OneDrive folder locally) can lock files during
  git operations. Not relevant in the cloud VM, but noted.
