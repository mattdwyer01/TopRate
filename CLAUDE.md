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
  results, flushes form history, computes WPR projection, refreshes
  `toprate_data.json`, publishes. Entry point is `main()`. Run daily by the
  GitHub Action, and every 5 minutes (prices only) by
  `.github/workflows/price_refresh.yml`.
- `frontend/` — the LIVE dashboard: a React + TypeScript + Vite + Tailwind app.
  `npm run build` (from `frontend/`) produces a single self-contained
  `frontend/dist/index.html` via `vite-plugin-singlefile`; that file is what
  gets copied to `toprate_live.html` at the repo root and deployed (see
  Deploy below). Source lives in `frontend/src/` — `api/adapter.ts` maps the
  raw `toprate_data.json` payload (abbreviated keys, see `types/data.ts`) onto
  clean domain types (`types/domain.ts`) that components consume.
  `toprate_live.html` is NOT rebuilt automatically on a data refresh - it's a
  static artifact that fetches `toprate_data.json` at runtime, so it only
  needs rebuilding when `frontend/src` changes.
- `toprate_html_v3.py` (~16,500 lines) — the OLD dashboard generator (Python
  string-templated HTML + a big embedded JS blob). No longer used to produce
  the live `toprate_live.html` (see `frontend/` above) - kept only as a
  reference/fallback until the new frontend has had time to prove itself.
  `render_html()` is still called by `toprate_daily.py`'s `rebuild_html()` for
  its data-JSON half (the payload the new frontend fetches); its HTML-string
  return value is discarded. Do not build new dashboard features here.
- `wpr_projection.py` — the WPR projection model: an additive model
  (`base + sum(ADJ_TERMS)`), where `base` is a 50/50 blend of TopRate's own
  rating (`wpr_nett`) and recency-weighted recent form (`ewm3`), falling back
  through recent-form averages. Both base and the summed adjustment go
  through their own separately-fitted calibration slopes (`_compute_base()`/
  `_calibrate_base()`, `_CALIB_ADJ_SLOPE`) before being added - the base
  slope is itself piecewise (bottom 10%/middle 70%/top 20% of raw base each
  fit separately, since a single global slope under/over-shrinks the tails).
  `build_training_frame()`, `project_race()`, `train_wpr_projection()`,
  `describe()` (the plain-English projection explanation shown in the
  dashboard's runner detail panel).
- `toprate_json_capture.py` — rich per-runner form capture (SvelteKit __data.json).
- `.github/workflows/daily.yml` — the GitHub Action. THIS is the workflow that
  runs. There is a duplicate `daily.yml` in the repo ROOT that is NOT used —
  ignore it (or delete it); only `.github/workflows/daily.yml` matters.
- `.github/workflows/price_refresh.yml` — runs every 5 min during AU racing
  hours, refreshes prices and `toprate_data.json` only (via
  `toprate_price_refresh.py` → `toprate_daily.py`'s `rebuild_html()`). Never
  touches `toprate_live.html`.
- `tab_results_poller.py` / `.github/workflows/tab_results.yml` — fast,
  provisional per-race results, plus track condition/rail updates, from
  TAB's public racing API (see `TAB_API_NOTES.md`). Results close the gap
  where the authoritative feed above can't resolve a race until its whole
  meeting finishes. Runs on a self-hosted GitHub Actions runner registered
  from a real Australian machine — currently a Vultr Melbourne instance
  (TAB geo-blocks and TLS-fingerprints most cloud/VPS hosts, confirmed
  empirically against GitHub-hosted runners specifically, but Vultr AU has
  been confirmed working in practice despite that general rule; a home
  machine works too, just less conveniently always-on). Reads everything
  straight off the cheap meeting-list endpoint (raceStatus/results[]/
  trackCondition/railPosition are already embedded per meeting/race, no
  drill-down into race detail needed), matching case-insensitively since
  TAB returns AU venues in ALL CAPS. Writes finish_position/won/placed
  (per runner) and going/track_grading/rail_position (per meeting, applied
  to every runner at that venue+date); never resulted/wpr_actual/
  comments_* — those stay exclusively `update_results()`'s job. going/
  track_grading/rail_position updates are DISPLAY-ONLY for now: they
  refresh what the dashboard shows but do NOT trigger a WPR ratings
  recompute (`compute_wpr_projection()` only runs in the full daily
  pipeline, not `--rebuild-only` — deliberately deferred, see Current
  state below, rather than assumed cheap/safe to wire in immediately).
  Triggered externally (cron-job.org → workflow_dispatch, same pattern as
  `price_refresh.yml`), not GitHub's own `schedule:`.

## Data files

- `wpr_form_history.csv.gz` — accumulating per-run form history, gzipped (it
  crossed GitHub's 100MB limit as raw CSV). pandas reads/writes `.gz`
  transparently. Committed to git so it persists across Action runs.
- `toprate_runners.csv` — current runner set (one row per runner per race).
- `toprate_data.json` — the dashboard's data payload, RACES windowed to the last
  25 days (via `TOPRATE_RACES_WINDOW_DAYS`, reduced from 30 Sep 2026 after the
  30-day payload grew to 94.4MB) to stay under GitHub's 100MB file limit.

## Conventions (follow these)

- NO em dashes anywhere, in code, comments, or output. Use commas or parentheses.
- Validate Python before considering a change done: `python -c "import ast;
  ast.parse(open('FILE.py').read())"`.
- Dashboard UI/feature changes go in `frontend/src/` (React + TypeScript), not
  `toprate_html_v3.py` (see File map). After editing, from `frontend/`:
  `npx tsc -b` (type-check) and `npm run build` (must produce a single
  `dist/index.html`) before considering a change done.
- 1 unit = $50 in the UI.
- Keep changes minimal and targeted; `toprate_daily.py` and `wpr_projection.py`
  are large files and broad edits are risky. Prefer small, targeted edits over
  rewrites.
- After editing anything that touches the data payload (`toprate_daily.py`,
  `wpr_projection.py`), rebuild to verify: `python toprate_daily.py
  --rebuild-only` (refreshes `toprate_data.json` from existing CSVs, no
  network fetch, and does NOT touch `toprate_live.html`). Check it completes
  and `toprate_data.json` stays under 100MB.

## Deploy

- Dashboard UI changes: `deploy_html.bat` — builds `frontend/`, publishes the
  result as `toprate_live.html`, no data fetch.
- Full data refresh: `deploy.bat` — fetches fresh race data via
  `toprate_daily.py`; does NOT rebuild `toprate_live.html` (it's a static
  frontend build, only refreshed by `deploy_html.bat` or a manual `npm run
  build` + copy to `toprate_live.html` at repo root).
- Both do: git add, commit, `git pull --rebase` before push, then push.
- On rebase conflicts on generated files (`toprate_runners.csv`,
  `toprate_data.json`, `toprate_live.html`, `wpr_form_history.csv.gz`), take the
  incoming (remote) version. Only discard generated data files, never code.
  - **Don't resolve this via `--ours`/`--theirs` from memory - verify which
    side is which first.** `--ours`/`--theirs` are INVERTED between `git
    rebase` (this repo's flow is `git pull --rebase`, see above) and a
    normal `git merge`: in a rebase, `--ours` is the upstream/incoming
    commit and `--theirs` is your own local commit being replayed - the
    opposite of merge semantics. Getting this backwards either direction
    causes real damage (see both incidents below - one used `--theirs`
    intending "incoming" and got local by luck, the other used `git show
    HEAD:<file>` intending "incoming" and got local for real, silently
    losing data). The reliable fix: don't trust either flag name blind -
    confirm the actual incoming content first with `git show
    origin/main:<file>` (or `FETCH_HEAD:<file>`), and confirm what you
    kept afterward with `git show HEAD:<file>`, rather than assuming a
    flag means what it means in the other kind of conflict.
  - This means **the incoming/remote content, always** — never "my local
    rebuild/backfill took longer to compute so it must be more valuable."
    A real incident (Sep 2026): resolving a merge with `git show
    HEAD:<file>` (i.e. keeping local/ours) across two consecutive merges
    reverted today's race field from an already-scratched, final 583
    runners back to a stale 1,049-runner pre-scratch snapshot, and
    silently deleted an entire freshly-pre-fetched race day (2026-09-03,
    341 rows) that only existed in the incoming version. Prices
    self-heal on the next refresh; field composition (scratches, declared
    fields, newly pre-fetched days) does not — there is no "next cycle" that
    fixes a reverted field, only a human noticing the live site looks wrong.
    If a local compute (retrain, backfill, recomputed projections) needs to
    survive a merge, the correct order is: take the incoming version for
    the conflicted file, THEN re-run your own recompute on top of that
    fresher base - never keep your own snapshot of the base data itself.
    (A faster variant when the recompute itself was expensive and its
    result still exists in git history under an orphaned/rebased-away
    commit: pull the already-computed columns back out with `git show
    <old-sha>:<file>` and field-merge them onto the fresher base by row
    key, instead of re-running the full computation from scratch.)

## Secrets — never commit these

- Never print or echo any key, token, or password in output.

## Current state

- Supabase was tried as a parallel Postgres copy of `toprate_runners` and
  `wpr_form_history` (with an eye toward eventually repointing the dashboard
  at it), then dropped (Sep 2026) - it never actually served the live
  dashboard (which reads `toprate_data.json` directly, unchanged throughout),
  cost real money and ~5-10 min of extra daily-run time for syncing, and was
  the source of most of the bugs chased around that time (schema drift, a
  bigint-cast bug, a silently-abandoned background sync, a storage-quota
  overage). If Supabase (or another external DB) is wanted again, treat it as
  a fresh decision rather than resurrecting the old `supabase_sync.py` - the
  git history has it (search for "Fix two Supabase sync bugs" and nearby
  commits) if the old approach is a useful reference. A collaborator who had
  read-only Supabase dashboard access now gets the CSVs directly instead
  (`toprate_runners.csv`, `wpr_form_history.csv.gz`) via repo access.
- The WPR projection model is at its accuracy ceiling; extensive feature and
  structural experiments found no improvement beyond noise. Do not add model
  complexity without a fundamentally new data source. The unexplored lever is
  bet selection, not prediction accuracy.
- `tab_results_poller.py` (Sep 2026) refreshes `going`/`track_grading`/
  `rail_position` intraday from TAB, but deliberately does NOT trigger a WPR
  ratings recompute when they change, even though `going` already feeds
  `wpr_going` as a model input - this isn't the "no model complexity"
  caution above (going is already a live input, not a new feature), it's
  that `compute_wpr_projection()` only runs in the full daily pipeline, is
  untimed standalone, and running it on a 5-min intraday cadence on a
  1 vCPU/2GB box is new, unvalidated load on the one part of the codebase
  explicitly flagged as risky to touch casually. Time it standalone and
  decide deliberately before wiring this in, rather than assuming it's
  cheap. Same reasoning applies to using TAB's `fixedOdds` to replace
  `price_refresh.yml`: that job currently runs on free GitHub-hosted infra,
  fully decoupled from whichever AU machine hosts the self-hosted runner;
  routing prices through TAB too would mean the AU machine going down takes
  out results AND prices AND conditions at once instead of just results
  freshness - run TAB prices in parallel against the existing feed first to
  check accuracy/completeness before considering a cutover, don't swap it
  in blind.
- **IMPORTANT for whoever next runs `train_wpr_projection()`/a full retrain
  (Sep 2026)**: `wpr_form_history.csv.gz` just had a major dedup bug fixed.
  Its dedup key used to include `formNumber`, which looks like a stable
  "which run number in career" index but isn't (it's relative to whatever
  race triggered the capture, so the same physical run got a different
  formNumber on every re-scrape). Result: 73% of the file (448,908/613,477
  rows) were undetected duplicate captures of the same (horse, date) run,
  80% of those with a genuinely different `wpr` value between copies - not
  cosmetic. Fixed in `flush_wpr_form_history()` (key is now `(horse_id-or-
  name, date)` only) and the existing file cleaned via
  `wpr_form_history_dedup_cleanup.py` (613,477 -> 324,026 rows, file
  79.3MB -> 39.9MB). Every own-history ADJ_TERM and the base signals
  (`ewm5`, `career_avg`, `best3`) average over a horse's own row series
  from this file, so a horse's older runs being silently double/triple-
  counted (worse the more it's raced since) was a systematic bias, not
  cosmetic bloat - this was NOT re-validated end-to-end against the live
  model tonight (too large an undertaking at the time, see chat). **The
  next retrain should explicitly compare held-out MAE/strike-rate before
  vs. after this fix** (the pre-fix numbers are the ones already documented
  throughout this file and the git history) rather than assuming they still
  hold - if a base-calc or ADJ_TERM conclusion shifts meaningfully once fed
  correct, undeduplicated-by-formNumber data, that supersedes the earlier
  finding, not the other way around.
- The dashboard frontend rebuild (Python-templated HTML → React/Vite, see File
  map) is in progress, phased, and further along than "Phase 1" implies -
  most of what's genuinely useful without bet tracking is already live:
  Race tab (meetings grid, race detail, runner detail modal, speed map,
  horse/jockey/trainer search via the header search icon or `/`), Review tab
  (predicted-vs-actual accuracy: point/rank/margin stats, calibration chart,
  breakdowns by distance/going/venue, cross-linked to the runner it's
  about), Settings modal (WPR $ price sharpness override, workflow_dispatch
  "Fetch data" buttons, cross-device sync of overrides/preferences via a
  private GitHub Gist - see `lib/githubSync.ts`). Deliberately NOT built,
  per explicit user decision: a P&L/bet-tracking tab - there's no bet log,
  and one wasn't wanted without real bet tracking behind it.

## What to be careful about

- The dashboard is live; a broken build takes it down. Validate and rebuild
  before deploying (`npx tsc -b && npm run build` in `frontend/`; the build
  must succeed and `dist/index.html` must load `toprate_data.json`
  correctly - verify against real data before pushing, not just a clean
  compile).
- `toprate_html_v3.py` is legacy/reference only now (see File map) - don't add
  new dashboard features there. It's still called for its data-JSON output,
  so don't delete it without first confirming what (if anything) still needs
  extracting from it into `toprate_daily.py` directly.
- OneDrive (the repo lives in a OneDrive folder locally) can lock files during
  git operations. Not relevant in the cloud VM, but noted.
