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
  TAB returns AU venues in ALL CAPS. Writes finish_position/won/placed/
  interim_resulted (per runner) and going/track_grading/rail_position (per
  meeting, applied to every runner at that venue+date); never resulted/
  wpr_actual/comments_* — those stay exclusively `update_results()`'s job
  (interim_resulted is a separate column that flips the dashboard's
  race-level "done" display flag early; resulted itself, and everything
  keyed off it, still waits for the authoritative pass). A real going
  change DOES trigger a WPR ratings recompute, scoped to just the
  meeting(s) that changed (`compute_wpr_projection(..., target_venues=...)`
  — see Current state below for the measured cost that made this safe to
  wire in). Also writes fixed_win_price/scratched (per runner) from a
  race's own fixedOdds, bounded to races starting within ~2hr (same window
  `toprate_price_refresh.py` already uses) — a SECOND, independent price
  source alongside that job's existing 5-min refresh, not a replacement of
  it (see Current state for why a cutover is a separate decision). A plain
  results/prices/scratches cycle publishes via a fast direct JSON patch
  (`toprate_daily.patch_data_json()`), not the full `--rebuild-only`
  pipeline — only a going change still forces that (see Current state).
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
- `horse_history/<date>_<venue-slug>.json` (Sep 2026) — one file per race
  meeting, written by `toprate_daily.py`'s `build_horse_history_files()`
  (called from `rebuild_html()`), holding every horse racing at that meeting's
  FULL (uncapped) form history, keyed by lowercased horse name. Static
  replacement for the decommissioned Supabase live fetch the frontend's
  "Recent runs" panel used to depend on for anything past the embedded
  payload's last-10 cap (see Current state below) - the frontend fetches the
  one meeting file for a race on demand (`lib/meetingFormHistory.ts`), not
  the whole directory. File-per-meeting (not file-per-horse - would be
  thousands of tiny files - or one combined file - the exact mistake that
  blew `toprate_data.json` past the 100MB limit once already) was chosen
  after measuring real numbers: 222 files in a 25-day window, largest ~1MB,
  ~80MB total. Only rewrites a file when its content changed and removes
  stale meeting files that rolled out of the window, so the frequent
  `price_refresh.yml`/`tab_results.yml` cycles don't churn ~200 unchanged
  files every run.

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
  `toprate_data.json` is marked `binary` in `.gitattributes` (Sep 2026) so this
  resolves instantly via `-X ours`/`-X theirs` instead of git computing a text
  diff/merge on an ~80MB single-line file every time - that cost was real: it
  turned into multi-minute push-retry hangs on `tab_results.yml`'s self-hosted
  runner once main's commit rate picked up. `toprate_runners.csv` stays text on
  purpose (see the `.gitattributes` comment) - it's genuinely row-per-runner,
  so different jobs updating different rows still benefit from a real merge.
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
  at it), then dropped (Sep 2026). The main dashboard payload (`toprate_data.json`)
  never depended on it. It DID serve one real feature client-side though: the
  runner detail panel's "Recent runs" table fetched a horse's complete career
  history live from Supabase (`lib/supabaseFormHistory.ts`) to replace the
  embedded payload's last-10-runs cap. Once Supabase was decommissioned that
  fetch started silently failing (no error surfaced to the user - every
  horse's panel just quietly capped at 10 runs regardless of real career
  length, indistinguishable from a genuinely short career). Found and fixed
  Sep 2026: `lib/supabaseFormHistory.ts` is gone, replaced by the static
  `horse_history/` files above (`lib/meetingFormHistory.ts` fetches the one
  meeting file for the race being viewed). Dropping Supabase itself cost real
  money and ~5-10 min of extra daily-run time for syncing, and was the
  source of most of the bugs chased around that time (schema drift, a
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
  `rail_position` intraday from TAB. A real `going` change now DOES trigger
  a WPR ratings recompute (`compute_wpr_projection(runners_df, target_date,
  target_venues=changed_venues)`), but only that - scoped to just the
  meeting(s) that changed, never the whole day. This was timed standalone
  before wiring it in (per the caution that used to live here): a full
  day's recompute measured ~74s for 41 races on hardware comparable to the
  Vultr box, dominated by a ~22s fixed cost (loading/grouping
  `wpr_form_history.csv.gz`) plus ~1.3s/race - scoping to one meeting (e.g.
  Geelong's 9 races) cut that to ~30s. Since this only fires when a
  condition genuinely changes (not every cycle), and the poll cycle already
  has room under the 15-min job timeout (see `tab_results.yml`), this was
  judged safe to wire in. `interim_resulted` (Sep 2026, separate column
  from `resulted`) is set by `apply_results()` the moment TAB reports a
  finishing position, and flips the dashboard's race-level `done` flag
  (shown as "Resulted", greys out the race, drops it from the next-to-jump
  ticker) immediately - `resulted` itself, and everything keyed off it
  (P&L math, miss-note detection, wpr_actual/comments backfill), still
  waits exclusively for `update_results()`'s authoritative pass, which
  overwrites/confirms it later. `fixed_win_price`/`scratched` are now ALSO
  refreshed from TAB's `fixedOdds` (Sep 2026), confirmed live via
  `--probe-odds` from the Vultr box: the cheap meeting-list endpoint
  carries no price data at all, but each race's own detail endpoint - built
  directly from the meeting's `venueMnemonic` + race number
  (`RACE_DETAIL`), no need for the extra `_links.races` meeting-level hop
  first - returns `runners[].fixedOdds` with `returnWin`/`returnPlace`/
  `bettingStatus`/`flucs`. Bounded to races that are still open
  (`hasFixedOdds`) and starting within `PRICE_LOOKAHEAD_HOURS` (2.0,
  matching `toprate_price_refresh.py`'s own window) - not every open race
  on the card all day, one extra request per eligible race per cycle.
  `apply_prices()` only ever writes a price when `bettingStatus` isn't
  `LateScratched` and `returnWin > 1` (same floor `toprate_price_refresh.py`
  already applies), and only ever sets `scratched=1`, never clears it. This
  is a SECOND, independent price source alongside `toprate_price_refresh.py`
  and `price_refresh.yml`'s existing 5-min refresh - both keep running
  unchanged, whichever wrote most recently wins on `fixed_win_price`, same
  as any other field multiple jobs touch. Actually REPLACING
  `price_refresh.yml` (so it stops running rather than racing TAB) is still
  a separate, not-yet-made decision - that would mean the AU machine going
  down takes out results AND prices AND conditions at once instead of just
  results/price freshness, so it needs its own deliberate call, not an
  assumption that "TAB writes prices now" implies "so does replacing the
  GitHub-hosted job entirely." A plain results/prices/scratches cycle also
  no longer pays the full `--rebuild-only` cost (Sep 2026) -
  `toprate_daily.patch_data_json()` writes just the touched runners'
  fx/f/won/scr keys directly into the existing `toprate_data.json` and
  flips a race's `done` flag once every runner has a finish, skipping the
  form-history/settling-band rebuild entirely (none of it depends on these
  fields) - only a real `going` change still forces the full rebuild
  (needed to serialize the scoped WPR recompute's `wprp_*` fields), and
  `patch_data_json()` itself falls back to signalling "do a full rebuild"
  rather than risk shipping a half-patched payload (missing/unparseable
  JSON, or a touched `run_id` not yet in the payload - a brand-new runner
  that hasn't been through a full rebuild yet).
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
- **`jockey_merit`/`trainer_merit`'s sample-size shrink was silently dead
  code, now fixed (found + fixed 2026-09-17)**: `wpr_projection.py`'s
  `_merit_term()` discounts a thin sample toward 0 (built after a real
  incident, Explosive Tycoon 2026-09-12: jockey_merit +6.04 off a 50%
  jockey_win_pct_90d that was actually 1-of-2 rides), but only when its
  `sample_n` argument isn't None - and `jockey_starts_90d`/
  `trainer_starts_365d` were null on 100% of `toprate_runners.csv`
  (0/67,046 rows, both fields). Root cause was NOT an API gap (a prior
  version of this note wrongly assumed that): confirmed via
  `toprate_field_discovery.py` against a live runner page that the API
  does return the count (`rd.jockeyStats[0].rides = 69` for a
  `periodDays=90` entry), and `build_stats_lookup()` in `toprate_daily.py`
  already correctly read it (`j90.get("starts") or j90.get("rides")`) -
  the actual bug was the row-build step right after it never copying
  `jockey_starts_90d`/`trainer_starts_365d` out of that lookup into each
  CSV row. Fixed there (two added `s.get(...)` lines). Older/existing
  rows stay null until new fetches accumulate under the fix - `_merit_term`
  still degrades to its unshrunk fallback on a null `sample_n`, just
  correctly rather than permanently now. Same root cause had also blocked
  the tracker's `JW_MIN` from ever gaining a minimum-starts floor (asked
  for 2026-09-17, "a jockey with 2 rides for 1 win... very deceiving") -
  that's unblocked too now that the field actually populates going
  forward, though a backtest still needs enough freshly-captured rows
  before it means anything (nothing to bucket by yet on the historical
  window).
- **`tab_results_poller.py` now infers "unplaced" (2026-09-17)**: real user
  report (Coco Dior) was that the Trackers/Summary tab kept a pick
  "pending" all day even though its race had already resulted on TAB,
  because that horse finished 5th+ and TAB's `results[]` (embedded on the
  meeting-list stub) generally only ever carries the top 4 placegetter
  groups - `apply_results()`'s old gate needed an exact `finish_position`,
  which such a horse was never going to get from the interim feed. Fixed
  by adding `unplaced_races` to `fetch_today_results()`: once positions
  1-4 in a race's `results[]` are ALL non-empty (never a partial/still-
  filling-in state - a gap earlier in the array means "not reported yet",
  not "no runner finished there"), every OTHER runner in that race is
  safely inferable as confirmed outside the top 4. `apply_results()` then
  writes `won=0`/`placed=0`/`interim_resulted=1` for those runners, but
  deliberately leaves `finish_position` blank (the exact placing is still
  unknown) - never touches a row that already has a real finish_position,
  and skips scratched runners (never ran, not "unplaced"). Safe to reuse
  `won=0` for this: confirmed against a real payload that an unresulted
  runner's `won` is always `NaN`/`None`, never `0`, so it can't collide
  with "not yet resulted". `speedmap_jockey_tracker.py`'s
  `reconcile_results()` gate was loosened to match (resulted once EITHER
  `f` or `won` is known, not just `f`). The frontend gained a small,
  additive `Runner.resultKnown` field (`r.f != null || r.won != null` in
  `adapter.ts` - the existing `won: boolean` collapses null/0 together, so
  it alone can't tell "not yet resulted" from "confirmed lost") used by
  `lib/trackerRules.ts`'s live (not-yet-CSV-logged) candidate rows in
  place of the old `finishPosition != null` check. Deliberately NOT
  touched: `resulted`/`wpr_actual`/`comments_*` (still exclusively
  `update_results()`'s job, per this file's `tab_results_poller.py` entry
  above), and every Race-tab/Review-tab "resulted" check that depends on
  the authoritative pass (`ResultVsProjection.tsx`, `RaceDetail.tsx`,
  `raceStatus.ts`, `accuracyStats.ts`) - those are unrelated to this
  interim-only signal and untouched. `patch_data_json()`'s race-level
  `done` flip was also loosened to accept `won is not None` alongside `f
  is not None` per runner, so a race can flip to (provisional) done once
  every runner's outcome is known even if one is only "confirmed
  unplaced" rather than an exact position.

  Confirmed live the same day: `toprate_runners.csv`/`toprate_data.json`
  picked up Coco Dior's `won=0`/`interim_resulted=1` correctly within one
  `tab_results.yml` cycle of the fix landing - but the Trackers/Summary
  tab still showed it "pending", because `speedmap_jockey_tracker.py`'s
  `reconcile_results()` (the thing that actually flips a LOGGED pick's CSV
  row to resulted) only ever ran from `daily.yml`'s fixed daytime slots
  (hours apart during racing hours - see that workflow's cron comments),
  never from the fast `tab_results.yml` cycle that runs every 1-2 min.
  Fixed by calling `speedmap_jockey_tracker.main()` from
  `tab_results_poller.py`'s `run_once()` too, gated on `n_result_rows > 0`
  (skip the ~85MB `toprate_data.json` re-read on a price-only/no-op
  cycle) and wrapped fail-safe like the WPR recompute above. `commit_and_push()`
  now also stages `tracker_high_volume.csv`/`tracker_low_volume.csv`
  (only if they already exist on disk) since `run_once()` can rewrite them
  now too - leaving them uncommitted would have broken the runner's next
  `git pull --rebase`. Verified directly against the real, live repo
  state (not synthetic data): running `speedmap_jockey_tracker.main()`
  picked up Coco Dior's already-written `won=0` and correctly reconciled
  it (4 previously-stuck high-volume picks, 3 low-volume, in one pass).

  Widened further the same day: the `n_result_rows > 0` gate above only
  covers RECONCILE lag (an already-logged pick not flipping to resulted
  promptly). It left a second, distinct CAPTURE lag - a runner that only
  becomes newly solo-qualifying partway through the day (a rival's own WPR
  gap can drift past `GAP_MAX` as projections keep refining - worked
  through in detail via Albert Palais/Hozumi, Kembla Grange R1 2026-09-17:
  Hozumi's gap to top was 3.9 at 08:03am capture time, contesting Albert
  Palais out of a High Volume pick, but had drifted to 4.8 - no longer
  qualifying - by the time it was checked again hours later) can have its
  whole qualifying window open and close between two `daily.yml` slots,
  permanently missing the durable CSV log even though the live Race tab
  already surfaces it in real time via `lib/trackerRules.ts`'s
  `liveTrackerCandidates()`. Real user feedback once this was traced back
  ("then the tracker should be updated") confirmed via `AskUserQuestion`
  that capturing more often was the intent, not re-evaluating an
  already-logged pick's frozen inputs (which stays exactly as-designed -
  see the git-blame'd comments on `reconcile_results()`/`build_candidates()`
  for why that's deliberate). Fixed by dropping the `n_result_rows > 0`
  gate entirely - `run_once()` already returns early above this point on a
  genuinely no-op cycle (nothing at all changed), so `sjt.main()` now just
  runs on every cycle that did SOME work (results/conditions/prices/
  scratches), not only a result-writing one. Confirmed cost is acceptable:
  measured 2.4s for a full `sjt.main()` pass against the real, live
  ~85MB `toprate_data.json` - a plain price cycle already pays a
  comparable cost reading/writing that same file via
  `patch_data_json_safe()`, and the self-hosted runner has room under
  `tab_results.yml`'s 15-min timeout.

  **That fix was silently a no-op in production the whole time it ran
  (found 2026-09-17, "why is Bunbury R6 resulted on the race tab but not
  the summary tab")**: `sjt.main()` DOES run every cycle and DOES
  correctly reconcile picks in memory and on disk - confirmed straight
  from the actual GitHub Actions job log for the exact cycle that wrote
  State Of Boom's win, which shows "reconciled 2 newly-resulted pick(s)"
  right there in the output. The bug is one step later: production always
  runs `tab_results_poller.py --once --no-push` (see `tab_results.yml`),
  meaning `run_once()`'s own Python-level `commit_and_push()` (the
  function this session earlier taught to `git add` the tracker CSVs
  too) never actually runs - `--no-push` hands ALL git operations to a
  separate shell step in the workflow YAML itself, which has its own,
  completely separate `git add toprate_runners.csv toprate_data.json`
  line that was never updated to match. So every cycle: `sjt.main()`
  rewrites the tracker CSVs correctly on disk, the commit step stages and
  commits everything EXCEPT those two files, and the reconciled content
  sits as an uncommitted, unstaged working-tree change - which the NEXT
  cycle's checkout step (`git clean -ffdx` + `git reset --hard`) silently
  discards before anyone ever commits it. Repeats forever, every ~5 min,
  for every single reconcile/capture since the day that fix shipped -
  worse, it also occasionally FAILED THE WHOLE CYCLE outright: the same
  unstaged tracker-CSV changes made `git pull --rebase` refuse to run
  ("cannot pull with rebase: You have unstaged changes") whenever a push
  got rejected and needed a retry, confirmed in a real failed job's own
  log the very next cycle after the one that reconciled fine. Fixed by
  adding the same `[ -f tracker_*.csv ] && git add tracker_*.csv` lines
  to `tab_results.yml`'s own commit step that `daily.yml`'s equivalent
  step already had (which is exactly why this never affected daily.yml's
  own reconcile/capture calls, only the fast cycle's). Lesson: a fix to a
  Python function's own git-staging logic doesn't cover every caller of
  that function - grep for every place `--no-push`/an equivalent flag
  hands git off to something else before assuming a `git add` fix is
  universally applied.
- **Mobile race table: two more real bugs found after being told "fixed" 4
  times (2026-09-17)** - both `RunnerRow.tsx`'s/`RaceDetail.tsx`'s mobile
  grid-cols. (1) Every column was a bare fixed px value under a `w-max`
  row (pinned to exactly its own content width, never `auto`) - fine on a
  narrow phone (forces the intended horizontal scroll), broken on anything
  wider than that content total (~390-639px CSS width - most large phones
  in portrait, not just tablets): the row just stopped growing, leaving
  the rest of the card blank instead of filling it (confirmed via
  Playwright screenshots at 430-639px, an exact match to the reported
  screenshot). Fixed by making the Horse column `minmax(Npx, 1fr)` instead
  of a bare px value and the row `min-w-full` instead of `w-max`, on both
  densities - holds its floor and overflows into the existing scroll
  below the min, absorbs any slack above it. (2) Compact (the DEFAULT
  density, not the Full density every previous round of this bug tested)
  had its own copy of the "Fixed $ column too narrow" bug Full went
  through 3 rounds to fix - Compact's own Fixed $ track was still 44px,
  never touched. `overflow: visible` meant the overflowing price text
  didn't get clipped, it rendered backward over whatever painted before it
  - confirmed by screenshotting exactly the TopRate cell's own box at a
  plain 393px width: a 2-digit value like "96" rendered as "9$", the "6"
  not clipped, just fully painted over. Fixed the same way as Full -
  widened to the same proven 76px, recovered the difference from
  Horse's own floor/Proj/TopRate. Both fixes verified across 360-600px
  and both densities via Playwright (row-vs-container overflow
  measurements, not just a screenshot glance) before being called done -
  see the git-blame'd comments on the grid-cols lines themselves for the
  exact numbers. Lesson for next time a "layout broken" report repeats
  after a claimed fix: re-verify EVERY density and a real WIDTH RANGE
  (not just the one viewport already tested), and check individual cells'
  own rendered content for silent overflow, not just the row's total
  width against its container.

  Same day, one more round: fixing the overflow made the table
  technically correct but still "not good enough" (real user feedback) -
  Full's header labels reused the desktop words (TopRate/Form/Jky Win%)
  in tracks that were never wide enough for them even before this
  session's fixes, so `truncate` rendered them as illegible fragments
  ("To...''/"Fo...''/"Jky...''). Gave the mobile header its own short
  labels instead (TR/Fm/J% - see `MOBILE_COLUMN_LABELS_FULL`/`_COMPACT`)
  - free, zero width cost, since the data cells were already sized to
  their real content. While re-checking width budgets for this, also
  found the "a few px of scroll is fine at 360px" call from the earlier
  round was wrong: scrolling all the way to reveal FP at 360px partially
  covered Proj's own value under the sticky name cell (e.g. "72.2"
  rendering as "2.2") - the identical failure mode already fixed for the
  wider-viewport bug, just smaller and un-checked. Recovered the
  remaining ~16px purely from Horse's own floor (68px->52px) rather than
  any numeric column - the floor only bites on the narrowest phones in
  the first place (1fr overrides it everywhere else) and the name span
  already truncates with an ellipsis, so a few more px of a long
  name/jockey line truncating is a far smaller cost than a WPR figure
  silently losing a digit. Full now needs zero scroll at every width
  tested, 360px included, not just 393px+.

  Same day, one more round: still "not right" (real user feedback) even
  with zero overflow and readable headers - TopRate/Form/Jky% sit right
  next to Fixed $ (76px, sized for a rare "$101.00"), so three ~26-28px
  columns at a 2px gap read as visibly cramped next to it, independent of
  how much slack Horse itself has via `1fr` (gap and column width don't
  scale with available space the way `1fr` does). Checked exact
  header-vs-data pixel alignment at 430/480/540px FIRST (perfect match at
  every width) to confirm this was a density complaint, not a bug, before
  touching anything. Asked which tradeoff to make (`AskUserQuestion`,
  real user choice): widen TopRate/Form/Jky% a few px each and the gap
  between them (2px->3px), recovered from Horse's floor again rather than
  dropping Form from mobile Full. First attempt recovered the full ~26px
  needed entirely from Horse (52px->39px) - technically fit with zero
  scroll, but silently went too far the other way: horse names truncated
  to a single letter at 360px ("6. S..."), unreadable. Settled on a
  smaller, verified widening (Horse only down to 50px) that leaves a
  small, real 14px scroll at 360px specifically (0px at 375px+, the
  large majority of phones) rather than firing 26px of the improvement's
  cost into unreadable names - explicitly checked that 14px of scroll
  does NOT reproduce the earlier value-clipping bug (unlike the 16px that
  did, back when this session found it): scrolled all the way at 360px
  and confirmed every value renders intact, only the Proj HEADER's "P"
  clips (cosmetic, header only, only visible if a 360px user manually
  scrolls all the way).
- **Contested/under-$3 races no longer jump straight to "Skipped races"
  while still pending (2026-09-17)**: `lib/trackerRules.ts`'s
  `skippedTrackerGroups()` used to re-evaluate every race live and call a
  contested or under-$3 result a "skip" regardless of whether the race
  had even run yet - misleading, since price and the field can both still
  move before the jump (real user request: "keep them in race order in
  the tracker even if they are under $3 or contested... only move to the
  skipped races section once resulted and they don't fit the criteria").
  `skippedTrackerGroups()` now only considers a resulted race - a
  genuinely final verdict. A new `pendingWatchCandidates()` covers
  everything it used to catch for a STILL-UPCOMING race instead, shaped
  identically to `liveTrackerCandidates()` (reuses the same
  `TrackerCandidateRow`/`candidateToRow()` path, just with a
  `watchReason: 'contested' | 'underPrice'` tag) so it merges straight
  into the Trackers tab's main list and sorts in race order alongside
  real picks, rendered with a "Watching" badge instead of "Live". Once a
  race actually resolves, its contested/under-$3 runners (if any)
  transition from a Watching card to a real Skipped races entry
  automatically - no special-casing needed, since both functions key off
  the same "has this race run" check.

  That check was `race.allResulted` at first, and was itself broken (real
  user report, same day: "Resulted races are not being pushed to the
  skipped section" - a real, confirmed case, Mornington R2: winner Top
  Conti fully known, but 4 scratched runners in the field, and a scratch
  never gets a finish_position/won written, so `allResulted` (which needs
  EVERY runner resolved) stayed false forever). Replaced with a local
  `raceHasRun()` helper: `race.runners.some(r => r.resultKnown)` - any ONE
  runner with a known result is enough, since the whole field's WPR/price
  inputs are frozen for good the moment the race actually runs, regardless
  of whether the fast-patch "done" flag ever catches up for a field with a
  scratch in it.

  Same request also asked for jockey/trainer/barrier/settling position on
  each tracker card. None of these are in `tracker_high_volume.csv`/
  `tracker_low_volume.csv`'s own columns (would need a Python/CSV schema
  change plus backfilling every existing logged row). Added client-side
  instead: `TrackerView` builds a `runnerLookup` Map from the currently-
  loaded `races` prop, keyed by `runId`, and `displayed` enriches every
  row (logged, live, or watching alike) from it right before render.
  Works for any date within the loaded payload (today always is; a date
  outside the ~25-day window shows '—' for these four fields only,
  everything else about the row is unaffected). Settling position is
  `predictedSettlingBand` (the same speed-map-derived label the Race
  tab's own speed map uses) - a prediction, not an actual running
  position, since that's the only "settling" data actually available on
  the runner.
- **Multiple tracker selections from the same race now show grouped
  (2026-09-18)**: contested watches (2+ runners meeting the base rule in
  one race) and the $6+ multi-selection-floor exception (see
  `evaluateTrackerQualifiers`) both put 2+ cards from the same race
  adjacent in the Trackers tab's main list, but nothing visually said
  they were related - easy to miss they're rivals in one race rather than
  two unrelated picks. `TrackerView` now groups consecutive same-`raceId`
  rows (guaranteed adjacent post-sort, since they share the exact same
  `date`/`startTime`) into one `GroupedRaceCard`: a single amber-bordered
  card with one shared venue/race/time header and an "N selections, same
  race" badge, each runner's own `PickCardBody` (the silk/name/badges/
  facts content, pulled out of `PickCard` so both share it) stacked below
  with a divider. A lone selection still renders as a plain `PickCard`,
  unchanged.
- **Audited every other git-staging list for the tab_results.yml bug class
  (2026-09-18)**: `price_refresh.yml`, `.github/workflows/daily.yml`, and
  `deploy_html.bat` all checked out clean (their `git add` lists cover
  every file their own code path can actually write). Found the same bug
  class for real in the LOCAL manual deploy path though: `toprate_daily.py`'s
  `publish()` (invoked by `deploy.bat`'s `--publish` step) was missing
  `wpr_form_history.csv.gz` and `horse_history/` - both genuinely written
  by deploy.bat's own earlier plain `python toprate_daily.py` call, so a
  local deploy could leave them sitting as a real, uncommitted
  working-tree change afterward, with the same downstream risk (a later
  `git pull --rebase` refusing to run at all with unstaged changes
  present) as the automated bug. Fixed both `publish()`'s own file list
  and `deploy.bat`'s own (redundant, but was equally out of date) second
  staging step at the bottom. Also confirmed `.github/workflows/
  toprate_daily.yml` (the OTHER, non-root duplicate of daily.yml, distinct
  from the already-documented dead root `daily.yml`) is `disabled_manually`
  on GitHub - dead, not a live risk, no action needed.

  While checking this, found something unrelated but more urgent: `daily.yml`
  has been failing on ~every trigger for hours (runs #462-467, 2026-09-17
  01:00-04:20 UTC) - not the fetch/rebuild/tracker steps (all succeed),
  the "Commit and push if changed" step's `git pull --rebase -X ours`
  retry loop, hitting its full 240s timeout on every one of 5 attempts
  before giving up (a KNOWN chronic issue - see this file's Deploy section
  - but this run of failures was back-to-back, not occasional). Each
  failed run's local commit (confirmed real, e.g. "27 files changed") is
  built on GitHub's own ephemeral hosted runner and is lost for good the
  moment the job ends without a successful push - meaning several hours
  of fully-computed daily fetches, including whatever they contained
  toward the `jockey_starts_90d`/`JW_MIN` backtest mentioned in the merit
  entry above, never actually reached `toprate_runners.csv` on `main` at
  all. Flagged to the user rather than attempted solo - fixing the
  underlying tab_results.yml-vs-daily.yml push race is exactly the kind
  of change `price_refresh.yml`'s own comment warns already backfired
  once (a shared concurrency group made daily.yml better but broke
  tab_results.yml far worse the same day).
- **Mobile UX audit of Review tab/Settings modal/runner detail modal/search
  found a real, page-wide header overflow bug (2026-09-17)**: found via the
  same Playwright-at-real-widths methodology (360/375/393/430/540/600px,
  exact `getBoundingClientRect`/`scrollWidth` measurements) that had
  already fixed several Race/Summary-tab layout bugs earlier the same day.
  `App.tsx`'s sticky header row (logo + Summary/Race/Review tabs +
  freshness/search/settings icons) needed ~379-398px of natural content
  width with nothing able to shrink or wrap, but only had ~328-361px of
  room inside the header's own padding at common phone widths
  (360-393px covers iPhone SE/12/13/14, Pixel, Galaxy). Since this header
  is shared/sticky across every tab, the overflow silently forced the
  WHOLE PAGE to scroll horizontally at those widths on every screen, not
  just one - previously undiscovered because every earlier mobile-layout
  fix this session was scoped to within-tab table/column content, never
  page-level scroll caused by the header itself. Fixed by shrinking the
  logo text and nav-tab padding/font at base and restoring the original
  sizing at the `sm` (640px+) breakpoint where there's room to spare.
  Verified `document.documentElement.scrollWidth` now exactly equals
  `clientWidth` at 360/375/393/430px (was a fixed 395px regardless of
  viewport below 430, i.e. genuine overflow, not measurement noise).
  Settings modal, Review tab (including every expandable section and its
  breakdown tables), search (empty state and real-query results), and the
  runner detail modal were all separately verified clean/overflow-free
  across the same width range - no further page-level bugs found there.
  One pre-existing, non-regression item noted but deliberately NOT
  touched: the runner detail modal's Career & condition table (see
  `CareerStats.tsx`) truncates its label column by ~5-10px on the
  narrowest phones ("Career" -> "Caree..."). That table's own comments
  already document a prior explicit user choice (Sep 2026) to keep its
  two panels side-by-side even on mobile rather than stack them (stacking
  was tried first and rejected for costing too much scroll), plus a
  `table-fixed` %-width tuning pass and a `title` tooltip fallback
  already anticipating some truncation - reversing that call wasn't this
  audit's call to make unilaterally, so it's flagged here rather than
  changed.
- **GAP_MAX 4 -> 5 sweep tested and rejected (2026-09-19)**: real user
  question ("what if the trackers were changed to be 5 WPR instead of
  4"). `wpr_tracker_gap_sweep.py` (new, read-only scratch script,
  committed for the record like the other `scratch_*`/`wpr_*_test.py`
  analyses) monkey-patches `speedmap_jockey_tracker.GAP_MAX` and reuses
  its own real `build_candidates()` unmodified across every date in the
  live `toprate_data.json` window with a known result (2026-08-23 to
  2026-09-17, 26 dates) - deliberately NOT a from-scratch reimplementation
  of the solo-only/price-floor/contested-exception logic, so it can't
  drift from the real rule. Result: 5 is worse than the current 4 on
  every metric for both trackers, and volume barely moves (the solo-only
  gate dominates pick count far more than the gap threshold itself -
  widening it mostly turns would-be additional qualifiers into contested,
  silent races rather than more solo picks). Tracker A (high volume):
  n 352->345, win% 19.9->18.8, flat ROI +25.0%->+22.1%, prop ROI
  +15.9%->+14.9%. Tracker B (low volume): n 74->77, win% 31.1->29.9, flat
  ROI +12.0%->+7.7%, prop ROI +15.1%->+11.3%. Recommendation: leave
  GAP_MAX at 4. Caveat this sweep is explicit about: n=26 dates here vs
  the n=297/271 the original 6->4 move was decided on (a longer,
  session-long backtest, never committed) - directionally consistent
  with 4 beating a looser threshold, but not the same statistical power,
  and notably this run's own 6.0 column came out roughly tied with (even
  slightly ahead of, on prop ROI) 4.0 for Tracker A, which the original
  6->4 sweep did not find - a real reminder that a 26-date window is
  noisy and shouldn't be used to relitigate settled 4-vs-6, only to
  answer the actual question asked (4 vs 5).
- **`daily.yml`'s chronic push-race fixed for real, root cause confirmed
  (2026-09-17)**: real user report ("Toprate daily not pushing") on top of
  the failure streak already flagged earlier the same day (runs #462-468).
  Pulled the actual job logs (not just conclusions) for run #468: the
  fetch/rebuild/tracker steps all succeeded in ~6 min, then EVERY one of 5
  `git pull --rebase -X ours` attempts hit exactly "TIMED OUT after 240s",
  back to back, for 20 straight minutes - a livelock, not an occasional
  slow merge (identical pattern confirmed across the whole #462-468
  streak). Root cause: the rebase replays this job's own commit against
  every commit that landed on `main` since checkout, and on a conflict
  (there's always one - it and `tab_results.yml`/`price_refresh.yml` all
  touch the same generated files) does a real 3-way content merge on
  `toprate_runners.csv` (~90MB, kept as text - see `.gitattributes`). The
  longer the retry loop ran, the MORE intervening commits
  `tab_results.yml`'s own ~5-min push cadence added, making the NEXT
  attempt's replay even more expensive - guaranteed to eventually never
  catch up once the commit rate crossed some threshold, not a transient
  blip that more retries could fix.
  Fixed by replacing `git pull --rebase -X ours` with `git fetch` + `git
  reset --mixed origin/main` in the retry loop. The repo's own policy for
  these generated files is already "always take incoming, then redo local
  compute on top" (this file's Deploy section) - the old rebase was
  already trying to express exactly that via `-X ours`, just through the
  expensive replay-with-merge route. `git reset --mixed` implements the
  identical policy as a cheap O(1) pointer move instead: it points
  HEAD/the index at the freshly-fetched `origin/main` (discarding only
  this job's own commit OBJECT, never its files) while leaving the
  working tree - this job's own freshly-generated output - completely
  untouched, so the same `stage_generated_files` list (pulled into a
  shell function so it isn't duplicated) just re-stages and re-commits
  fresh on top of the new tip. No merge, so no cost that scales with how
  many commits landed while the job was busy retrying. This is a
  different, narrower fix than the shared-concurrency-group attempt this
  file already documents as having backfired (that one changed
  `tab_results.yml`'s own scheduling/locking and starved its live-results
  cadence) - this change touches only `daily.yml`'s own internal recovery
  logic and does not affect `tab_results.yml` or `price_refresh.yml` in
  any way. Not yet confirmed against a real failing run (the fix landed
  between #469's own in-flight run and its successor) - watch the next
  few `daily.yml` runs to confirm the push actually completes fast now
  rather than burning the full 5-attempt budget.
- **Tracker JW_MIN raised 14 -> 20, GAP_MAX raised 4 -> 5 (2026-09-19)**:
  real user request ("strike rate increase"). `wpr_tracker_strike_rate_
  sweep.py` (new, read-only scratch script, same monkey-patch-the-real-
  `build_candidates()` approach as `wpr_tracker_gap_sweep.py`) swept
  `GAP_MAX`, `JW_MIN` (jockey_win_pct_90d floor), and `TAGS`
  (favoured-only vs favoured+neutral) looking for a genuine strike-rate
  lever. Headline finding: unlike `GAP_MAX` (noisy, non-monotonic - see
  the `GAP_MAX 4 -> 5` entry above, still correct as a description of
  that sweep alone), raising `JW_MIN` improved win% AND ROI TOGETHER for
  both trackers, not a tradeoff - at JW_MIN=20: Tracker A n 337->179,
  win% 19.6->22.3, flat ROI +21.1%->+32.3%; Tracker B n 74->31, win%
  31.1->41.9, flat ROI +12.0%->+53.9%. 22+ showed even bigger numbers but
  Tracker B's sample thinned to n<=21 (n=2 at 30), too noisy to trust -
  real user decision to land on 20 rather than push further. Also swept
  favoured-only (dropping the "neutral" speed-map tag): asymmetric,
  NOT a clean global toggle - helps Tracker B (41.2% win%) but badly
  hurts Tracker A (13.7%, -36.6% ROI) - not applied.

  Separately, and AGAINST this sweep's own recommendation: `GAP_MAX` was
  also raised 4 -> 5, a real user decision made explicitly after being
  shown that combining GAP_MAX=5 with the new JW_MIN=20 is neutral-to-
  negative in the same backtest window (Tracker B completely unaffected,
  n=31/win%=41.9% identical from GAP_MAX 4 through 6 once JW_MIN=20 is
  the binding constraint; Tracker A slightly worse as the gap widens,
  win% 22.3%->21.0%, flat ROI +32.3%->+24.4% at 5). Implemented anyway
  per explicit instruction, same precedent as the earlier `CONTESTED_
  PRICE_FLOOR` call where the user weighted other factors over pure
  backtest robustness - flagged here for whoever revisits this. This
  supersedes the "GAP_MAX 4 -> 5 sweep tested and rejected" entry above
  as the CURRENT production value (that entry's own numbers/reasoning
  for why 5 alone looked worse than 4 are still accurate, just no longer
  the decision that shipped once combined with the new JW_MIN).

  Updated everywhere both constants are duplicated: `speedmap_jockey_
  tracker.py` (source of truth), `frontend/src/lib/trackerRules.ts`
  (live/watching candidates), `frontend/src/lib/raceModel.ts`'s
  `OVERLAY_MAX_GAP_FROM_TOP` (the Race tab's "X WPR from top rated"
  divider, exported so `RaceDetail.tsx` reads it live rather than
  carrying a second hardcoded copy - see that file's own drift history),
  and the Trackers tab's own rule-description copy/comment (both
  numbers were hardcoded into a user-facing string, not derived from a
  constant). Ran `tracker_history_cleanup.py` against the new thresholds
  to purge already-logged picks that no longer qualify (same precedent
  as the original GAP_MAX 6->4 cleanup): `tracker_high_volume.csv` 391
  -> 94 rows, `tracker_low_volume.csv` 91 -> 32 rows. Verified live:
  every currently-showing pick's Jockey % is now >= 20, description text
  reads ">= 20... within 5 WPR", zero layout overflow.
- **Jockey_starts_90d minimum-starts floor backtested: NOT ENOUGH DATA YET
  (2026-09-19)**: real user follow-up request ("do a backtest on min
  jockey starts"), the exact check the `jockey_merit` entry above already
  flagged as blocked pending real data. `wpr_tracker_jockey_starts_floor_
  sweep.py` (new, read-only scratch script) confirmed the block is still
  in effect: `jwN` (jockey_starts_90d) only actually populates in
  `toprate_data.json` from 2026-09-17 onward (the date the underlying
  field-copy bug was fixed), and of RESULTED dates as of today
  (2026-09-18), only 2026-09-17 and 2026-09-18 have any real value at
  all - every older row in the ~26-day window is still null. Checked
  anyway rather than assumed: only 5/190 of Tracker A's current
  GAP_MAX=5/JW_MIN=20 candidates and 2/32 of Tracker B's even carry a
  real starts value, and of those, only 3 (A) and 1 (B) ever resulted -
  n=3 and n=1 is pure noise, not a finding (A's 3 happened to all be
  >=20 starts already, so every floor from 5 to 20 shows an identical,
  meaningless +83.3% flat ROI; B's lone data point was a single loss,
  -100%). No floor applied - revisit once meaningfully more days have
  accumulated under the fix (a week or two of daily fetches, matching
  the "next retrain" caution pattern already used elsewhere in this
  file for a similar not-enough-fresh-data situation).
- **JW_STARTS_MIN=25 shipped, JW_MIN checked and left at 20 (2026-09-19)**:
  direct follow-up to the two entries above. Real user ask ("reduce
  jw_min to 15, but make min starts 50") was checked against real data
  before shipping rather than applied as asked: JW_MIN=15 alone is
  actually WORSE than the current 20 for both trackers (win% 22.3%->
  17.7% for A, 41.9%->27.3% for B - it sits in the same real dip the
  original strike-rate sweep already found at JW_MIN=16), so lowering it
  would have been a regression with no offsetting benefit. Reported this
  back rather than implementing a known-worse change; user then asked
  for the full list of jockeys clearing 15% (108 of 654, 69 with a real
  starts count - see chat for the full table) and, seeing the real
  distribution (a genuine buffer of 50+ jockeys sit comfortably above
  50 starts; the deceptive tail - D Northey 50% on 2 starts, Teaque
  Gould 33.3% on 3, Paige Fergusson-Smith 25% on 4 - is exactly the
  thin-sample problem this floor targets), settled on JW_STARTS_MIN=25
  rather than 50, keeping JW_MIN at 20.
  Implemented in `speedmap_jockey_tracker.py`'s `build_candidates()`
  (checks `jwN` right after the existing `jw` win% check) and mirrored
  in `frontend/src/lib/trackerRules.ts`'s `evaluateTrackerQualifiers()`
  (checks `runner.jockeyStarts90d`) - same null-passes-rather-than-fails
  convention as `wpr_projection.py`'s own `_merit_term()` (an unknown
  sample isn't penalized, it falls back to unshrunk/unfiltered), since
  `jockey_starts_90d` only actually populates in `toprate_data.json`
  from 2026-09-17 onward (see the jockey_merit entry above) and a strict
  null-excludes version would throttle both trackers to near-zero picks
  immediately over stale/missing data rather than genuinely thin
  samples. Confirmed via a real backtest before shipping that this is a
  near no-op today given that data gap (n/win%/ROI identical with and
  without the floor in the live window) and will only start doing real
  filtering as more days accumulate real counts. `tracker_history_
  cleanup.py` re-run against the new rule: 0 rows removed from either
  CSV, exactly as predicted.
- **JW_MIN lowered back 20 -> 14 (2026-09-19)**: direct follow-up, real
  user decision made explicitly against this session's own strike-rate
  finding above ("change jw min to 14 then"). Checked first whether
  JW_STARTS_MIN=25 (just shipped) compensated for a lower win% floor -
  it doesn't, since that floor is still a near no-op on today's mostly-
  null starts data. At JW_MIN=14 (GAP_MAX=5, JW_STARTS_MIN=25): Tracker
  A n 186->337, win% 21.0->18.4, flat ROI +24.4%->+17.7%; Tracker B
  n 31->77, win% 41.9->29.9, flat ROI +53.9%->+7.7% - reported as a real
  trade of strike rate/ROI for roughly double the pick volume, user
  confirmed that's the intended trade-off before shipping.
  Non-obvious wrinkle worth remembering for next time a threshold moves
  in EITHER direction: re-ran `tracker_history_cleanup.py` expecting 0
  rows removed (loosening a per-runner threshold can only help a runner
  qualify, never hurt it, or so the naive reasoning goes) and got 16
  removed from `tracker_high_volume.csv` instead. Root cause: solo-only
  is a RACE-LEVEL population check, not a per-runner one - loosening
  JW_MIN can let a RIVAL newly qualify in a race that used to have
  exactly one qualifier, turning it contested and silencing the whole
  race (unless the CONTESTED_PRICE_FLOOR exception saves it). A looser
  per-runner filter is not guaranteed to be a superset of picks at the
  population level once solo-only is involved - always re-run the
  cleanup and check the actual removed count after ANY GAP_MAX/JW_MIN/
  JW_STARTS_MIN change, never assume based on which direction the
  number moved.
- **2026-09-18 was a genuinely 0-for-13 day for both trackers, real user
  report ("Check today's tracker results... they are very bad")**:
  confirmed against the real CSVs, not dismissed - 11 High Volume + 2 Low
  Volume picks resulted, 0 wins. Root-caused before drawing any
  conclusion: all 11 High Volume picks were captured in ONE batch at
  15:40 that day (`jw` 14.1-19.4 each) - the exact moment the JW_MIN
  20->14 revert landed and the pipeline caught the day's whole card up
  under the newly-loosened rule in one shot, so this was the FIRST
  batch of data under that setting, not an established track record. The
  2 Low Volume losses (jw 29.1/22.2, both well above even the old 20
  floor) were unrelated to the threshold change - ordinary variance.
  0-for-11 has roughly a 1-in-10 chance even at the backtested ~18-20%
  win rate, so this single day didn't prove the JW_MIN=14 call wrong on
  its own, but it was flagged as worth watching rather than dismissed -
  and became part of the direct motivation for the relative-rank
  replacement below.
- **JW_MIN (absolute jockey_win_pct_90d floor) REPLACED entirely with a
  race-relative rank, JW_FLOOR=10/JW_RELATIVE_TOP_PCT=10 (2026-09-19)**:
  real user proposal, prompted by the rough 0-for-13 day above - "being
  in the top x% of jockey sr in the race, rather than 14% and above...
  floor of at least above 10%". Rationale: a jockey's ABSOLUTE win% means
  less than how they compare to the specific field they're riding
  against today (a 16% jockey is genuinely strong in a weak country
  field, mediocre in a stacked metro one) - the old absolute floor
  couldn't tell those two situations apart.
  `wpr_tracker_jockey_relative_rank_sweep.py` (new, read-only scratch
  script - re-implements `build_candidates()`'s race loop with only the
  jw check swapped, since a rule-SHAPE change can't be monkey-patched the
  way a plain constant sweep could) tested top 10/15/20/25/30/40/50%
  against the-then-current absolute JW_MIN=14 baseline. Top 10% won
  outright, not just on strike rate - it beat the baseline on win% AND
  ROI AND volume simultaneously for Tracker A (n 338->403, win%
  18.3->20.6, flat ROI +17.3%->+23.4%) and dramatically for Tracker B
  (win% 29.5->39.0, flat ROI +6.3%->+40.7%, though B's own volume fell
  78->41). Every X looser than 10% (15% through 30%) degraded steadily
  for Tracker A - 10% is a genuine peak in this backtest window, not an
  arbitrary round number picked because the user said "10" for the floor
  too (they're two independent constants, `JW_FLOOR` and
  `JW_RELATIVE_TOP_PCT`, that happen to share a value here).
  Population for "in the race": every non-scratched runner's `jw`
  (`jwN`'s "jockey_starts_90d" sibling field `jw` = jockey_win_pct_90d),
  not just runners already past the speed_map/gap checks - the whole
  point of a relative rule is comparing against the full field's jockey
  quality, not an already-filtered subset. Ties count generously
  (matching this file's existing `_rank_desc` convention elsewhere): a
  jockey tied for the cutoff rank still qualifies. Real, deliberate
  trade-off worth remembering: with a small field, this can still let
  through the single best-of-the-field jockey once they clear JW_FLOOR
  even if that jockey's own absolute number is unremarkable (e.g. an
  11% jockey who's simply the best available in a genuinely weak field)
  - the backtest above already reflects that behaviour and still came
  out ahead, so it's not something to "fix" later without re-checking
  the numbers first. `JW_STARTS_MIN=25` (unrelated mechanism, still
  null-passes) is unaffected and stays in place alongside this.
  Implemented in `speedmap_jockey_tracker.py`'s `build_candidates()`
  (computes `jw_field` from the whole race's `runners`, not just `valid`,
  right where `trr_vals`/`wpr_vals` are computed) and mirrored in
  `frontend/src/lib/trackerRules.ts`'s `evaluateTrackerQualifiers()`
  (same `jwField`/`jwCutoffRank` pattern, reusing the file's existing
  `rankDesc` helper) - verified production `build_candidates()` matches
  the sweep script's own numbers almost exactly (n=404 vs predicted 403,
  tiny drift from data refreshing in between, not a bug). `tracker_
  history_cleanup.py` re-run against the new rule: 23 rows removed from
  `tracker_high_volume.csv`, 5 from `tracker_low_volume.csv` - expected,
  since a rule-shape change (not just a threshold move) genuinely
  reshuffles which already-logged picks still qualify.
- **jw (win%) confirmed better than jrt (jockey_rating) as the tracker's
  ranking field - checked, not applied (2026-09-19)**: real user question
  ("rank jockeys on win strike rate, or toprate jockey rating?").
  `wpr_tracker_jockey_field_choice_sweep.py` (new, read-only scratch
  script) swapped `jrt` (TopRate's own ~50-100 composite jockey score,
  currently unused by the tracker, good coverage - ~78% of runners, same
  ballpark as `jw`) into the relative-rank rule in place of `jw` at
  several top-X%/floor combos. `jw` won outright: at the shipped config
  (top 10%, floor 10) Tracker A gets 20.5%/+22.8% flat ROI, B 39.0%/
  +40.7%; `jrt`'s best config (top 20%, floor barely matters since jrt's
  compressed distribution means the rank cutoff is already the binding
  constraint) only reaches 18.7%/+9.2% for A and 28.9%/+5.4% for B -
  worse at every setting tested, and ROI-negative at jrt's tightest
  config. Consistent with an unrelated but adjacent existing finding:
  `wpr_projection.py`'s own "own_jockey" experiment (see that file's
  ADJ_TERM history comments) found `jockey_rating` measurably worsened
  held-out MAE when tested as an own-history upgrade/downgrade term -
  different question (predicting a horse's rating from a jockey change
  vs ranking jockeys against each other in one race), same field, same
  direction. No production change - `jw` was already the shipped choice.
- **Tracker A gets a form-factor floor, `PFM_A_FLOOR=60.0` - and a real NaN
  bug found in the sweep script that first picked a different number
  (2026-09-19)**: real user question ("should there be a minimum floor for
  form factor or top rate rating?"). `wpr_tracker_a_rating_floor_sweep.py`
  (new, read-only scratch script, re-implements `build_candidates()`'s
  race loop with the floor check INSIDE the qualifying loop, same
  population-level precedent as the jockey relative-rank change) tested
  both fields as an ABSOLUTE floor for Tracker A only (Tracker B already
  has its own RACE-RELATIVE version of this idea via its rating-agreement
  condition). TopRate rating (`trr`) is a real tradeoff, not a free win -
  win% climbs 20.5%->28.1% at trr>=99 but flat ROI drops 22.8%->10.7% at
  trr>=97, the classic favourite-bias pattern. Form factor (`pfm_score`)
  looked like a genuine non-tradeoff win instead, and the user confirmed
  shipping it - initially landed on `PFM_A_FLOOR=65.0`.

  While independently verifying the shipped change against the sweep
  script's own predictions (comparing rid-sets directly, not just
  aggregate counts), found production and the sweep disagreed (n=202 vs
  n=213 on identical loaded data). Root cause: `run_one()`'s floor checks
  were written exclude-style (`if val is None or val < floor: continue`),
  and `pfm_score_by_rid.get(rid)` can return `NaN` (a real pandas float,
  not `None`) for a missing score - `NaN is None` and `NaN < floor` are
  BOTH `False`, so a NaN score silently passed every exclude-style check
  instead of being filtered out. Production's own check was already
  written the safe, include-style way (`if val is not None and val >=
  floor: <include>`, which correctly evaluates `False` for NaN) - the bug
  was in the sweep script alone, not in production. This is the same NaN
  gotcha already found once earlier this session in
  `wpr_tracker_jockey_field_choice_sweep.py`'s debugging - now hit a
  second time in a different script, worth remembering as a recurring
  footgun with pandas-sourced lookups specifically (`_load_pfm_lookup()`
  reads `toprate_runners.csv` via pandas), not a one-off mistake.

  Fixed the sweep script's checks to match production's include-style
  pattern and re-ran the full sweep. The correction mattered: a finer
  sweep (step of 2 around 58-74) showed pfm 62-68 is actually a real LOCAL
  TROUGH, not the peak the buggy numbers suggested - `pfm>=65` itself only
  reached flat ROI +22.6% (barely above the +22.8% no-floor baseline),
  not the "+33-35% peak" first reported. Two genuinely stronger, stable
  bands sit either side of that trough: 58-62 (flat ROI +30-32%, n~212-
  227) and 70-74 (flat ROI +32-35%, n~164-181). Moved the shipped value
  from 65 to 60 - the lower band, chosen over the higher one for its
  larger sample (n=221 vs 181), both clearly outside the trough and both
  still beating the no-floor baseline on win% and both ROI measures.
  TopRate rating floor still NOT applied - it only trades one metric for
  the other, no clean win, unaffected by this correction.

  Implemented in `speedmap_jockey_tracker.py`'s `build_candidates()`: the
  race loop now computes a shared, pre-pfm-filter `race_qualifiers` list
  (the existing tag/gap/jw-relative-rank/jw_starts checks), then splits
  it into Tracker A's own `a_pool` (additionally filtered by
  `pfm_score_by_rid.get(rid) >= PFM_A_FLOOR`, include-style/NaN-safe) and
  Tracker B's existing `b_pool` (rating-agreement, unchanged) - each pool
  is its own independent solo-only population, mirroring how B's
  rating-agreement already worked. Mirrored in
  `frontend/src/lib/trackerRules.ts`'s `evaluateTrackerQualifiers()` (new
  `aPool` array alongside the existing `bPool`, same population-level
  solo/contested/underPrice resolution applied to it) and in
  `TrackersTab.tsx`'s module comment + High Volume `description=` string
  (both now mention "form factor of 60+"). `tracker_history_cleanup.py`
  re-run against the new rule: 30 rows removed from
  `tracker_high_volume.csv` (0 from `tracker_low_volume.csv`, expected -
  this floor only touches Tracker A) - a real, substantial cut, consistent
  with a genuinely new absolute filter rather than a near no-op.
- **`PFM_A_FLOOR` raised 60 -> 70 (2026-09-19, direct follow-up)**: real
  user decision ("Actually make it 70"), made after the corrected sweep
  above already showed the 70-74 band (flat ROI +32-35%, n~164-181) as
  the single strongest stretch in the whole corrected sweep, ahead of the
  58-62 band the previous entry landed on for its larger sample. Updated
  everywhere `PFM_A_FLOOR` is duplicated: `speedmap_jockey_tracker.py`
  (source of truth), `frontend/src/lib/trackerRules.ts`'s `PFM_A_FLOOR`
  constant, and `TrackersTab.tsx`'s module comment + High Volume
  `description=` string (both now read "form factor of 70+" / ">=70").
  `tracker_history_cleanup.py` re-run against the tightened floor: 11
  more rows removed from `tracker_high_volume.csv` (54->42 - runners in
  the now-excluded 60-69 band), 0 from `tracker_low_volume.csv` (still
  unaffected, as expected - this floor only ever touches Tracker A).
- **`JW_RELATIVE_TOP_PCT` raised 10 -> 20 for more volume (2026-09-19)**:
  real user question ("How to get more volume?"), answered by pointing
  out the solo-only gate dominates pick count far more than any single
  threshold, then a specific ask to sweep two axes together.
  `wpr_tracker_volume_sweep.py` (new, read-only scratch script,
  re-implements `build_candidates()`'s race loop with BOTH `PFM_A_FLOOR`
  and `JW_RELATIVE_TOP_PCT` swept inside the qualifying loop, same
  population-level precedent as every prior sweep this session) found
  Tracker B is far more tolerant of loosening `JW_RELATIVE_TOP_PCT` than
  Tracker A, since `PFM_A_FLOOR` doesn't touch B at all: at top 15%, B
  n 41->57 (+39%) with only win% 39.0->36.8/flat ROI +40.7%->+35.8%; at
  top 20% (held with `PFM_A_FLOOR=70`), B n 41->66 (+61%), win%
  39.0->36.4, flat ROI +40.7%->+34.8% - still a modest cost. Tracker A is
  more sensitive: at top 20% it gains n 181->255 (+41%) but flat ROI
  drops further, +32.4%->+19.6%. Recommended 15% as the cheapest volume
  gain for both trackers together; real user decision went with 20%
  instead ("Make it 20"), a deliberate trade of more of Tracker A's edge
  for more volume on both, not a correction to the 10% peak the original
  relative-rank sweep found (that peak is still real for the strictest
  possible setting, just no longer what's shipped).
  Updated everywhere duplicated: `speedmap_jockey_tracker.py` (source of
  truth), `frontend/src/lib/trackerRules.ts`'s `JW_RELATIVE_TOP_PCT`
  constant, and `TrackersTab.tsx`'s module comment + High Volume
  `description=` string (both "top 10%" -> "top 20%" - careful to leave
  the SEPARATE "above 10%" wording alone, since that one describes the
  unrelated absolute `JW_FLOOR`, which stayed at 10 and happens to share
  the same number). `tracker_history_cleanup.py` re-run: 4 rows removed
  from `tracker_high_volume.csv` even though this was a pure loosening (0
  from `tracker_low_volume.csv`) - the same population-level effect
  documented at the JW_MIN 20->14 entry above: a newly-qualifying rival
  (who also cleared `PFM_A_FLOOR`) turned a previously-solo race
  contested, silencing a pick that used to fire alone. Confirms, yet
  again, that a threshold loosening is never guaranteed to be a pure
  superset of picks once solo-only is involved - always re-run this
  script and check the real count after ANY `GAP_MAX`/`JW_FLOOR`/
  `JW_RELATIVE_TOP_PCT`/`JW_STARTS_MIN`/`PFM_A_FLOOR` change.
- **`CONTESTED_PRICE_FLOOR` lowered 6 -> 5, a much weaker volume lever than
  hoped (2026-09-19)**: direct follow-up ("any more volume opportunities?"
  -> "yes" to sweeping this first). `wpr_tracker_contested_floor_sweep.py`
  (new, read-only scratch script) monkey-patches the real
  `build_candidates()` directly rather than reimplementing it - safe here
  since, unlike `GAP_MAX`/`JW_FLOOR`/`JW_RELATIVE_TOP_PCT`/`PFM_A_FLOOR`,
  this constant can't change which pool (a_pool/b_pool) a runner lands in;
  it only decides whether an ALREADY-contested race (2+ pool members,
  solo-only already failed) fires on all of them or stays silent. Result:
  Tracker B's contested-race count never changed at ANY floor value
  tested in this backtest window (n=66 throughout - the rating-agreement
  condition apparently never produces a 2+-member contested group in this
  window), so this lever does nothing for B at all. For Tracker A, only
  $6->$5 was close to free (n 255->262, flat ROI +19.6% unchanged, prop
  ROI +5.8%->+5.5%); every step looser than that ($4, $3, disabled
  entirely) traded real ROI for volume, with "disabled" flipping prop ROI
  negative outright. Shipped the $5 nudge only - real user decision, not
  a push to $4/$3/disabled. Updated everywhere duplicated:
  `speedmap_jockey_tracker.py` (source of truth), `frontend/src/lib/
  trackerRules.ts`'s `CONTESTED_PRICE_FLOOR` constant, and
  `TrackersTab.tsx`'s module comment + High Volume `description=` string.
  `tracker_history_cleanup.py` re-run: 0 rows removed from either CSV -
  expected here (unlike the JW_RELATIVE_TOP_PCT/JW_MIN loosenings above),
  since this constant only affects an already-contested race's own
  fire/silent decision, never population membership, so it genuinely
  can't disqualify an existing pick the way a population-level threshold
  can.
- **New "Combo" score on the Race tab (2026-09-19)**: real user request,
  direct follow-up to the composite-score capture-rate analysis above
  ("can we order race tab by a different score... within 5 wpr (or
  whatever our new score is)" -> "can you weight them in a way that
  toprate rating, wpr & form factor are included?" -> "do the best one
  and the margin can be an even 10"). `wpr_composite_score_capture_test.py`
  (1,994 complete-case resulted races, 56 dates - not gated by speed_map,
  so a much bigger sample than any tracker sweep) grid-searched every
  weight triple with all three weights > 0 and found `0.20*projectedWpr +
  0.70*toprateRating(rescaled) + 0.10*formFactor(rescaled)` the best: 75.1%
  winner capture rate at the SAME shortlist selectivity as the existing
  5-WPR `OVERLAY_MAX_GAP_FROM_TOP` threshold produces, vs projectedWpr
  alone's 65.5% - a real improvement, not a tradeoff, and it edges out
  even the best 2-way blend (WPR+trr only, no form factor, 74.5%).
  Deliberately did NOT touch `speedmap_jockey_tracker.py`'s own GAP_MAX/
  solo-only logic or its live mirror in `trackerRules.ts` - the original
  ask was specifically about the Race tab's own display/ordering, and
  extending this to the tracker's betting rule would need its own
  from-scratch re-sweep of every tracker threshold against the new
  score's very different scale, a separate decision not yet made.

  Implemented as a NEW, independent computation in
  `frontend/src/lib/raceModel.ts` (`compositeScore()`,
  `computeCompositeGaps()`, `COMPOSITE_WEIGHT_*`,
  `COMPOSITE_MAX_GAP_FROM_TOP = 10`, rounded up from the backtest's own
  matched-margin search which found 9.99) - deliberately NOT folded into
  `computeEffectiveRace()`, since that function's own WPR value feeds
  price-softmax math (mirrors `wpr_projection.py`'s `project_race()`
  formula, calibrated against real WPR's own distribution) and overlay/
  underlay detection - swapping in a differently-scaled blended score
  there would have silently corrupted fair-price calculation and every
  overlay flag derived from it. `toprateRating`/`formFactor` are rescaled
  onto `projectedWpr`'s own population mean/std (fixed constants from the
  backtest script's own printed stats, not recomputed live per race -
  a per-race z-score would be a different, unvalidated calculation) before
  blending, so the weights aren't distorted by `toprateRating`'s tiny
  2.71 population std or `formFactor`'s wide 30.88 one. Missing
  `toprateRating`/`formFactor` per-runner gracefully drops that component
  and renormalizes the remaining weights (falls back toward plain WPR
  when data's thin, matching `wpr_projection.py`'s own base-fallback-chain
  convention) rather than returning no score at all - this specific
  degradation behaviour was NOT itself backtested (the backtest was
  complete-case only), a deliberate, conservative choice flagged here for
  whoever revisits it.

  New sort key `'compositeScore'` added to `frontend/src/lib/sorting.ts`,
  surfaced as a "Combo" column in `RaceDetail.tsx` - DESKTOP-ONLY,
  deliberately not added to either mobile density's own visible columns
  (`MOBILE_COLUMN_LABELS_FULL`/`_COMPACT`) given this file's own long,
  hard-won history of mobile grid-cols overflow bugs from squeezing in
  one more column; a mobile user can still select the "Combo" sort from
  the existing mobile dropdown (which already lists every `COLUMN_LABELS`
  entry regardless of mobile visibility, same as Base/Adj today) without
  needing a visible mobile column. The existing "X WPR from top rated"
  divider line now branches on `sortKey`: Proj sort still uses the
  original WPR-based `gapFromTop`/`OVERLAY_MAX_GAP_FROM_TOP`, completely
  untouched; Combo sort uses the new, independent `compositeGapByRunId`/
  `COMPOSITE_MAX_GAP_FROM_TOP` and reads "10 pts (Combo) from top rated"
  instead, so the two never get confused for each other.
- **Tested, NOT applied: swapping the tracker's WPR-based GAP_MAX check
  for the new Combo composite score (2026-09-19)**: direct follow-up
  ("do trackers need to be updated to replace wpr 5 rule with new score
  instead?" -> "Test it"). Flagged the risk before running rather than
  assuming the Combo score's own win-capture validation would carry over:
  that validation measured "is the winner in the shortlist" against
  `toprate_runners.csv`'s full window, not the tracker's own metric
  (ROI once jockey/price/solo-only filters stack on top), and this
  session had already found rating-heavy signals trade win% for ROI
  (the TopRate-rating-floor test; jw beating jrt as the ranking field for
  the same reason) - the Combo score leans 70% on toprateRating.
  `wpr_tracker_composite_gap_sweep.py` (new, read-only scratch script,
  re-implements `build_candidates()`'s race loop with ONLY the gap
  check's underlying score swapped to the exact same composite formula/
  weights/rescale constants as `raceModel.ts`'s `compositeScore()` -
  every other condition, and the 26-date/speed_map-gated window, stays
  identical to every prior tracker sweep) confirmed the risk was real:
  verified the reimplementation reproduces production exactly first
  (n=262/66, matching), then found EVERY composite-gap threshold tested
  (5 through 20) WORSE than the current WPR-based GAP_MAX=5 on both ROI
  measures for BOTH trackers - e.g. at composite gap<=10 (roughly the
  same selectivity area as today): Tracker A flat ROI +19.6%->+7.2%,
  prop ROI +5.5%->+1.7%; Tracker B flat ROI +34.8%->+27.1%, prop ROI
  +35.7%->+27.3% - a real, consistent loss across the whole swept range,
  not a knife-edge result at one threshold. NOT applied - the tracker's
  `GAP_MAX`/`speedmap_jockey_tracker.py` and `trackerRules.ts` stay on
  raw WPR, unchanged. The Combo score remains Race-tab-only.
- **Combo made the Race tab's default sort, and given its own mobile
  column (2026-09-19)**: real user request ("sort by combo by default...
  on mobile show combo column, hide TR"). `RaceDetail.tsx`'s
  `sortKey`/`sortDir` initial state changed from `projectedWpr` to
  `compositeScore` (the existing "X from top rated" divider logic already
  branched on `sortKey` correctly for this, no change needed there).

  Mobile (both Compact and Full densities) had `toprateRating` ("TR")
  removed and `compositeScore` ("Cb") added in its exact old slot, right
  after Proj - TopRate itself became desktop-only in the same change
  (`RunnerRow.tsx`'s TopRate cell gained `hidden ... sm:inline`; the
  Combo cell lost the `hidden ... sm:inline` it shipped with initially,
  becoming visible everywhere). Combo shows a decimal WPR-scale value
  like Proj (e.g. "76.6"), not a bare 2-3 digit integer like TR did, so
  its mobile track needed Proj's own width, not TR's narrower one -
  widened compact 30px->40px and full 29px->36px, recovered from Horse's
  own floor again (compact 90px->80px, full 50px->43px) per this file's
  own established pattern for this exact class of change (see the
  earlier, much longer mobile-grid-cols saga above). `RaceDetail.tsx`'s
  matching mobile header grid-cols and `MOBILE_COLUMN_LABELS_FULL/
  _COMPACT` updated to match exactly, same as every prior mobile
  grid-cols change - all three (RunnerRow's grid-cols, RaceDetail's
  header grid-cols, the label arrays) must stay in lockstep or the header
  and data rows misalign.

  This was verified via the same thorough Playwright methodology as
  every prior mobile grid-cols change - see chat for the specific
  bounding-box checks confirming no clipping/overlap between Cb and its
  neighbours and zero overflow at 360-1280px in both densities before
  this shipped.
- **Combo made the prominent (bold) figure, moved left of Proj
  (2026-09-19, direct follow-up)**: real user request ("combo should be
  the bold number, not proj. have combo to the left of proj"). In
  `RunnerRow.tsx`: the `font-semibold text-emerald-deep` styling that
  used to mark Proj as the row's headline number moved to the Combo
  cell; Proj is now styled like TopRate/Form (`text-ink-mute`, plain).
  Proj's own confidence % sub-line and manual-override asterisk stayed
  attached to the Proj cell, not Combo - those are specifically about
  the raw WPR projection's own model confidence/override, not the blend,
  so moving them would have misattributed what they describe.
  `COLUMN_LABELS`/`MOBILE_COLUMN_LABELS_FULL`/`_COMPACT` in
  `RaceDetail.tsx` reordered to put `compositeScore` before
  `projectedWpr`, matching a same reorder of the two cells in
  `RunnerRow.tsx`'s JSX. No grid-cols width-string changes were needed
  anywhere: Compact/Full mobile already gave both cells equal widths
  (40px/36px) when Combo was first added, and desktop's own two
  neighbouring track widths (60px/56px) simply swap which column they
  belong to when the cells swap order, since the string is positional,
  not keyed - confirmed by inspection rather than assumed, then verified
  live via Playwright (computed style, not just a screenshot glance, for
  the bold/color swap; bounding boxes for clipping/overlap; zero
  overflow at 360-1280px in both mobile densities) before shipping.
- **Proj shown as a whole number (2026-09-19, direct follow-up)**: real
  user request ("change proj to be a whole number"). `RunnerRow.tsx`'s
  Proj value cell swapped `fmtWpr` (1 decimal) for `fmtInt` (rounded,
  matching TopRate/Form's own convention) - Combo right next to it is
  unaffected, still `fmtWpr`/1 decimal, since it wasn't part of the ask.
  Scoped to this one cell only (the Race tab's Proj column specifically,
  the exact context of this conversation) - `projectedWpr` is displayed
  with its own formatting in several other places (`RunnerDetailModal.tsx`,
  `SpeedMap.tsx`/`SpeedMapGrid.tsx`, `ResultVsProjection.tsx`) that were
  deliberately left untouched, not because of any technical constraint,
  just because they weren't part of what was asked.
- **Combo reweighted 0.20/0.70/0.10 -> 0.45/0.30/0.25 (wpr/trr/pfm),
  2026-09-19**: real user observation, using the shipped feature: "combo
  is very aligned to market price because of the heavy trr weighting" -
  `toprateRating` correlates closely with how the market itself prices a
  runner, so a 70%-trr blend inherited a lot of that market-alignment,
  making Combo less of an independent signal than intended.
  `wpr_composite_score_capture_test.py`'s new trr-weight-cap section
  (for each trr cap, finds the best wpr/pfm split via a finer 0.05-step
  grid) found the tradeoff is smooth, not a cliff: capping trr at 0.30
  (under half its original weight) only cost 1.8pp of matched-margin
  capture rate (73.3% vs the original triple's 75.1%). Real user
  follow-up ("can you give a bit more to pfm?") found pfm had real slack
  at that same trr=0.30 cap too - doubling it from 0.10 to 0.20, then to
  0.25, cost essentially nothing further (73.1%, then 73.2% - a small,
  noisy improvement, not a real cost). Landed on 0.45/0.30/0.25: wpr
  restored to plurality driver, trr cut well under half its original
  weight, pfm given real, meaningful influence (up from a token 0.10) -
  73.2% capture rate, a deliberate trade of ~2pp for a materially less
  market-mirroring score, not a correction to the original triple (which
  is still the single best PURE capture-rate optimum found, just not
  what shipped). `COMPOSITE_MAX_GAP_FROM_TOP` left at 10 - the new
  triple's own matched margin came out at 10.08, close enough not to
  re-round for a 0.08 difference.
- **Re-tested (and re-rejected) using the REWEIGHTED Combo score in the
  tracker, 2026-09-19**: direct follow-up ("could we use this new combo
  in the tracker? is 10 pts margin still accurate?"). The original test
  (see the earlier "Tested, NOT applied" entry above) used Combo's
  original 0.20/0.70/0.10 weighting and found it worse than raw WPR at
  every threshold - that risk was attributed to the heavy 70% trr
  weight's favourite-bias pull, so it was worth re-checking rather than
  assuming the conclusion still holds once trr dropped to 30%.
  `wpr_tracker_composite_gap_sweep.py` updated to the currently-shipped
  0.45/0.30/0.25 weights and re-run (widened the swept range down to
  gap<=3 too, since wpr's restored dominance brings the composite's
  scale much closer to raw WPR's own, unlike the old trr-heavy version)
  - same conclusion holds: EVERY threshold tested (3 through 20) is
  STILL worse than the current WPR-based GAP_MAX=5 on both ROI measures
  for both trackers, even though Tracker A's win% at the tightest
  thresholds (23.0-23.4% at gap<=3-5) is now close to or slightly above
  production's 22.9% - e.g. best case for A, gap<=5: flat ROI +19.6%->
  +11.2%, prop ROI +5.5%->+3.2%; Tracker B is uniformly worse at every
  threshold (win% 36.4%->34.3%, flat ROI +34.8%->+27.1%, prop ROI
  +35.7%->+27.3%, identical across the whole swept range - B's
  rating-agreement population simply doesn't depend on this gap check).
  On the margin question specifically: 10 is NOT the right value for
  this reweighted formula either way - the best results now cluster
  around gap<=3-5 (much closer to raw WPR's own scale, since wpr is the
  plurality weight again), not 10 - but this is moot, since even the
  best available margin still underperforms production. NOT applied,
  same as before - tracker stays on raw WPR regardless of which Combo
  weighting is considered.
- **`wpr_combo_race_tab_capture_analysis.py` added, Combo vs market-in-
  order analysis, margin re-checked at 10-12, then reweighted 0.45/0.30/
  0.25 -> 0.50/0.25/0.25 (2026-09-19)**: real user follow-up chain after
  the tracker re-test above, asking specifically about the Race tab (not
  the tracker): "what is the analysis for finding the winner using
  combo? look at within 10 and less, strike rate, top 2/3/4, avg
  selections" -> "only look at margin view, but give strike rate for
  winner/quinella/trifecta/first-four" -> "compare to just taking the
  market in order, add avg price" -> "what number margin should we use?"
  -> "what about 12?" -> "leave at 10, boost wpr to 0.5 in combo".

  Full margin-view findings (1,994 complete-case resulted races that
  also require a known price, 56 dates - a stricter complete-case filter
  than the earlier capture-rate script, since ranking by market price
  needs every non-scratched runner to have one): market-in-order beats
  Combo on winner AND quinella strike rate at every margin tested (3
  through 12), at a shorter average price too, so there's no value edge
  there either - the market's own collective information (scratchings,
  late mail, track bias) is genuinely hard to beat for picking the
  winner specifically. Combo's real edge is on trifecta/first-four at
  low-to-mid margins (e.g. margin<=7: first-four 3.8% Combo vs 0.0%
  market; margin<=10: 12.6% vs 8.4%) - but that edge erodes as the
  margin widens and mostly vanishes by margin 12 (market catches up or
  overtakes on every metric except a near-tied first-four). No sharp
  cliff anywhere in the margin curve - every metric improves smoothly
  and continuously, so there's no statistically "correct" margin, just a
  judgment call on list length vs capture. Recommended and shipped:
  leave `COMPOSITE_MAX_GAP_FROM_TOP` at 10 - it's close to where Combo's
  distinctive trifecta/first-four edge is still real, before it erodes
  at wider margins, without an excessive average selection count (~3.9).

  Separately, the SAME DAY, real user request to increase `wpr`'s weight
  further: "boost wpr to 0.5 in combo". Took the +0.05 from `trr` (0.30
  -> 0.25), not `pfm` - consistent with the whole session's throughline
  that `trr` (not `pfm`) is the market-aligned component being
  deliberately dialed back; `pfm` stayed at the 0.25 it was given a
  genuinely meaningful voice at just above. Checked before shipping:
  capture rate barely moves (73.2% -> 72.5%), matched margin barely
  moves (10.08 -> 9.82) - real user decision to leave the divider at 10
  regardless, per the margin analysis above. Landed on `0.50/0.25/0.25`
  (wpr/trr/pfm) as the CURRENT shipped weighting, superseding the
  `0.45/0.30/0.25` entry above (that entry's own reasoning for landing
  there is still accurate as a description of that step, just no longer
  the final value).
- **Speed Map widened from 6 to 10 tactical columns (2026-09-19)**: real
  user report, working from a live screenshot: "how is carbonados not an
  unfav map, it is drawn wider than Spartus & Il Passero but they are
  unfav" -> after explaining the tint is driven by the trained
  `speed_map` ADJ_TERM (demeaned against the race, barrier is only one of
  several inputs - see `SpeedMapGrid.tsx`'s own long comment on this) and
  showing the real numbers (Carbonados barrier 18, demeaned speed_map
  -0.39, just inside the neutral side of the -0.5 unfavoured cutoff;
  Spartus barrier 16 at -0.53, just past it) -> "then why isn't carbonados
  further forward in the speed map?" -> traced to the SAME kind of
  near-miss one level up: Carbonados' `predictedRelSettle` is 0.504, just
  0.004 past the old 0.5 boundary between the Off Pace and Midfield
  columns, so it landed in the same single "Midfield" column as horses
  sitting genuinely deep in that zone (e.g. Spartus at 0.622, Il Passero
  at 0.606) with no visual way to tell them apart -> real user proposal,
  "seems like there should be more columns to space them out", confirmed
  via `AskUserQuestion` as "10 columns everywhere (desktop + mobile)"
  over a desktop-only option or a within-column position-cue alternative.
  `SpeedMapGrid.tsx`'s `COLUMNS` array split each of the 4 broad middle
  zones (Backmarker/Off Midfield/Midfield/Off Pace - where the reported
  crowding actually lives) into a deeper and a nearer half, while Pace and
  Leader stay single, already-narrow columns (2+2+2+2+1+1=10). The two
  columns in a split pair deliberately SHARE the same label/shortLabel
  (both just say "Midfield", not "Deep Midfield"/"Midfield") - reads as
  one wider zone shown in finer resolution, not two different tactical
  zones, and needed no new terminology or mobile shortLabel-width work.
  `MIDFIELD_IDX` (the wide-barrier "!" caution flag's "at least Midfield-
  forward" cutoff) updated 2 -> 4 to match Midfield's new starting index.
  Confirmed this genuinely fixes the reported case: Carbonados'
  0.504 now lands in the DEEPER of the two Midfield columns (0.5-0.6),
  distinctly one column back from a horse at 0.49 (which would land in
  the nearer Midfield column, 0.4-0.5) or 0.4 (Off Pace) - the old
  single-column Midfield bucket no longer hides that gradient. Verified
  via a background Playwright pass against real data (desktop layout,
  mobile overflow, tint sanity, console errors) before landing - desktop
  (10 columns, correct label pairing, zero overlapping cards, 6px gaps
  throughout) and mobile (no page/component horizontal overflow at
  360/393px, tint mix sane, zero JS errors) both passed cleanly. Mobile
  went from 6 to 10 columns in the same fixed-width, no-horizontal-scroll
  flex row this file has tuned carefully before - the highest risk part
  of this change, real user aware and opted in anyway when asked - and
  the pass did surface two real, non-blocking mobile findings: (1) the
  "Off Midfield" and "Off Pace" mobile column headers both truncated to
  "OFF ..." at 360-393px (the shared "Off " prefix ate the only 4
  characters `truncate` leaves visible at that width), making the two
  zones indistinguishable by header text alone - fixed immediately by
  dropping the internal space (`shortLabel: 'OffMid'`/`'OffPace'`, no
  longer 'Off Mid'/'Off Pace'), which moves the distinguishing M/P letter
  into that same 4-character window instead of being pushed out by the
  space. A second, narrower Playwright pass at exactly 360px (not just
  393px) found this fix only PARTIAL: "OffMid" still truncated to "OFF..."
  there specifically (the wide "M" glyph itself got swallowed by the
  ellipsis at a 29px column width) while "OffPace" showed enough of
  itself to display its own "P" - the two were no longer identical text,
  but "Off Midfield" still had no distinguishing letter visible at 360px.
  Shortened further to `'OMid'`/`'OPace'` (dropping "ff" entirely) so the
  distinguishing letter sits immediately after the shared "O" - re-checked
  again at exactly 360px to confirm. (2) mobile
  card horse-names are now down to essentially one visible character +
  ellipsis (vs 2-3 characters under the old 6-column layout) - an
  inherent, expected cost of narrower cards from doubling column count
  rather than a bug (full name is still in the card's hover tooltip), left
  as-is rather than "fixed" since there's no free width left to recover it
  from without giving back some of the column-count improvement itself -
  flagged here in case a future report wants it revisited.
- **Speed Map wide-gate caution threshold widened from outer-third to
  outer-half (2026-09-19), same-day direct follow-up**: real user
  follow-up to the 10-column change above, working through the same
  Randwick screenshot (Randwick's "Nick Moraitis Trophy (Bm88)", NOT R1 -
  corrected 2026-09-19 after a Playwright verification pass caught this
  file mislabeling it "Randwick R1" throughout the original thread; the
  app itself was never wrong, only these notes) - Ice Kool (barrier 10 of 15, draw 0.64) was
  projected on-pace/Midfield-forward in this Hot-tempo race, the exact
  "needs to cross rivals or a hot pace to be plausible" scenario the "!"
  caution flag exists for, but sat just under the old 2/3 (outer-third)
  cutoff and got no flag - the same kind of near-miss this file already
  fixed once for the tint threshold and the column boundaries themselves.
  Asked "is it realistic to predict Ice Kool and Nepo Baby will settle on
  the fence from those wide barriers" -> explained the column axis never
  claims lateral/rail position at all (only forward/back timing - the
  barrier gauge is the only lateral cue, and it already showed Ice Kool's
  gate as amber/moderate, not innermost) -> "should they be not settling
  on the fence then" (confirmed: correct, realistic expectation is wide
  running, not the rail) -> "correct the speed map then" -> `AskUserQuestion`
  clarified the ask as specifically widening the caution flag's threshold
  (not a UI relabel, and not a change to the underlying WPR/settle model -
  `settling_estimate.py`'s `barrier_nudge`, already calibrated, untouched).
  `computeCautionRunIds()`'s `drawFrac >= 2/3` check -> `drawFrac >= 1/2`.
  Checked the real, non-obvious consequence before shipping rather than
  assuming Ice Kool would end up flagged: the file's existing "at most ONE
  wide-and-forward runner gets forgiven in a Fast/Hot-tempo race, the
  LEAST wide of the qualifying group" rule (added earlier per its own
  2026-09-16 feedback, unmodified here) means widening the pool just
  changes who's least-wide - Ice Kool (0.64) is milder than Oakfield
  Jupiter (barrier 11, draw 0.71), which had been the sole exemption
  under the old threshold, so the exemption MOVES to Ice Kool: Oakfield
  Jupiter newly gets flagged, Ice Kool stays unflagged (arguably correct
  by the model's own "least implausible gets the benefit of the doubt"
  logic - the flag's job was never "show every wide gate", it's "flag
  which crossing looks LEAST plausible"). Reported this counterintuitive
  result and asked before shipping (`AskUserQuestion`): keep it (the
  Oakfield Jupiter catch is a real improvement, and Ice Kool being
  exempted is defensible on the model's own terms), revert, or drop the
  single-exemption rule entirely so every qualifier gets flagged - real
  user decision was to keep it as implemented. Verified via a background
  Playwright pass against this exact race before landing.
- **New "SM Adj" race-table column, same day**: real user request, direct
  follow-up to the caution-threshold conversation above - "add a column
  for speed map adj, with green and red colour". Surfaces the exact same
  number the Speed Map's own tile tint is built from (speed_map ADJ_TERM,
  demeaned against the race - see SpeedMapGrid.tsx's own long comment for
  why the raw wpjcb value alone would be misleading), as its own sortable
  desktop-only column between Adj and Combo, green for positive
  (favoured)/red for negative (hurt)/gray for null or ~0, same styling
  convention as the existing Adj column beside it. Extracted the demeaning
  formula out of SpeedMapGrid.tsx into a new exported
  `speedMapDemeanedByRunId()` in `raceModel.ts` so the Speed Map's tint and
  this column read from ONE shared calculation rather than two independent
  copies that could quietly drift apart over time (the same DRY precedent
  `OVERLAY_MAX_GAP_FROM_TOP`/`compositeScore()` already set elsewhere in
  that file) - `computeEffectiveRace()` now also returns `speedMapAdj` per
  runner, computed over the same non-scratched population its own
  `scratched` Set already defines (matching exactly what RaceDetail.tsx's
  `SpeedMapGrid` prop is filtered to, so the two can never see a different
  race mean). null for a scratched runner, same as the Speed Map excluding
  them from the grid entirely. Desktop-only (RunnerRow.tsx/RaceDetail.tsx
  grid-cols and COLUMN_LABELS), same as Base/Adj immediately to its left -
  not added to either mobile density, per this file's own long, hard-won
  history of mobile grid-cols overflow bugs; still reachable through the
  mobile sort dropdown like Base/Adj already are. Verified via a
  background Playwright pass (column alignment, values cross-checked
  against the Speed Map's own tint for the same runners, sort behaviour,
  desktop/mobile layout) before landing.
- **SM Adj added to Full mobile density too, same day**: direct follow-up
  - real user report "not seeing it" turned out to mean mobile, not a
  deploy/cache issue (`AskUserQuestion` confirmed) - the column had been
  shipped desktop-only, same as Base/Adj, on the assumption that was the
  safe default given this file's own long mobile-column-overflow history.
  Added to Full density only (not Compact, which stays untouched) via the
  same `compact ? 'hidden sm:inline' : ''` trick Form/Jockey Win% already
  use to appear on Full mobile + desktop but not Compact.
  `RunnerRow.tsx`'s Full-only mobile grid-cols grew from 8 to 9 tracks,
  adding a 30px SM track right after Horse (before Cb) - Horse's own floor
  was DELIBERATELY only trimmed a little (43px -> 38px), not fully
  absorbed the way this file's established pattern usually recovers a new
  column's cost, since taking the whole ~33px from Horse would have left
  it near-unreadable at 360px; the remaining width was left to the row's
  existing horizontal-scroll fallback instead. Mirrored in `RaceDetail.tsx`
  (matching grid-cols + a new "SM" entry in `MOBILE_COLUMN_LABELS_FULL`).
  Verified via a background Playwright pass at 360/393px in both densities
  before landing, specifically checking for the exact failure mode this
  file has hit before (scrolling to reveal a far-right column pushing an
  earlier value under the sticky Horse/silk cells) - see its own findings
  for whether the Horse floor needed further adjustment.
- **SM Adj repositioned and given a real neutral zone, same day**: direct
  follow-up on a screenshot - "Sm should be between j% and fixed. Green
  and red colours should be +/- 0.5". Two changes: (1) moved from between
  Adj/Combo (desktop) and Horse/Combo (mobile Full) to between Jky Win%/
  J% and Fixed $ on both - `COLUMN_LABELS`/`MOBILE_COLUMN_LABELS_FULL`
  reordered and both grid-cols track lists updated to match (desktop:
  `...44px_56px_60px_68px_52px` with SM Adj's 60px track now right before
  Fixed $'s 68px; mobile Full: `...31px_30px_76px_20px` with SM Adj's
  30px track now right before Fixed $'s 76px). Total column widths
  unchanged, only their order. (2) the cell's own colour check changed
  from a bare sign test (any positive green, any negative red) to the
  SpeedMapGrid tile's own +-0.5 neutral-zone threshold - real user
  correction after the earlier verification pass had flagged, as a
  cosmetic note, that a small value like -0.4 showed red text next to an
  untinted (still-white) Speed Map tile for the same runner. Extracted
  SpeedMapGrid.tsx's own local `THREAT_THRESHOLD` constant into a new
  exported `SPEED_MAP_TINT_THRESHOLD` in raceModel.ts (same DRY precedent
  as `speedMapDemeanedByRunId` itself) so the tile and the table column
  read from one shared threshold rather than the table inventing its own
  number that could drift from the tile's - SpeedMapGrid's own tint
  behaviour is unchanged, just reading the constant from its new home.
  Verified via a background Playwright pass (column position on both
  densities, and the actual CSS class applied to several cells spanning
  clearly-positive/clearly-negative/near-zero SM Adj values, not just a
  visual glance) before landing.
- **SM Adj mobile Full width tradeoff: real, conflicting verification
  results, user chose to keep it (2026-09-19)**: a background Playwright
  pass against the PRE-reposition build (commit 4950b13, SM Adj between
  Horse/Combo) found two real problems at mobile widths - horse names
  rendering with ZERO visible characters before the ellipsis at both
  360px and 393px (Horse's floor only trimmed 43->38, ~28px short of the
  new column's real ~33px cost), and, at 360px specifically, scrolling
  the row fully right to reveal FP pushed the Combo score completely
  behind the sticky Horse column (geometrically confirmed, not just a
  screenshot glance) - the exact "value hidden under sticky cell" failure
  class this file has hit and fixed multiple times before. Reported this
  plainly (not softened) via `AskUserQuestion` - revert to desktop-only,
  drop another mobile column to make room, or keep it and accept the
  tradeoff - and flagged that repositioning (see the reposition entry
  above) doesn't change total row width, so the same regression was
  expected to still be present. A SEPARATE, later background Playwright
  pass against the ALREADY-REPOSITIONED build (commit 88242a7, SM Adj
  between J%/Fixed $) scrolled the same row fully right at both widths
  and found NO clipping under the sticky column this time - values stayed
  fully intact - though it still measured the same non-zero scroll
  distance (9px at 393px, 42px at 360px) as a real, pre-existing,
  accepted tradeoff. The two results genuinely disagree on the clipping
  question specifically (same total row width, different column order,
  and the second check was screenshot-based rather than the first's
  explicit bounding-box containment math) - not yet reconciled. Real user
  decision, made with the first (more alarming) report already in hand:
  keep the current implementation as shipped rather than revert or drop a
  column. Horse-name legibility at 360px was NOT re-verified against the
  repositioned build specifically (repositioning doesn't change Horse's
  own floor, so the zero-characters finding likely still holds) - worth a
  closer look if a future mobile legibility complaint comes in on this
  exact race/density/width combination.
- **Second, dotted reference line for the WPR-based cutoff (2026-09-19)**:
  real user request, direct follow-up - "add a dotted line for 5 from top
  rated and different colour". The existing gap-from-top divider line
  already showed EITHER "5 WPR from top rated" (Proj sort,
  `OVERLAY_MAX_GAP_FROM_TOP`) OR "10 pts (Combo) from top rated" (Combo
  sort, `COMPOSITE_MAX_GAP_FROM_TOP`) as one solid indigo line, never
  both - so sorted by Combo (the app's default sort since an earlier
  entry above), there was no way to see where the tracker-validated,
  betting-relevant WPR-5 cutoff actually fell, since Combo's own ranking
  mostly tracks WPR (50% weight in its blend) but isn't identical to it.
  Added a SECOND divider, shown only when `usingComposite` (Combo sort) -
  showing the primary line a second time under Proj sort would just
  duplicate information already on screen. Styled distinctly per the
  request: `border-dotted` (not a solid filled bar) and amber (not
  indigo, an already-established colour elsewhere in this file for
  informational/secondary markers, e.g. the override asterisk and FS/FU
  spell labels) so it reads as a secondary reference line, not a second
  primary boundary. Uses the same per-row transition-detection approach
  as the primary line (`gapFromTop <= OVERLAY_MAX_GAP_FROM_TOP`, checked
  against `effectiveByRunId` directly rather than `compositeGapByRunId`)
  but deliberately NOT gated on the primary line's own "only meaningful
  when contiguous" concern - since Combo and WPR rank differently, WPR-5
  membership isn't guaranteed to be contiguous under Combo's own sort
  order, so this line can in principle appear more than once if the
  underlying data is genuinely non-contiguous; left as an honest
  reflection of that rather than forced into a single, potentially
  misleading mark. Verified via a background Playwright pass (line
  renders correctly dotted/amber, appears only under Combo sort, coexists
  sensibly with the existing indigo line, no overflow/console errors)
  before landing.
- **Dotted WPR-5 line fixed to show exactly once, same-day follow-up**:
  the "left as an honest reflection" call above was wrong in practice -
  real user report with a screenshot (Caulfield R1 "The Taggart (Bm74)",
  2026-09-19): the per-row transition check fired 3 separate times on
  that race's actual data ("should only be 1 dotted line"), which reads
  as broken/noisy, not informative, once you actually see it happen.
  Replaced with `lastWprGapWithinThresholdIndex` (a `useMemo`, computed
  once per sort/race rather than per row): finds the LAST row position
  under the current Combo sort order where `gapFromTop <=
  OVERLAY_MAX_GAP_FROM_TOP`, and the dotted line now renders only at
  `i === lastWprGapWithinThresholdIndex`. Deliberately the LAST qualifying
  row, not the first - the decision-relevant framing is "everyone below
  this line is definitely outside the WPR-5 group", which holds even when
  a few non-qualifying rows sit ABOVE the line too (Combo's own
  re-ordering can't promise perfect contiguity there anyway, and a line
  positioned after the first qualifying run would incorrectly exclude
  later qualifying runners from the visual grouping entirely). Verified
  via a background Playwright pass specifically against the reported
  Caulfield R1 race (confirms exactly one line now, not three) plus
  several other large fields, and re-confirmed Proj sort/the primary
  indigo line are both unaffected.
- **Dotted line switched from WPR-based to Combo-based, same-day direct
  correction**: "And it should be based on combo, not wpr" - the dotted
  line's whole premise was wrong from its first version onward: it had
  read `effectiveByRunId[...].gapFromTop` (the WPR-based
  `OVERLAY_MAX_GAP_FROM_TOP`), showing a cross-metric comparison, when
  the actual intent was a TIGHTER inner tier of the SAME Combo score the
  primary 10pt line already sorts/groups by. Replaced with a new local
  `COMBO_INNER_GAP_FROM_TOP = 5` (Combo-scale points, not exported from
  raceModel.ts like the two real cross-file constants are, since nothing
  else needs a "Combo gap of 5") read from `compositeGapByRunId` - the
  exact same source the primary line uses, just a smaller threshold.
  Label text changed to match ("5 pts (Combo) from top rated", was "5
  WPR from top rated"). Kept the same-day single-index fix (
  `lastComboInnerGapWithinThresholdIndex`, computed once via `useMemo`,
  not per-row) since that fix's own reasoning (Caulfield R1's 3-lines
  bug) applies identically here - a "Combo gap <=5" run can still be
  non-contiguous under Combo's own sort for the same reason a WPR-based
  one was. Since 5 < 10, the dotted line is mathematically guaranteed to
  fall at or above the solid indigo 10pt line, never below it. Verified
  via a background Playwright pass (correct label, position checked
  against actual Combo score values above/below the line, ordering
  relative to the indigo line, Proj sort unaffected) before landing.
- **5pt vs 10pt Combo exotic-capture analysis, same day (analysis only,
  no production change)**: direct follow-up to the two divider lines
  above - "what's the analysis on 1st, quinella, tri, f4 for within 5 pts
  vs 10 pts... could it be a standout where within 5 pts is in for all
  positions and then within 10 pts is just in for the last 1 or 2
  places" - i.e. a banker-for-the-top-spot(s)/wider-net-for-the-minor-
  placings exotic structure. `wpr_combo_5v10_exotics_capture_test.py`
  (new, read-only scratch script, same complete-case population as
  `wpr_composite_score_capture_test.py` - 2,019 races, 57 dates - using
  the CURRENTLY-shipped 0.50/0.25/0.25 weighting, not the older scripts'
  0.45/0.30/0.25) computed win/quinella/trifecta/first-four capture rate
  for the pure inner5 pool, the pure outer10 pool, and every hybrid in
  between (relax the last 1/2/3 required placegetters from inner5 to
  outer10). Avg selections: inner5 2.08/race, outer10 3.99/race.
  Headline numbers: win 48.8% (inner5) vs 73.5% (outer10); quinella 15.0%
  vs 45.4% (both-inner5 vs both-outer10), with the hybrid (1st inner5,
  2nd outer10) at 28.7%; trifecta 4.0% (all inner5) -> 8.0% (relax last
  1) -> 15.2% (relax last 2) -> 24.8% (all outer10); first-four 1.2% (all
  inner5) -> 2.3% (relax last 1) -> 4.9% (relax last 2) -> 8.5% (relax
  last 3) -> 13.9% (all outer10). Reading these together: banking only
  the TOP spot at the tight 5pt threshold and opening every other
  placing to the wider 10pt pool (trifecta's "relax last 2", first-four's
  "relax last 3") recovers roughly 60% of the full outer10-boxed capture
  rate (15.2/24.8 and 8.5/13.9) while only needing the narrow ~2-selection
  inner5 pool for the banked leg instead of the ~4-selection outer10 pool
  there too - a real, usable trade-off for a keyed/banker bet structure,
  not a free lunch (it's still meaningfully behind full outer10 boxing on
  raw capture rate, just cheaper for the banked leg). Not yet turned into
  a staking/ROI or actual combinations-cost calculation (this analysis
  stopped at capture rate + avg pool size, matching exactly what was
  asked) - a natural next step if this is pursued further, same as every
  other capture-rate-first analysis in this file's history.
- **Top-Combo-pick gap>5 win rate/avg odds queried, same day**: direct
  follow-up - "what's the strike rate and avg odds of top ranked winners
  who are more than 5 clear of 2nd ranked". Added an open-ended `gap > 5`
  query to `wpr_combo_top_pick_margin_analysis.py` (the existing bucketed
  table stops at discrete ranges like "3-5"/"5-7", none of which directly
  answer an open "more than 5" question). Same population/weighting as
  that script's own margin-bucket table (1,994 races, complete-case incl.
  known price, currently-shipped 0.50/0.25/0.25 Combo weighting). Result:
  n=799 races, win 36.9%, place 69.3%, avg price $2.77, flat ROI -14.4%,
  prop ROI -12.1% - a real, meaningfully higher strike rate than the
  full population's overall 29.0% average (as expected - a clear
  standout is more likely to actually win), but still ROI-negative at
  these prices, consistent with this file's standing finding that Combo's
  top pick has no robust backing edge anywhere tested so far (margin,
  price floor, state, race class - see the earlier entries in this
  section) - a higher win rate alone doesn't imply a betting edge once
  the market has already priced that same standout-ness in.
- **Combo converted to a fair price/edge vs market, tested for a real
  overlay-betting signal - NOT profitable at any threshold (2026-09-19)**:
  real user question, direct follow-up - "what about if combo was
  converted into a price and compared against market? can it be
  profitable to bet overlays?". `wpr_combo_price_overlay_test.py` (new,
  read-only scratch script) replicates `wpr_projection.py`'s own
  `compute_edge_scores()` softmax EXACTLY (same beta=0.15, read from
  `wpr_models/config.json`, not the 0.4 fallback `get_price_beta()` uses
  when config is missing - checking this mattered, an earlier draft
  nearly used the wrong fallback) for both Combo and raw WPR side by
  side, over 6,133 resulted races (121 dates, 2026-04-26 to 2026-09-18) -
  the biggest population this session has used for any Combo analysis,
  since this needs no complete-case restriction (edge is computed
  per-runner over whoever has both a score and a price, matching
  production's own per-runner-valid convention exactly, not a
  whole-race complete-case gate).

  Sanity-checked the formula before trusting any ROI number: tried
  reproducing the CSV's own already-stored `wprp_edge` column from
  scratch and found it does NOT match closely (mean abs diff ~0.03-0.05)
  under either price fallback order tried - traced to `wprp_edge` being
  written ONCE pre-race against whatever price was live at fetch time,
  while today's `fixed_win_price`/`starting_price_sp` columns are
  continuously overwritten by later price-refresh cycles and the
  post-race SP fill, so comparing a frozen historical edge against a
  now-updated price column is a timing mismatch, not evidence either
  formula is wrong. Verified the formula a different way instead: edge
  correlates with log(price) only moderately (~0.4, not a near-tautology
  of "edge just means longshot"), and a high-edge (>0.10) subset beats
  its OWN price bucket's baseline win rate in 5 of 7 buckets (e.g. $3-5:
  20.7%->22.1%, $8-15: 6.9%->8.0%) - the same "not just picking
  longshots" property this repo's own documented favourite-longshot-bias
  check already required of the raw-WPR edge signal, so the underlying
  mechanism checks out even though the specific numbers can't be
  cross-validated against the stale stored column.

  Headline result, swept edge>0.00 through edge>0.20 for both Combo and
  raw WPR: **every single threshold is flat-ROI-negative for both**, from
  around -17% to -31% at the loose end down to -1.1% (Combo)/-1.8% (WPR)
  at the tightest, thinnest threshold tested (edge>0.20, n=603/454) -
  neither ever crosses into profit. Combo modestly OUTPERFORMS raw WPR at
  every matched threshold (e.g. edge>0.10: Combo win% 22.7%/flat ROI
  -18.9% vs WPR's 13.4%/-18.9% - same ROI, meaningfully higher win rate,
  i.e. shorter average winning prices) but "modestly better than a
  losing baseline" is still a losing strategy. This extends this file's
  own standing finding (no robust backing edge for Combo's top pick,
  found independently via margin/price-floor/state/race-class slicing
  earlier) to a genuine price/edge framing rather than just a margin-
  bucket one, and reaches the same conclusion: this project's own
  documented "the unexplored lever is bet selection, not prediction
  accuracy" line still doesn't have a validated betting rule behind it
  from this angle either.
- **Win-betting every runner in the inner5/outer10 Combo pool, crossed
  with a price floor - also not profitable, same day**: direct follow-up
  - "what about adding a price floor and only win betting those within 5
  or 10 pts of top rated". Different bet shape from every prior Combo
  analysis (not #1-pick-only, not an edge-vs-market framing): back EVERY
  runner in `wpr_combo_5v10_exotics_capture_test.py`'s existing inner5/
  outer10 pools to win, swept across price floors ($2 through $10), added
  as a new section in that same script. Same complete-case population
  (2,019 races), price = starting_price_sp falling back to
  fixed_win_price. Every floor is flat-ROI-negative for both pools except
  one cell (inner5, floor>=$10: n=248, flat ROI +1.6%, prop ROI +5.1%) -
  checked this one BEFORE reporting it as a finding, per this file's own
  established pattern (every prior apparently-positive cell in this
  file's history has failed the same two checks): excluding the 3
  biggest-priced winners (Ozzy The Equaliser $17, Pretty Perky $16, Or Am
  I $15) flips it to -16.7%/-9.1%, and a first-half/second-half date
  split (52 dates) shows -36.9% vs +38.9% - the apparent profit is a
  handful of longshot winners clustered in one half of the window, not a
  stable edge, the exact same fragility signature this file has now
  documented repeatedly (CONTESTED_PRICE_FLOOR, the gap>=3/price>=3
  claim, Maiden race class). No robust profitable cell found anywhere in
  this sweep - extends the standing "no robust backing edge for Combo"
  finding to a third distinct bet shape (straight win-betting a
  gap-threshold pool with a price floor, after margin-bucket framing and
  overlay/edge framing both already failed to find one).
- **Market-disagreement angle tested - also no edge, same day**: real
  user question, open-ended - "any betting edges you can find with combo
  score?" - after margin/price-floor/state/class/overlay/win-betting all
  came back negative, tried the one classic "value" framing not yet
  covered: does Combo's #1 pick do better specifically when it DISAGREES
  with the market (i.e. Combo's top-rated runner is NOT the market's own
  favourite) - the textbook signature of a model seeing something real,
  vs just echoing the market. `wpr_combo_market_disagreement_test.py`
  (new, read-only scratch script, biggest population yet for a
  per-runner Combo test - 6,126 races, 121 dates, no complete-case gate,
  same per-runner-valid convention as `wpr_combo_price_overlay_test.py`)
  splits races into AGREE (Combo's #1 = market's #1 favourite, n=3,757,
  win 37.1%/flat ROI -11.4%) vs DISAGREE (different runners, n=2,369, win
  19.4%/flat ROI -15.1%) - DISAGREE is WORSE, not better, both on win
  rate and ROI, the opposite of the value hypothesis. Sliced DISAGREE
  further by how much shorter the market favourite is (price ratio) and
  by state looking for a sub-population where disagreement pays off -
  found one near-breakeven cell (SA, n=173, +0.9%/+2.4%) and checked it
  before reporting, per this file's own established practice: FAILS both
  robustness checks (first-half/second-half date split: +15.1% vs
  -12.0%; excluding the 2 biggest-priced winners: -7.6%) - not a real
  finding, the honest DISAGREE headline (-15.1%/-16.2% overall) stands.
  Combined running total across this whole thread: margin buckets, price
  floors (both the #1-pick-only and the whole-pool framings), state,
  race class, market-in-order comparison, softmax edge-vs-market, and now
  market-disagreement - EVERY angle tried lands on the same conclusion,
  no robust profitable betting rule found for Combo anywhere. This is a
  real, useful negative result in its own right (see this file's own
  "the unexplored lever is bet selection, not prediction accuracy" line
  above) - not proof no edge exists at all, but every reasonably obvious
  angle checked so far comes back empty once stress-tested rather than
  taken at face value.
- **First genuinely-more-robust-than-noise Combo result: a jockey
  quality floor on Combo's own #1 pick, real but modest (2026-09-19)**:
  direct follow-up - "look into that" (bringing in a signal Combo doesn't
  already contain, the closing suggestion of the disagreement-test
  entry above, since speedmap_jockey_tracker.py's own jockey-relative-
  rank mechanic already has a validated positive-ROI history on ITS OWN,
  differently-gated population). `wpr_combo_jockey_filter_test.py` (new,
  read-only scratch script, same 6,126-race/121-date per-runner-valid
  population as the market-disagreement test) swept both a relative
  jockey-rank filter (top X% of jockey_win_pct_90d across the WHOLE race
  field, same convention as the tracker's own build_candidates()) and an
  absolute jw floor, applied to Combo's own #1-ranked pick (no solo-only,
  speed_map, or price-floor gating - none of the tracker's other
  machinery, just "back Combo's top pick when its jockey clears X").
  Baseline (no filter): win 30.2%, flat ROI -13.0%. A clean, monotonic
  improvement as the floor rises, crossing into positive territory
  around jw>=18 (n=1,147, win 39.8%, flat ROI +3.4%, prop ROI +0.1%) and
  peaking around jw>=20 (n=812, win 40.9%, flat ROI +4.6%, prop ROI
  +1.4%) before thinning into noise above jw>=25 (n<=296).

  Checked both cells with the same two robustness tests every other
  apparently-positive Combo result in this file has failed (date-half
  split, exclude-3-biggest-winners) - THIS is the first one that does
  NOT collapse into deeply negative territory under either check: jw>=18
  first-half +5.9%/second-half +1.6% flat (both sides of the split stay
  positive, unlike every prior fragile finding's dramatic sign flip),
  excl-top3-winners +0.6% (still near breakeven, not a collapse); jw>=20
  first-half +11.4%/second-half -0.0% flat (second half is flat, not
  negative), excl-top3-winners +2.0%. Still a real caveat worth stating
  plainly: the effect is meaningfully weaker in the second half of the
  window for both floors, and proportional ROI at jw>=18 does go slightly
  negative in the second half (-2.8%) even though flat ROI doesn't -
  this reads as "a real, modest signal that may be softening or just
  noisy at this sample size", not "a proven, durable edge" the way the
  tracker's own JW_MIN backtests (run on a different, much larger
  same-idea population over more history) were treated. Not yet applied
  anywhere in production (this is Combo's own #1 pick specifically, a
  DIFFERENT population from both the existing tracker rule and the Race
  tab's own display) - a natural next step if this holds up would be
  deciding whether/how to surface it (a new tracker-style rule, a Race
  tab badge, or just left as a documented finding) - not done without
  that decision being made explicitly first.
- **Adding a "not a bad map" (speed_map) filter tested - no improvement,
  and the jockey-only signal itself did not replicate on this smaller
  window (2026-09-19)**: direct follow-up - "what about combo being
  within 5 or 10 and good jockey, and not a bad map".
  `wpr_combo_jockey_map_combo_test.py` (new, read-only scratch script)
  combines Combo gap<=5/gap<=10 (the whole pool, same as
  wpr_combo_5v10_exotics_capture_test.py, not just the #1 pick), a
  jockey_win_pct_90d floor, and a speed_map tag != "unfavoured" filter
  (matches speedmap_jockey_tracker.py's own TAGS=("favoured","neutral")/
  DEMEAN_THRESHOLD=0.5 exactly). Necessarily reads toprate_data.json, not
  toprate_runners.csv (speed_map isn't in the CSV) - which only carries
  ~25 dates of speed_map history (from 2026-08-22 onward), a MUCH
  smaller/more recent population than wpr_combo_jockey_filter_test.py's
  own 121-date one (1,189 races here vs 6,126 there) - confirmed 'ff' in
  toprate_data.json's runner payload is numerically identical to
  pfm_score in toprate_runners.csv for the same run_id before trusting
  Combo could be computed from the JSON at all.

  Whole-pool result (gap<=5/10 x jw floor x map filter): every single
  cell is still ROI-negative, from -18% down to -3% to -10% at the
  tightest floors - excluding "unfavoured" runners gives a small,
  fairly consistent nudge in the right direction at every combination
  (e.g. gap<=5/jw>=20: -7.2% -> -4.8%; gap<=10/jw>=20: -9.8% -> -5.8%)
  but never enough alone to cross into profit.

  Also re-ran the SAME jockey-floor test as the prior entry (Combo's #1
  pick only, not the whole pool) but restricted to this smaller 25-day
  window specifically, to check whether adding the map filter helps that
  already-promising population: it does NOT reach profitability on this
  window either (jw>=18: -4.8%/-4.4% any/excl.unfav; jw>=20: -5.6%/-4.4%)
  - the map filter's own effect here is negligible (a few tenths of a
  percent), not a real lever. This is a real, honest gap with the prior
  entry's own numbers (+3.4%/+4.6% at jw>=18/20 on the full 121-date
  population) - NOT a contradiction though: the prior entry's own
  robustness check already found the SAME jockey rule's second half of
  its full window meaningfully weaker than its first half (jw>=20:
  second-half flat ROI flat at -0.0%), and this 25-day window is exactly
  the most recent tail of that same weaker second half, so a negative
  result here is consistent with, not opposed to, that caveat - it just
  makes the "may be softening or noisy" concern more concrete than
  before. Combined reading: the jockey-quality signal is still the most
  promising thing found in this whole Combo-edge thread, but it has NOT
  been strengthened by adding a map filter, and its own recent-data
  performance is a real, unresolved question mark rather than a settled
  win - more history under this exact rule (not just more slicing of
  the same window) is what would actually resolve it, matching this
  file's own repeated "not enough data yet, revisit later" pattern used
  for jockey_starts_90d/JW_STARTS_MIN elsewhere in this section.
- **Adding an overlay-or-mild-underlay price filter tested - looked
  promising, FAILED the winner-exclusion robustness check (2026-09-19)**:
  direct follow-up - "And either being an overlay, or within n% of the
  price (so not too much of an underlay)". `wpr_combo_jockey_map_price_
  test.py` (new, read-only scratch script, same 25-date speed_map-gated
  toprate_data.json population as the map-filter entry above) adds a
  4th condition on top of gap<=5/10 + jw>=18 + map filter: exclude only
  SEVERE underlays. Fair price/model_prob computed via the same
  softmax formula as wpr_combo_price_overlay_test.py (beta=0.15), over
  the race's own combo-scored-and-priced runners; price_ratio =
  market_price/fair_price; an "underlay tolerance" of N% keeps ratio >=
  1-N/100 (0% = overlay-or-exactly-fair only, no underlay tolerance at
  all).

  Sweeping tolerance 0-25%: the TIGHTEST setting (0%, overlay/fair-only)
  looked like the best row in the whole sweep - gap<=5: n=204, flat ROI
  +5.6%, prop ROI +1.3%; gap<=10: n=258, flat ROI +2.8%, prop ROI +1.2% -
  with ROI degrading steadily and monotonically as more underlay
  tolerance was allowed, consistent with the "severe underlay = bad
  sign" hypothesis. Checked before reporting either as a finding, same
  as always: FAILS the exclude-3-biggest-winners check clearly for both
  (gap<=5: +5.6% -> -6.3%; gap<=10: +2.8% -> -11.2%) - a handful of
  bigger-priced winners are doing all the work, the same fragility
  signature this file has now documented many times over. Date-half
  split was more mixed (gap<=5's two halves both stayed positive,
  +7.9%/+3.5%; gap<=10's flipped sign, -5.1%/+10.3%) but the winner-
  exclusion failure alone is enough to not trust either cell. Not a
  finding - the overlay/underlay-tolerance idea does not rescue the
  jockey+map combination on this window.

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
