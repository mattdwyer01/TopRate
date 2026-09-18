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
