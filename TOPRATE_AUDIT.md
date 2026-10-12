# TopRate dependency audit (13 Oct 2026)

Goal: no TopRate information anywhere. This lists every place TopRate data, ratings or code still sits in the repo, how it got there,
what depends on it, and the order to remove it. Nothing below was deleted except the form-history ratings (phase 1, see the end).

How to read the "source" labels:

- **AUTHORED** means TopRate created it (a rating, an index, a score, a label). It is TopRate's analysis and should go.
- **COMPILED** means a statistic TopRate computed from public results. It can be recomputed from results we hold.
- **FACT** means an observed race fact (finishing order, margin, weight, barrier, price, sectional position, steward report) that reached us
  through TopRate's feed. The original publisher is racing authorities or bookmakers, but our only copy for 2017 to Oct 2026 came from
  TopRate. Whether FACT counts as "TopRate information" is a policy decision (see "Decisions needed").

## 1. Data files

| File | Rows / size | What is in it | Source |
|---|---|---|---|
| `race_results_2017.csv.gz` ... `race_results_2026.csv.gz` | 1.37M runs, 190 MB | `wpr`, `atw` (ratings); `sect_i_*` (sectional index, 12 columns); `raceShapeEarly/Mid/Late`; `wprStatus`, `blackType`; results, margins, weights, barriers, positions (`position800m` etc.), `winners_time`, `time_last600m`, SP and `price_opening/mid/top`; `comments_video`, `comments_steward`; breeding (`sire`, `dam`) | ratings and indices AUTHORED, rest FACT |
| `race_results_2026_rc.csv.gz` | 2.4k runs | our own ratings for 9 to 11 Oct, but CHAINED FROM A TOPRATE SEED (`build_results_ext.py`, `rc_chain.py`) | AUTHORED (seed) |
| `wpr_form_history.csv.gz` | 372k runs, 55 MB | the horse page's Recent runs and chart. `wpr` now OURS (phase 1). Still holds `sect_i_*`, `raceShape*`, `wprStatus`, steward/video comments, price columns | `wpr` replaced, other columns as above |
| `runners.csv`, `runners_archive.csv.gz` | 154 columns | see section 2 | mixed |
| `toprate_runners.csv`, `toprate_runners_archive.csv.gz` | 42 MB + 10 MB | retired frozen copy of the old runner file, same columns as section 2 | AUTHORED + COMPILED |
| `horse_history/*.json` | 81 MB, one file per meeting | full form per horse (built from the form history, so carries the same columns) | follows the form history |
| `toprate_data.json`, `toprate_history.json` (+ `.gz`) | 4 MB + 76 MB | the dashboard payload; keys listed in section 3 | mixed |
| `toprate_price_history.csv` | price snapshots | fixed win prices by run id (despite the name these are bookmaker prices) | FACT |
| `toprate_model_picks.csv` | old pick log | columns `tr_rank`, `early_rank`, `wpr_rank`, ... | AUTHORED |
| `wpr_projection_log.csv.gz` | every logged projection | output of models trained on TopRate ratings (section 4) | derived from AUTHORED |
| `bet_signals_history.json`, `bet_signals.json` | EV per runner | output of the bet model (section 4) | derived from AUTHORED |
| `analysis/wpr_wfa_table.csv` | 453 rows | weight-for-age table used by our own chain; fitted to TopRate ratings (`analysis/wpr_recreate.py`) | AUTHORED (fit) |
| `trip_map.json`, `replay_codes.json`, `tab_dividends.csv` | small | trip map built from results (FACT based), replay codes from TAB, dividends from TAB | FACT / not TopRate |

## 2. `runners.csv` columns

AUTHORED (TopRate's ratings and indices):
`wpr_nett`, `wpr_rank`, `wpr_last1`, `wpr_avg_last3`, `wpr_trend`, `wpr_consistency`, `wpr_peak_rank_1yr`, `wpr_dist`, `wpr_going`, `wpr_dist_n`,
`toprate_rating`, `toprate_price`, `speed_rating`, `pfm_score`, `pfm_score_rank` (form factor), `jockey_rating`, `trainer_rating`,
`early_speed_score`, `mid_speed_score`, `late_speed_score`, `total_speed_score`, `speed_rank_in_race`, `rating_career_best_wpr`,
`rating_career_best_rank`, `rating_career_next_wpr`, `rating_career_next_rank`, `rs_score`, `rs_label`, `race_shape_early/mid/late`,
`wpr_actual` (TopRate's `atw` for races up to 8 Oct; our own for 9 Oct on), `wpr_actual_rank`, `sect_early`, `pace_scenario`, `contested_pace`.

Provenance unknown, needs checking against the capture code: `pf_ai_rank`, `pf_ai_price`, `pf_ai_score`, `pf_class_rank`, `pf_tac_class_rank`,
`pf_time_rank`, `pf_early_time_rank`, `pf_last600_rank`, `pf_last400_rank`, `pf_last200_rank`, `pf_run_style`, `pf_class_change`, `pf_reliable`
(prefix `pf_`, probably a third party's ratings that TopRate republishes; either way they arrive through TopRate).

COMPILED (recomputable from results): `jockey_win_pct_90d`, `trainer_win_pct_365d`, `jt_combo_*`, `jockey_pot_pct_90d`, `trainer_pot_pct_365d`,
`jockey_lt3l_pct_90d`, `trainer_lt3l_pct_365d`, `jockey_starts_90d`, `trainer_starts_365d`, `stats_*` (first up, second up, track, sire wet/dry,
current jockey), `wins_at_dist`, `starts_at_dist`, `places_at_dist`, `going_breakdown`, `form_string`, `runs_with_wpr`, `avg_settled_pos`,
`avg_800m_pos`, `avg_400m_pos`, `weight_trend`, `weight_handicap_today`.

FACT: date, venue, state, race, distance, prize, going, track grading, rail, start time, class, horse, jockey, trainer, barrier, tab number,
weights, prices (`fixed_win_price`, `open_price`, `starting_price_sp`, `price_top`), `finish_position`, `margin_finish`, `won`, `placed`,
scratchings, `comments_video`, `comments_steward`, `silk_url` (silks host is silks.medialityracing.com.au, not TopRate).

OURS: `wprp_*` (projection and bet-signal fields, but see section 4: they come from models trained on TopRate ratings), `wprp_atwo`.

## 3. Dashboard payload and UI

Payload runner keys that carry AUTHORED values: `trr` (TopRate rating), `trp` (TopRate price), `ff` (form factor), `wprt`, `wpr1`, `wpra`, `jrt`, `trt`,
`spd`, `es`, `ms`, `ls`, `ts` (speed scores), plus race keys `rse`, `rsm`, `rsl`, `rs_score`, `rs_label`, `hfs`, `fs`.
`formRuns` and `formAll` (the Recent runs table and chart) now hold OUR ratings in the `wpr` field; their other fields (`se/sm/sl/ie/im/il`
sectional index values) are still TopRate's. `wpja` is TopRate's up to 8 Oct and ours after.
UI (`frontend/src`): the Race table's TopRate, Form and Nett columns, "Jky Win%", jockey/trainer rating tiles, the sectional index panel in the horse
page (`horseParts.tsx`, `CareerStats.tsx`), the TopRate/Form/Nett tiles in `RunnerDetailModal.tsx`, the Combo score (removed from the UI already), and the
help text. `types/data.ts` and `api/adapter.ts` map the raw keys.

## 4. Models and calibration trained on TopRate ratings

- `projection/models/main_seed*.txt.gz`, `light_seed*.txt.gz`, `light_np_seed*.txt.gz`: LightGBM trained with TopRate `wpr` as both label and history
  features, plus `sect_i_*` and `raceShape*` features. This is the model behind Proj, Base, Adj and the waterfall.
- `projection/models/suitability_model.txt` (Speed Map adjustment): fitted on residuals of the old main model; its training script is NOT in the repo, so it
  cannot be retrained without rebuilding it first.
- `projection/models/calibration.json`, `levels.json`, `jockey_impute.json`, `atw_results_scale.json`, `ladder.json`, `pvj_model.txt`, `main_info.json`,
  `light_info.json`: calibration constants, level tables and a finish model, all fitted to TopRate-rated history.
- `betsignal/models/bet_seed*.txt`, `state.pkl` (cache): the bet model uses TopRate-rated form (ratings of past runs) as features, so EV, Model $, the
  Select/Volume tiers and the Rating blend inherit TopRate ratings.
- `wpr_models/` (`projection.joblib`, `pop_adj_models.joblib`, `confidence.joblib`) and `wpr_projection.py`: the previous projection model. It is retired
  as the dashboard's projection, but `toprate_daily.py` still imports parts of `wpr_projection.py`, so it cannot simply be deleted.
- `settling_model.joblib`, `race_speed_model.joblib`, `settling_config.json`, `race_speed_config.json`: trained on positions and sectional data from the
  results files (FACT plus `sect_i_*` AUTHORED).
- `analysis/wpr_wfa_table.csv`: used by our own chain for weight-for-age; fitted to TopRate ratings. The official scale is public and could replace it.
- Own ratings seeded from TopRate: `race_results_2026_rc.csv.gz`, `own_ratings/chain.py`'s `seed_history`, `own_ratings/rc_chain.py`,
  `own_ratings/build_results_ext.py`. The seedless chain (`own_ratings/rebuild_history.py`, section 6) replaces them.

## 5. Code, workflows and credentials

Code that calls TopRate's API or website (`api.toprate.au`, `toprate.au`), mostly through a login with the account in secrets `TOPRATE_EMAIL` and `TOPRATE_PASSWORD`
(14 references in 9 workflows):
`toprate_daily.py`, `toprate_price_refresh.py`, `toprate_json_capture.py`, `toprate_page_discovery.py`, `toprate_field_discovery.py`, `toprate_mcp_server.py`,
`meeting_transfer.py`, `backfill_race_results.py`, `backfill_runner_history.py`, `backfill_atw_historical.py`, `backfill_bulk_meeting_fields.py`.
`tab_fields.py` and `tab_probe_race_fields.py` only mention TopRate in comments.
Workflows that log in: `daily.yml`, `price_refresh.yml`, `backfill_race_results.yml`, `backfill_runner_history.yml`, `backfill_atw_historical.yml`,
`backfill_bulk_meeting_fields.yml`, `field_discovery.yml`, `toprate_login_probe.yml`, `toprate_rpc_probe.yml`. Workflows that only mention TopRate or run its
fetch code: `tab_results.yml`, `rebuild_payload_oneoff.yml`, `rc_fields_daily.yml`, `own_ratings_daily.yml`. (toprate.au has answered 403 on race detail calls since about 5 Oct 2026, so most of this is already dead weight.)
Legacy generators kept for reference: `toprate_html_v3.py` (still imported for its data-JSON half), `wpr_projection.py`.
Documentation: `CLAUDE.md` describes TopRate data throughout.
Git history keeps every old file and rating; deleting them from the working tree does not remove them from history.

## 6. What was done in this change (phase 1)

- `own_ratings/rebuild_history.py`: rates every past run (1.10M runs, Jan 2017 to Oct 2026) with our chain starting from an EMPTY history. Inputs are only
  margin, distance, weight carried, age and sex. The level is pinned to an average of 70 by a causal correction from our own earlier ratings (a scale
  convention, not fitted to TopRate). TopRate's `wpr` is read only by `--validate` to print the comparison below; it never feeds a rating.
- `own_ratings/replace_form_ratings.py`: replaced the `wpr` of every row in `wpr_form_history.csv.gz` with the own rating of the same run. Rows with no own
  rating (barrier trials, jumps races, runs with no margin) are blank, not kept at TopRate's number.
- `atw_offsets.py` returns no offsets, because the form history is now on the plain own scale (there is no "rating at next start's weight" shift to measure).
- `own_ratings/apply_results.py`: new form rows and the settled runners' `wpr_actual` use the own-chain ratings only.
- `.github/workflows/own_ratings_daily.yml`: reruns the history chain nightly (about 4 minutes) before settling and extending the form history.

Quality of the own ratings against TopRate's (comparison only):

| Year | Runs compared | Mean difference (own minus TopRate) | Mean absolute difference | Correlation |
|---|---|---|---|---|
| 2017 | 2,988 | -4.3 | 8.3 | 0.65 |
| 2019 | 38,401 | -4.3 | 7.8 | 0.74 |
| 2021 | 128,405 | -3.2 | 6.0 | 0.84 |
| 2022 | 160,492 | -1.9 | 5.5 | 0.83 |
| 2023 | 180,982 | -0.8 | 4.9 | 0.84 |
| 2024 | 181,284 | +0.1 | 4.9 | 0.83 |
| 2025 | 176,370 | -0.3 | 5.1 | 0.82 |
| 2026 | 135,033 | -0.9 | 5.3 | 0.82 |

- Within a race the order agrees almost perfectly (rank correlation 0.98), because margins set it. The weaker part is comparing races: the typical class
  error of a whole race is about 6 rating points (2021 on), more before that. The first two years are poor because the chain starts with no history.
- Our ratings are less spread out than TopRate's (standard deviation 11.2 against 13.4), so differences between horses look about 16% smaller.
- Form history: 298,722 of 371,775 rows (80%) now carry our rating. Of the 73,053 blank rows, 67,875 never had a TopRate rating either (barrier trials
  and similar); 5,178 had one that we cannot reproduce (mostly runs with no recorded margin). The 4,755 runs from 1 to 11 Oct are included.
- The projection model is still fitted to TopRate's scale. Until phase 2, the horse page shows our rating history next to a projection on TopRate's scale,
  and the two differ by about 5 points per run on average (1 point on average in level).

## 7. Decisions needed

1. **FACT columns.** Keep results, margins, weights, barriers, positions and prices as facts we already hold, or also source them elsewhere? racing.com gives
   margins and results for every state from about Jul 2026 and for VIC/SA/QLD from 2021/2022 (GPS tables), TAB gives prices and results, but 2017 to 2021
   outside VIC/SA/QLD exists only in our TopRate copy.
2. **Retrain on our ratings (phase 2).** The projection and bet models are fitted to TopRate's `wpr`. Replacing `wpr`/`atw` in the results files with the
   own ratings and retraining main, light, calibration, bet model and a rebuilt suitability model removes the dependency but changes every projection and
   EV. Expect lower accuracy first (our ratings are noisier, section 6), so I would compare held-out error and EV backtests before and after and ship
   only if the loss is acceptable.
3. **Sectional index (`sect_i_*`) and race shape.** TopRate-authored and found not to derive from real race time (see CLAUDE.md, "Correction (11 Oct 2026)").
   They gave about 0.004 to 0.006 RMSE in the ladder test, so dropping them costs little.
4. **Frontend.** Remove the TopRate, Form, Nett, jockey/trainer rating and speed score columns and tiles, or replace each with a statistic we compute.
5. **Credentials and code.** Delete the TopRate fetch code, the 9 login workflows and the two secrets once phase 2 no longer needs the daily fetch.
6. **Git history.** Removing old files from the tree leaves them in history; scrubbing history is destructive and needs its own decision.

## 8. Suggested order

1. Phase 1 (this change): form history, offsets, nightly job. Done once merged.
2. Replace `wpr_actual` and `race_results_2026_rc.csv.gz` with the seedless chain; stop using the seeded chain.
3. Phase 2: re-rate the results files, retrain the models, compare, switch.
4. Remove AUTHORED columns from `runners.csv`, the payload and the UI.
5. Delete the fetch code, workflows, secrets, `toprate_runners*.csv`, `wpr_models/`, `wpr_projection.py`; update `CLAUDE.md`.
