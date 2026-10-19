# Horsetorque "Edge" ideas: backtest findings (19 Oct 2026)

Branch `claude/horsetorque-edge-backtest-tjul7l`. Code: `analysis/horsetorque_edge/` (analysis only; nothing in production, `runners.csv`, the payload or the locked rule was changed).
Reproduce: `python analysis/horsetorque_edge/run_all.py` (about 12 minutes), then `python analysis/horsetorque_edge/build_findings.py`.

## Read this first: what could and could not be tested

1. **The locked rule can only be tested on 26 Apr to 8 Oct 2026.** TR rating and the Mid/Late/Total speed scores exist only in the retired TopRate runner files
   (`archive/toprate/`), for 7,158 resulted races. The rule as given (TR rank <= 3, Mid, Late and Total ranks each <= 2, Top price >= $3, fixed-odds win) made
   **885 bets in that window**. The results files carry no TR rating, and the private racing-model repo was not available in this session, so there is no 2016+ version of the locked rule.
   The v3 header in `toprate_html_v3.py` is the only definition in this repo (the picks log shows the `main` model changed definition several times in May 2026); "Mid+Late+Total top 2" is read as each of the three ranks <= 2.
2. **"2016+" is really 2019+.** The results files have almost nothing before 2019 (2016: 83 rows, 2017: about 4k rows, 2018: about 19k rows, with no last-400m and almost no prices):

| year | runs | races | last400 | pos800 | top_price |
|---|---|---|---|---|---|
| 2019 | 38,327 | 3,867 | 97% | 98% | 100% |
| 2020 | 80,649 | 8,052 | 96% | 97% | 100% |
| 2021 | 128,331 | 13,173 | 96% | 97% | 100% |
| 2022 | 160,249 | 16,797 | 94% | 95% | 100% |
| 2023 | 180,698 | 19,064 | 91% | 92% | 100% |
| 2024 | 181,075 | 18,967 | 90% | 92% | 100% |
| 2025 | 176,205 | 18,816 | 91% | 93% | 100% |
| 2026 | 132,367 | 14,133 | 92% | 94% | 100% |

3. **Reference rule P (2019 to 2026) is a stand-in, not the locked rule.** To get an 8-year population I built rule P from as-of results data: last-3 WPR rank <= 3, as-of Mid/Late/Total sectional proxies each rank <= 2, Top >= $3, at least 3 prior runs.
   The proxies match the real columns poorly (within-race rank correlation with the real score: Mid 0.29, Late 0.44, Total 0.77, TR vs last-3 WPR 0.71; `calibrate_proxy.py`). In the 2026 window only 219 of rule P's 3,912 picks are real locked-rule picks (6%), and rule P finds 25% of the real ones.
   Rule P bets 4x as often at longer prices (avg $11.8 vs $5.4). Read results on P as "does this idea move a sectional-form rule", never as "this is what the locked rule would have done". Where the two disagree, trust neither; the real-rule sample is small.
4. **The Top price is a hindsight maximum.** `price_top` is at or above the starting price on 100% of 2019 to 2026 runs (average +10.8%), so it is the best price the horse reached, not a price you can reliably take. Every ROI table therefore shows **ROI at Top and ROI at SP**; the achievable result sits between them.
   The real locked rule returns +4.2% at Top and -5.1% at SP over 885 bets (s.e. about 7 points either way), i.e. it is not distinguishable from zero.
5. **Sectional units.** The results files hold last-400m as `sect_i_l400` in lengths against a per-race standard, not seconds (a per-runner time is not stored; `time_last600m` is a race constant filled on 1 to 30% of races). XR uses 0.147 s per length (the repo-measured figure), so 0.1 s = 1 point = 0.68 lengths.
   Values beyond 15 lengths from the winner are clipped (the columns hold +-100 data errors). These are TopRate-authored columns, read raw on purpose (the production `own_overlay` blanks them).
6. **Model.** A walk-forward logistic regression (train before year Y, test 2023 to 2026, 636k runners, 67.6k races; features demeaned within race; price never a feature) stands in for the racing-model rating model. AUC and log-loss are out of sample. "Gain" is the paired drop in race-level winner log-loss against the base set (positive = better), with its standard error.
7. **Settled position** is `position800m` (`positionSettled` is blank in every file). **F&M and 3YOF rungs** can only be detected from `race_name` (filled on about 15% of rows), so they apply to 0.02% of runs. **Race shape** was projected in the analysis module only; nothing was written to `runners.csv`.
8. **Many looks.** Test 3 is a 12-cell sweep on 885 bets. A cell that looks good there needs to hold in halves and on the second data set before it counts.

## Verdicts

| # | Idea | Verdict |
|---|---|---|
| 1 | Class par ladder | **Worth keeping as a feature, small gain, not a betting edge.** class_par class_move/peak_at_class beat the trackGrading version (+0.0019 vs +0.0007 nats a race, t 9.6) and the retired rung ladder (+0.0014). sr_vs_par adds nothing on top. ROI is unchanged within noise. The Open (non black type) rung of 100 is about 6 points too high against what winners rate. |
| 2 | XR / TOF | **Small model gain (+0.0020 nats, t 5.5), no ROI change, avoid flag not supported.** The flag is rare (0.7% of runs) and flagged runners do not lose more than unflagged ones. |
| 3 | Compression gate | **Not supported.** No gate improves rule P at any of the 12 settings (best -10.0% vs -10.2% ungated; tight gates are worse). The real-rule best cell (+10.6%, n=502) does not hold up when the same gate uses `wpr_nett` (-4.6%). |
| 4 | Golden 8 | **The ~75% claim does not hold as stated.** 91% of all winners settle in the first 8 only because most fields are 8 or fewer. In fields of 9+ it is 86.8% against 73.0% of runners (lift 1.19); 75% is reached only at 13 to 14 runners. A real but modest map effect. Projected map position adds +0.0016 nats. Race shape cannot be projected from settle positions (R2 0.05, 0.00, 0.06). |
| 5a | Price bands / $3 floor | **No case to move the floor.** Below $3 the real rule loses (-5.3% at $1.5-2, -10.8% at $2-3), but $3 vs $2.5 vs $4 vs $5 are all inside one standard error (7 to 12 points), and rule P points the other way. |
| 5b | Dutch top 4, outlay < 80% | **Loses.** -6.9% at Top and -15.6% at SP over 38.7k model races (59% strike); market top 4 (-4.8% at Top) and TopRate-rank top 4 (-6.3% at Top, -14.5% at SP) are similar. Not a useful benchmark to beat. |

---
## Test 1: class par ladder

### 1a. Ladder coverage and whether par tracks the ratings (2019-2026 flat runs)

class_par mapped on 99.98% of runs. F&M / 3YOF rungs could be applied to only 0.019% of runs (race_name is filled on ~15% of rows), so they are effectively unused.

| par_band | runs | mean_wpr | winner_mean_wpr |
|---|---|---|---|
| 86 Maiden | 315983 | 64.5 | 77.5 |
| 86.5-90 low BM/CLS | 96287 | 66.4 | 77.3 |
| 90-92 BM62-ish | 368335 | 71.6 | 82.1 |
| 92-94 | 101249 | 76.5 | 86.2 |
| 94-96.5 | 86934 | 78.6 | 87.8 |
| 96.5-99 | 21818 | 82.2 | 91.3 |
| 99-101 Open/LR | 67107 | 78.2 | 86.7 |
| 101-104 G3/LR | 9970 | 88.7 | 97.5 |
| 104-108 G2 | 5675 | 89.8 | 99.5 |
| 108+ G1 | 4327 | 92.9 | 102.8 |

Correlation of each class measure with the run rating (higher = the ladder really measures class):

| ladder | spearman_with_wpr | pearson_with_wpr |
|---|---|---|
| trackGrading (bug) | 0.029 | -0.004 |
| retired rung ladder | 0.490 | 0.391 |
| class_par | 0.482 | 0.419 |

Calibration of the rungs (winners only): if the ladder were in WPR points, winner WPR minus par would be flat down the table.

| grp | races | par | winner_wpr | winner_wpr_minus_par |
|---|---|---|---|---|
| G1 | 501 | 108.4 | 101.9 | -6.5 |
| G2 | 636 | 104.8 | 98.1 | -6.7 |
| G3 | 1115 | 100.8 | 96.6 | -4.2 |
| LR | 1699 | 99.1 | 94.8 | -4.3 |
| BM/CLS 94+ | 1570 | 98.6 | 87.6 | -11.0 |
| Open (no black type) | 8517 | 97.9 | 85.7 | -12.2 |
| BM/CLS 84-93 | 1825 | 96.4 | 90.3 | -6.1 |
| BM/CLS 74-83 | 7394 | 94.1 | 87.1 | -7.0 |
| BM/CLS 62-73 | 33093 | 91.6 | 84.1 | -7.6 |
| BM/CLS below 62 | 23699 | 89.9 | 78.6 | -11.3 |
| Maiden | 32820 | 86.0 | 77.5 | -8.5 |

### 1b. Out-of-sample model comparison (train before year Y, test 2023-2026)

Gain = paired reduction in race-level winner log-loss vs base (positive = better); t = gain / s.e. over races.

| variant | runners | races | auc | logloss | race_ll | race_ll_gain_vs_base | gain_se | gain_t | top1 |
|---|---|---|---|---|---|---|---|---|---|
| base | 635998 | 67585 | 0.7229 | 0.3082 | 1.9392 | n/a | n/a | n/a | 27.42 |
| +class_move/peak (trackGrading bug) | 635998 | 67585 | 0.7232 | 0.3081 | 1.9385 | +0.0007 | 0.0001 | +6.3 | 27.56 |
| +class_move/peak (retired rung ladder) | 635998 | 67585 | 0.7237 | 0.3080 | 1.9378 | +0.0014 | 0.0002 | +8.8 | 27.60 |
| +class_move/peak (class_par) | 635998 | 67585 | 0.7239 | 0.3079 | 1.9372 | +0.0019 | 0.0002 | +9.6 | 27.67 |
| +class_par +sr_vs_par | 635998 | 67585 | 0.7239 | 0.3079 | 1.9372 | +0.0019 | 0.0002 | +9.0 | 27.71 |
| +sr_vs_par only | 635998 | 67585 | 0.7237 | 0.3080 | 1.9378 | +0.0014 | 0.0002 | +7.8 | 27.69 |

### 1c. ROI at the Top price (flat 1 unit, fixed-odds win), model gates on the two rule populations

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| base: model #1, Top>=$3 | 47,464 | 8,939 | 18.8 | 6.16 | -9.8 | 1.0 | -16.9 | -10.1 | -9.3 | -10.3 |
| base: rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| base: rule P + model rank<=2 | 18,004 | 3,387 | 18.8 | 6.46 | -6.2 | 1.9 | -14.8 | -7.5 | -4.1 | -8.3 |
| base: locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| base: locked rule + model rank<=2 | 506 | 114 | 22.5 | 4.96 | -0.1 | 8.7 | -7.9 | -4.6 | -4.1 | +3.8 |
| +class_move/peak (class_par): model #1, Top>=$3 | 47,156 | 8,984 | 19.1 | 6.07 | -9.1 | 1.0 | -16.2 | -9.5 | -8.3 | -9.9 |
| +class_move/peak (class_par): rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| +class_move/peak (class_par): rule P + model rank<=2 | 17,868 | 3,371 | 18.9 | 6.42 | -6.3 | 1.9 | -14.9 | -7.6 | -3.9 | -8.7 |
| +class_move/peak (class_par): locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| +class_move/peak (class_par): locked rule + model rank<=2 | 507 | 116 | 22.9 | 4.98 | +2.6 | 8.9 | -5.1 | -1.9 | -2.2 | +7.3 |
| +class_par +sr_vs_par: model #1, Top>=$3 | 47,136 | 9,008 | 19.1 | 6.08 | -8.7 | 1.0 | -15.8 | -9.1 | -8.2 | -9.1 |
| +class_par +sr_vs_par: rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| +class_par +sr_vs_par: rule P + model rank<=2 | 17,854 | 3,366 | 18.9 | 6.44 | -6.4 | 1.9 | -15.1 | -7.7 | -4.7 | -8.2 |
| +class_par +sr_vs_par: locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| +class_par +sr_vs_par: locked rule + model rank<=2 | 511 | 117 | 22.9 | 4.98 | +3.2 | 8.9 | -4.6 | -1.2 | -0.3 | +6.6 |


## Test 2: winner-anchored sectional rating (XR) and TOF

XR = winner WPR + (runner last-400m - winner last-400m) converted at 1 point per 0.1 s, TOF = XR - WPR. The results files hold last-400m as `sect_i_l400` in LENGTHS vs a per-race standard (per-runner last-400m times are not stored; only the winner has a time, and only on 1-30% of races), so lengths are converted at 0.147 s per length (1.47 points per length). The repo's own rating-per-length slope is ~2.15, so 1.47 compresses XR relative to WPR (TOF averages +5.8); a 2.15 version is reported as a sensitivity. Differences beyond +-15 lengths are clipped (sect_i columns hold +-100 data errors). Coverage: XR on 93% of runs.

### 2a. Retrain with vs without XR / TOF / TOF rank (train before Y, test 2023-2026)

| variant | runners | races | auc | logloss | race_ll | race_ll_gain_vs_base | gain_se | gain_t | top1 |
|---|---|---|---|---|---|---|---|---|---|
| base + class_par | 635998 | 67585 | 0.7239 | 0.3079 | 1.9372 | n/a | n/a | n/a | 27.67 |
| + XR/TOF/TOF rank | 635998 | 67585 | 0.7244 | 0.3075 | 1.9352 | +0.0020 | 0.0004 | +5.5 | 27.54 |
| + TOF only | 635998 | 67585 | 0.7243 | 0.3076 | 1.9356 | +0.0016 | 0.0003 | +4.8 | 27.51 |
| + XR only | 635998 | 67585 | 0.7241 | 0.3078 | 1.9365 | +0.0008 | 0.0002 | +3.5 | 27.70 |

### 2b. ROI at the Top price with the model as a gate on the rule populations

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| base + class_par: model #1, Top>=$3 | 47,156 | 8,984 | 19.1 | 6.07 | -9.1 | 1.0 | -16.2 | -9.5 | -8.3 | -9.9 |
| base + class_par: rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| base + class_par: rule P + model rank<=2 | 17,868 | 3,371 | 18.9 | 6.42 | -6.3 | 1.9 | -14.9 | -7.6 | -3.9 | -8.7 |
| base + class_par: locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| base + class_par: locked rule + model rank<=2 | 507 | 116 | 22.9 | 4.98 | +2.6 | 8.9 | -5.1 | -1.9 | -2.2 | +7.3 |
| + XR/TOF/TOF rank: model #1, Top>=$3 | 47,614 | 9,070 | 19.0 | 6.16 | -8.2 | 1.0 | -15.4 | -8.5 | -7.3 | -9.1 |
| + XR/TOF/TOF rank: rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| + XR/TOF/TOF rank: rule P + model rank<=2 | 17,819 | 3,345 | 18.8 | 6.50 | -6.4 | 1.9 | -15.1 | -7.7 | -4.8 | -8.1 |
| + XR/TOF/TOF rank: locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| + XR/TOF/TOF rank: locked rule + model rank<=2 | 520 | 119 | 22.9 | 5.00 | +0.9 | 8.6 | -7.1 | -3.5 | +2.9 | -1.1 |

### 2c. Avoid flag: TOF<0 last start AND rear third at the 800m call AND weight up OR distance up (flag known before the race)

Flag set on 6,790 runs (0.7% of runs where it can be computed; needs a prior TOF and 800m position). It is rare by construction: horses that settle in the rear third almost always finish with a positive TOF (they pass tiring runners), so TOF<0 AND rear third is a narrow corner. The race-relative version (TOF below the race mean) is flagged on 46,551 runs (5.0%).

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| flag set (all runners) | 6,789 | 849 | 12.5 | 17.32 | -15.3 | 4.1 | -22.6 | -18.4 | -10.9 | -19.8 |
| flag not set (all runners) | 915,316 | 97,232 | 10.6 | 25.78 | -17.7 | 0.4 | -26.2 | -17.8 | -16.0 | -19.4 |
| flag set, Top >= $3 | 6,307 | 658 | 10.4 | 18.47 | -15.6 | 4.4 | -23.0 | -18.9 | -11.9 | -19.2 |
| flag not set, Top >= $3 | 864,923 | 75,471 | 8.7 | 27.15 | -18.5 | 0.4 | -27.1 | -18.6 | -16.7 | -20.3 |
| flag set, 2.15 pts/length XR | 15,869 | 1,615 | 10.2 | 24.31 | -19.4 | 2.9 | -26.9 | -21.3 | -19.9 | -18.8 |
| flag not set, 2.15 pts/length XR | 906,236 | 96,466 | 10.6 | 25.75 | -17.6 | 0.4 | -26.1 | -17.7 | -15.9 | -19.4 |
| flag set, race-relative TOF (TOF below the race mean) | 46,549 | 6,276 | 13.5 | 16.32 | -18.3 | 1.4 | -25.5 | -18.9 | -19.1 | -17.5 |
| flag not set, race-relative TOF | 875,556 | 91,805 | 10.5 | 26.22 | -17.6 | 0.4 | -26.2 | -17.7 | -15.8 | -19.5 |
| race-relative flag set, Top >= $3 | 42,419 | 4,485 | 10.6 | 17.69 | -19.7 | 1.6 | -27.0 | -20.4 | -20.6 | -18.7 |
| race-relative flag not set, Top >= $3 | 828,811 | 71,644 | 8.6 | 27.57 | -18.4 | 0.5 | -27.0 | -18.5 | -16.5 | -20.3 |
| rule P picks with flag | 672 | 98 | 14.6 | 8.81 | -21.6 | 8.3 | -29.1 | -28.2 | -7.3 | -35.8 |
| rule P picks without flag | 59,286 | 8,397 | 14.2 | 13.33 | -9.5 | 1.3 | -18.6 | -10.1 | -8.7 | -10.2 |
| rule P picks with race-relative flag | 4,530 | 710 | 15.7 | 9.15 | -11.5 | 3.7 | -20.1 | -14.0 | -19.4 | -3.7 |
| rule P picks without race-relative flag | 55,428 | 7,785 | 14.0 | 13.61 | -9.4 | 1.3 | -18.6 | -10.2 | -8.1 | -10.8 |
| locked rule picks with race-relative flag (2026) | 99 | 24 | 24.2 | 5.40 | +26.2 | 23.8 | +12.5 | +4.6 | +65.5 | -12.4 |
| locked rule picks without race-relative flag (2026) | 747 | 164 | 22.0 | 5.37 | +2.2 | 7.5 | -6.7 | -1.4 | +8.8 | -4.2 |
| locked rule picks with flag (2026) | 16 | 4 | 25.0 | 5.26 | +28.8 | 61.7 | +26.9 | -71.5 | +8.8 | +48.8 |
| locked rule picks without flag (2026) | 830 | 184 | 22.2 | 5.37 | +4.6 | 7.2 | -5.0 | +1.3 | +15.0 | -5.7 |

Win rate vs the book-normalised market-implied rate (a flag that the price already holds shows no gap):

| avoid | n | win_rate | market_implied |
|---|---|---|---|
| flag not set | 915316 | 10.62 | 12.09 |
| flag set | 6789 | 12.51 | 13.67 |

### 2d. TOF rank as a stand-alone selection (as-of last-3 mean TOF, fields of 6+)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| TOF rank 1 (as-of last-3 mean), Top >= $3 | 105,951 | 5,347 | 5.0 | 50.03 | -27.7 | 1.6 | -36.6 | -28.3 | -26.3 | -29.1 |
| TOF rank <= 2 | 210,149 | 12,207 | 5.8 | 43.75 | -25.6 | 1.1 | -34.5 | -26.0 | -23.8 | -27.5 |
| TOF rank last | 107,976 | 12,961 | 12.0 | 14.59 | -14.8 | 1.0 | -22.3 | -15.2 | -11.7 | -17.9 |


## Test 3: race compression gate

Model rating = ridge regression of the run WPR (race-relative) on the as-of features (base + class_par), walk-forward 2023-2026. `compressed(thr, N)` = at least N runners (rank 1 included) rated within `thr` points of rank 1. Gate = skip a pick when its race is compressed. The sweep is 12 thresholds, so read it against the halves columns, not the single best row.

| stat | mean | 25% | 50% | 75% |
|---|---|---|---|---|
| gap_1_5 | 5.86 | 3.48 | 5.09 | 7.29 |
| field | 8.99 | 7.00 | 9.00 | 11.00 |
| n_within_3 | 2.97 | 2.00 | 3.00 | 4.00 |
| n_within_4 | 3.81 | 2.00 | 4.00 | 5.00 |
| n_within_5 | 4.64 | 3.00 | 4.00 | 6.00 |
| n_within_6 | 5.42 | 4.00 | 5.00 | 7.00 |

### 3a. rule P (2023-2026)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| no gate | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| skip compressed: >= 4 within 3 pts (kept 71%) | 26,745 | 4,005 | 15.0 | 12.56 | -10.2 | 1.8 | -19.0 | -11.2 | -8.5 | -11.8 |
| skip compressed: >= 5 within 3 pts (kept 86%) | 32,081 | 4,836 | 15.1 | 12.13 | -10.2 | 1.6 | -19.0 | -11.1 | -8.9 | -11.6 |
| skip compressed: >= 6 within 3 pts (kept 94%) | 35,111 | 5,276 | 15.0 | 11.93 | -10.0 | 1.5 | -18.7 | -10.8 | -8.5 | -11.4 |
| skip compressed: >= 4 within 4 pts (kept 54%) | 20,273 | 2,976 | 14.7 | 13.44 | -11.6 | 2.1 | -20.4 | -13.0 | -10.9 | -12.3 |
| skip compressed: >= 5 within 4 pts (kept 73%) | 27,171 | 4,088 | 15.0 | 12.57 | -10.9 | 1.8 | -19.6 | -11.9 | -10.2 | -11.5 |
| skip compressed: >= 6 within 4 pts (kept 85%) | 31,907 | 4,817 | 15.1 | 12.10 | -10.1 | 1.6 | -18.9 | -11.0 | -8.9 | -11.4 |
| skip compressed: >= 4 within 5 pts (kept 39%) | 14,631 | 2,069 | 14.1 | 14.53 | -14.3 | 2.5 | -22.9 | -16.3 | -17.2 | -11.4 |
| skip compressed: >= 5 within 5 pts (kept 58%) | 21,848 | 3,268 | 15.0 | 13.22 | -11.1 | 2.0 | -19.7 | -12.4 | -11.3 | -11.0 |
| skip compressed: >= 6 within 5 pts (kept 74%) | 27,671 | 4,183 | 15.1 | 12.48 | -10.3 | 1.8 | -19.0 | -11.4 | -10.4 | -10.2 |
| skip compressed: >= 4 within 6 pts (kept 28%) | 10,435 | 1,443 | 13.8 | 15.93 | -16.0 | 3.1 | -24.4 | -18.6 | -17.4 | -14.6 |
| skip compressed: >= 5 within 6 pts (kept 45%) | 16,954 | 2,488 | 14.7 | 14.18 | -12.4 | 2.3 | -21.0 | -14.2 | -12.7 | -12.2 |
| skip compressed: >= 6 within 6 pts (kept 62%) | 23,281 | 3,482 | 15.0 | 13.04 | -11.2 | 1.9 | -19.8 | -12.4 | -11.0 | -11.4 |

### 3a. locked rule, real (Apr-Oct 2026)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| no gate | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| skip compressed: >= 4 within 3 pts (kept 74%) | 646 | 143 | 22.1 | 5.33 | +1.6 | 8.0 | -7.0 | -2.6 | +10.0 | -6.6 |
| skip compressed: >= 5 within 3 pts (kept 86%) | 745 | 167 | 22.4 | 5.33 | +3.6 | 7.5 | -5.4 | -0.0 | +10.1 | -2.8 |
| skip compressed: >= 6 within 3 pts (kept 94%) | 814 | 178 | 21.9 | 5.35 | +1.7 | 7.2 | -7.2 | -1.6 | +10.0 | -6.5 |
| skip compressed: >= 4 within 4 pts (kept 54%) | 474 | 100 | 21.1 | 5.32 | -0.8 | 9.5 | -8.5 | -6.5 | +1.9 | -3.4 |
| skip compressed: >= 5 within 4 pts (kept 73%) | 638 | 140 | 21.9 | 5.36 | +0.9 | 8.1 | -7.8 | -3.4 | +10.1 | -8.3 |
| skip compressed: >= 6 within 4 pts (kept 85%) | 742 | 164 | 22.1 | 5.33 | +2.0 | 7.5 | -6.9 | -1.6 | +10.9 | -6.8 |
| skip compressed: >= 4 within 5 pts (kept 39%) | 341 | 67 | 19.6 | 5.45 | -6.2 | 11.1 | -14.2 | -14.2 | +2.1 | -14.3 |
| skip compressed: >= 5 within 5 pts (kept 58%) | 502 | 118 | 23.5 | 5.35 | +10.6 | 9.6 | +2.0 | +5.2 | +19.0 | +2.2 |
| skip compressed: >= 6 within 5 pts (kept 76%) | 658 | 150 | 22.8 | 5.30 | +6.3 | 8.2 | -3.0 | +2.2 | +17.4 | -4.8 |
| skip compressed: >= 4 within 6 pts (kept 28%) | 246 | 45 | 18.3 | 5.50 | -15.7 | 12.1 | -21.5 | -24.9 | -13.0 | -18.2 |
| skip compressed: >= 5 within 6 pts (kept 47%) | 406 | 87 | 21.4 | 5.29 | +1.8 | 10.5 | -5.6 | -4.8 | +6.3 | -2.5 |
| skip compressed: >= 6 within 6 pts (kept 63%) | 552 | 124 | 22.5 | 5.28 | +5.5 | 9.0 | -2.7 | +0.6 | +14.2 | -3.0 |

### 3b. rule P (2023-2026): ROI by gap_1_5 quartile (larger gap = less compressed)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| gap_1_5 0.0 to 3.8 | 9,365 | 1,344 | 14.4 | 9.85 | -10.6 | 2.8 | -19.1 | -12.3 | -9.3 | -11.9 |
| gap_1_5 3.8 to 5.5 | 9,365 | 1,477 | 15.8 | 9.98 | -6.0 | 2.8 | -15.6 | -7.3 | -3.7 | -8.3 |
| gap_1_5 5.5 to 7.9 | 9,365 | 1,446 | 15.4 | 11.03 | -8.3 | 3.3 | -17.2 | -11.1 | -2.2 | -14.5 |
| gap_1_5 7.9 to 48.5 | 9,365 | 1,326 | 14.2 | 16.40 | -16.0 | 2.9 | -24.0 | -18.1 | -21.4 | -10.6 |

### 3b. locked rule, real (Apr-Oct 2026): ROI by gap_1_5 quartile (larger gap = less compressed)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| gap_1_5 0.3 to 3.8 | 218 | 47 | 21.6 | 5.45 | +9.9 | 14.9 | -3.1 | +0.5 | +22.4 | -2.6 |
| gap_1_5 3.8 to 5.6 | 217 | 52 | 24.0 | 5.33 | +3.6 | 13.0 | -5.3 | -5.0 | -0.3 | +7.3 |
| gap_1_5 5.6 to 7.9 | 218 | 50 | 22.9 | 5.27 | +14.4 | 15.7 | +2.9 | +2.0 | +51.4 | -21.4 |
| gap_1_5 7.9 to 38.5 | 219 | 42 | 19.2 | 5.45 | -14.6 | 12.4 | -18.9 | -23.8 | -15.1 | -14.2 |

### 3c. Locked rule (real) gated on compression of TopRate's own pre-race wpr_nett

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| locked rule, no gate | 885 | 195 | 22.0 | 5.37 | +4.2 | 7.1 | -5.1 | +0.9 | +14.3 | -5.8 |
| wpr_nett: skip >= 4 within 3 (kept 77%) | 681 | 149 | 21.9 | 5.45 | +2.4 | 8.0 | -6.1 | -1.9 | +15.4 | -10.0 |
| wpr_nett: skip >= 5 within 3 (kept 88%) | 783 | 171 | 21.8 | 5.38 | +1.7 | 7.4 | -7.0 | -2.1 | +12.0 | -8.7 |
| wpr_nett: skip >= 6 within 3 (kept 95%) | 845 | 187 | 22.1 | 5.36 | +4.1 | 7.2 | -5.1 | +0.6 | +15.1 | -6.9 |
| wpr_nett: skip >= 4 within 4 (kept 62%) | 552 | 117 | 21.2 | 5.43 | -0.7 | 8.8 | -9.0 | -6.1 | +19.7 | -20.6 |
| wpr_nett: skip >= 5 within 4 (kept 76%) | 677 | 148 | 21.9 | 5.42 | +2.1 | 8.0 | -6.3 | -2.3 | +14.6 | -10.4 |
| wpr_nett: skip >= 6 within 4 (kept 88%) | 776 | 170 | 21.9 | 5.39 | +1.9 | 7.4 | -6.5 | -1.9 | +14.4 | -10.4 |
| wpr_nett: skip >= 4 within 5 (kept 46%) | 409 | 80 | 19.6 | 5.50 | -10.1 | 9.7 | -16.2 | -16.6 | +4.3 | -23.9 |
| wpr_nett: skip >= 5 within 5 (kept 64%) | 563 | 116 | 20.6 | 5.38 | -4.6 | 8.5 | -11.9 | -9.9 | +4.3 | -13.0 |
| wpr_nett: skip >= 6 within 5 (kept 79%) | 696 | 150 | 21.6 | 5.37 | -0.6 | 7.7 | -8.7 | -4.8 | +9.7 | -10.8 |
| wpr_nett: skip >= 4 within 6 (kept 36%) | 321 | 63 | 19.6 | 5.49 | -9.5 | 11.0 | -15.7 | -17.3 | +1.0 | -19.9 |
| wpr_nett: skip >= 5 within 6 (kept 52%) | 459 | 96 | 20.9 | 5.40 | -2.6 | 9.6 | -9.6 | -9.1 | +5.3 | -9.9 |
| wpr_nett: skip >= 6 within 6 (kept 68%) | 606 | 129 | 21.3 | 5.37 | -1.1 | 8.3 | -8.5 | -6.0 | +7.5 | -9.6 |


## Test 4: race shape and the Golden 8

"Settled position" is the 800m call (`position800m`): `positionSettled` is blank in every results file. For sprints this call is close to the start, for staying races it is mid-race. Only races where the winner and at least 80% of the field have an 800m position are used.

### 4a. Winners by settled position (104,406 races, all field sizes)

| settled_position | runners | winners | winner_share_pct | cumulative_pct | win_rate_pct | avg_top_price |
|---|---|---|---|---|---|---|
| 1 | 104396 | 22048 | 21.1 | 21.1 | 21.1 | 18.4 |
| 2 | 104378 | 14765 | 14.1 | 35.3 | 14.1 | 19.6 |
| 3 | 104400 | 13180 | 12.6 | 47.9 | 12.6 | 20.9 |
| 4 | 104254 | 12487 | 12.0 | 59.8 | 12.0 | 21.3 |
| 5 | 103508 | 10591 | 10.1 | 70.0 | 10.2 | 23.3 |
| 6 | 100934 | 9071 | 8.7 | 78.7 | 9.0 | 25.8 |
| 7 | 95138 | 7341 | 7.0 | 85.7 | 7.7 | 28.6 |
| 8 | 85117 | 5517 | 5.3 | 91.0 | 6.5 | 31.9 |
| 9 | 71068 | 3933 | 3.8 | 94.8 | 5.5 | 35.6 |
| 10 | 55141 | 2544 | 2.4 | 97.2 | 4.6 | 39.7 |
| 11 | 37988 | 1534 | 1.5 | 98.7 | 4.0 | 43.5 |
| 12 | 24329 | 782 | 0.7 | 99.4 | 3.2 | 47.6 |
| 13+ | 22435 | 613 | 0.6 | 100.0 | 2.7 | 53.6 |

### 4b. First-8 share by field size (the claim only has content when the field is larger than 8)

| field_size | races | winners_in_first8_pct | runners_in_first8_pct | lift | win_rate_first8 | win_rate_9plus |
|---|---|---|---|---|---|---|
| <=8 | 32965 | 100.0 | 100.0 | 1.00 | 14.3 | n/a |
| 9-10 | 33047 | 92.8 | 84.2 | 1.10 | 11.6 | 4.8 |
| 11-12 | 26011 | 84.9 | 69.9 | 1.22 | 10.6 | 4.4 |
| 13-14 | 10124 | 76.3 | 59.6 | 1.28 | 9.5 | 4.4 |
| 15-24 | 2142 | 66.8 | 51.0 | 1.31 | 8.4 | 4.3 |
| 9+ all | 71324 | 86.8 | 73.0 | 1.19 | 10.9 | 4.5 |

### 4c. Fields of 9+ by distance

| distance | races | winners_in_first8_pct | runners_in_first8_pct | lift |
|---|---|---|---|---|
| <=1100 | 15134 | 90.0 | 75.2 | 1.20 |
| 1101-1300 | 21197 | 87.6 | 73.0 | 1.20 |
| 1301-1600 | 23285 | 85.4 | 71.8 | 1.19 |
| 1601-2000 | 7457 | 83.8 | 72.7 | 1.15 |
| 2000+ | 4250 | 84.7 | 72.6 | 1.17 |

### 4d. Projected map position (mean 800m position of the last 3 starts) in fields of 9+

| measure | value |
|---|---|
| Spearman: projected avg settle vs actual 800m position | 0.426 |
| runners projected in first 8 (rank<=8) who actually settle in first 8, % | 80.381 |
| winners with projected rank <= 8, % (fields 9+) | 81.740 |
| runners with projected rank <= 8, % (fields 9+) | 76.721 |
| win rate, projected rank <= 8, % | 9.821 |
| win rate, projected rank > 8, % | 7.230 |

### 4e. Race shape projected from settling positions (race_shape_early / mid / late)

Race-level ridge regression of TopRate's realised raceShapeEarly/Mid/Late on pre-race pace pressure (number of horses whose average settle is 3 or better, mean settle of the 3 most forward, field size, early-speed history, distance), walk-forward 2023-2026. This is the version of "populate race_shape" that can be known before the race; the realised values are post-race and are what the runners file would hold after the result.

| target | races | r2_out_of_sample | corr | corr_n_leaders |
|---|---|---|---|---|
| raceShapeEarly | 64032 | 0.045 | 0.214 | 0.137 |
| raceShapeMid | 62272 | 0.000 | 0.018 | 0.007 |
| raceShapeLate | 64032 | 0.059 | 0.244 | -0.176 |

### 4f. Retrain with projected map position (settle_m3_pos, map_rank_pct, golden8 flag)

| variant | runners | races | auc | logloss | race_ll | race_ll_gain_vs_base | gain_se | gain_t | top1 |
|---|---|---|---|---|---|---|---|---|---|
| base + class_par | 635998 | 67585 | 0.7239 | 0.3079 | 1.9372 | n/a | n/a | n/a | 27.67 |
| + projected map position (avg settle, rank pct, first-8 flag) | 635998 | 67585 | 0.7246 | 0.3077 | 1.9357 | +0.0016 | 0.0002 | +7.5 | 27.78 |

### 4g. ROI at the Top price with the model as a gate

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| base + class_par: model #1, Top>=$3 | 47,156 | 8,984 | 19.1 | 6.07 | -9.1 | 1.0 | -16.2 | -9.5 | -8.3 | -9.9 |
| base + class_par: rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| base + class_par: rule P + model rank<=2 | 17,868 | 3,371 | 18.9 | 6.42 | -6.3 | 1.9 | -14.9 | -7.6 | -3.9 | -8.7 |
| base + class_par: locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| base + class_par: locked rule + model rank<=2 | 507 | 116 | 22.9 | 4.98 | +2.6 | 8.9 | -5.1 | -1.9 | -2.2 | +7.3 |
| + projected map position (avg settle, rank pct, first-8 flag): model #1, Top>=$3 | 47,301 | 9,082 | 19.2 | 6.08 | -8.0 | 1.0 | -15.2 | -8.5 | -7.3 | -8.8 |
| + projected map position (avg settle, rank pct, first-8 flag): rule P (population, no gate) | 37,457 | 5,593 | 14.9 | 11.81 | -10.2 | 1.5 | -19.0 | -11.0 | -9.4 | -11.1 |
| + projected map position (avg settle, rank pct, first-8 flag): rule P + model rank<=2 | 17,378 | 3,277 | 18.9 | 6.40 | -7.2 | 1.9 | -15.7 | -8.5 | -6.1 | -8.2 |
| + projected map position (avg settle, rank pct, first-8 flag): locked rule (real, 2026) | 870 | 191 | 22.0 | 5.38 | +3.5 | 7.1 | -5.9 | +0.4 | +11.4 | -4.3 |
| + projected map position (avg settle, rank pct, first-8 flag): locked rule + model rank<=2 | 492 | 112 | 22.8 | 4.92 | -0.2 | 8.8 | -7.9 | -4.8 | -7.5 | +7.0 |


## Test 5: sanity checks

### 5a. Locked rule (real, Apr-Oct 2026) by Top price band, rule applied WITHOUT the $3 floor

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| Top $1.5-2 | 78 | 43 | 55.1 | 1.74 | -5.3 | 9.8 | -9.7 | -9.3 | +17.9 | -27.3 |
| Top $2-3 | 219 | 81 | 37.0 | 2.47 | -10.8 | 8.0 | -14.7 | -13.5 | -13.7 | -8.0 |
| Top $3-5 | 473 | 124 | 26.2 | 3.86 | -1.4 | 7.7 | -8.5 | -3.8 | +6.7 | -9.1 |
| Top $5-7 | 231 | 48 | 20.8 | 5.67 | +17.3 | 15.2 | +6.2 | +10.3 | +17.0 | +17.7 |
| Top $7-+ | 181 | 23 | 12.7 | 8.93 | +2.2 | 20.2 | -10.8 | -14.3 | +30.6 | -25.8 |

Cumulative floors (a bet is placed at or above the floor):

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| Top floor $1.5 | 1,182 | 319 | 27.0 | 4.59 | +0.8 | 5.5 | -7.2 | -1.7 | +9.1 | -7.1 |
| Top floor $2.0 | 1,104 | 276 | 25.0 | 4.79 | +1.3 | 5.9 | -7.0 | -1.4 | +9.4 | -6.9 |
| Top floor $2.5 | 996 | 233 | 23.4 | 5.07 | +2.8 | 6.4 | -6.0 | -0.1 | +10.9 | -4.9 |
| Top floor $3.0 | 885 | 195 | 22.0 | 5.37 | +4.2 | 7.1 | -5.1 | +0.9 | +14.3 | -5.8 |
| Top floor $4.0 | 622 | 113 | 18.2 | 6.19 | +3.1 | 9.1 | -7.2 | -1.7 | +22.0 | -15.7 |
| Top floor $5.0 | 412 | 71 | 17.2 | 7.10 | +10.7 | 12.3 | -1.3 | +3.5 | +26.5 | -5.1 |

Same rule settled at the starting price instead (Top is never below SP, so it behaves like the best price seen rather than a price you can take at will; SP is the sensitivity):

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| SP floor $1.5 | 1,172 | 314 | 26.8 | 4.28 | -7.0 | 5.1 | n/a | -9.1 | -0.9 | -12.8 |
| SP floor $2.0 | 1,081 | 266 | 24.6 | 4.49 | -6.8 | 5.5 | n/a | -9.1 | -1.2 | -12.3 |
| SP floor $2.5 | 960 | 222 | 23.1 | 4.78 | -5.0 | 6.0 | n/a | -7.7 | +2.1 | -11.8 |
| SP floor $3.0 | 816 | 173 | 21.2 | 5.14 | -4.5 | 6.8 | n/a | -7.6 | +5.2 | -14.1 |
| SP floor $4.0 | 546 | 93 | 17.0 | 5.98 | -7.5 | 9.1 | n/a | -12.2 | +1.7 | -16.7 |
| SP floor $5.0 | 346 | 53 | 15.3 | 6.89 | -4.5 | 12.4 | n/a | -11.8 | -1.2 | -7.8 |

Reference rule P without the floor (2019-2026, as-of proxy, NOT the locked rule):

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| Top $1.5-2 | 3,364 | 1,846 | 54.9 | 1.75 | -4.5 | 1.5 | -10.0 | -4.5 | -4.2 | -4.7 |
| Top $2-3 | 9,722 | 3,769 | 38.8 | 2.47 | -5.6 | 1.2 | -11.6 | -5.6 | -0.4 | -10.7 |
| Top $3-5 | 19,007 | 4,688 | 24.7 | 3.86 | -6.7 | 1.2 | -14.2 | -6.7 | -5.4 | -8.0 |
| Top $5-7 | 11,500 | 1,889 | 16.4 | 5.70 | -7.3 | 2.0 | -15.5 | -7.4 | -4.9 | -9.7 |
| Top $7-+ | 32,422 | 2,339 | 7.2 | 21.55 | -12.1 | 2.2 | -22.2 | -13.3 | -10.6 | -13.6 |

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| Top floor $1.5 | 76,015 | 14,531 | 19.1 | 11.41 | -8.8 | 1.0 | -17.3 | -9.4 | -6.6 | -11.1 |
| Top floor $2.0 | 72,651 | 12,685 | 17.5 | 11.86 | -9.1 | 1.1 | -17.7 | -9.6 | -7.1 | -11.0 |
| Top floor $2.5 | 67,981 | 10,692 | 15.7 | 12.52 | -9.3 | 1.2 | -18.1 | -9.9 | -7.8 | -10.7 |
| Top floor $3.0 | 62,929 | 8,916 | 14.2 | 13.31 | -9.6 | 1.2 | -18.6 | -10.2 | -8.5 | -10.7 |
| Top floor $4.0 | 52,317 | 6,020 | 11.5 | 15.32 | -10.2 | 1.5 | -19.5 | -10.9 | -8.8 | -11.6 |
| Top floor $5.0 | 43,922 | 4,228 | 9.6 | 17.40 | -10.9 | 1.7 | -20.5 | -11.8 | -9.0 | -12.7 |

Rule P, below vs above the $3 floor by year:

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| 2019 $1.5-3 | 162 | 67 | 41.4 | 2.32 | -5.9 | 9.1 | -10.9 | -9.6 | -2.8 | -9.0 |
| 2019 $3-+ | 2,495 | 274 | 11.0 | 22.32 | -3.6 | 7.4 | -13.4 | -8.8 | -10.4 | +3.0 |
| 2020 $1.5-3 | 602 | 268 | 44.5 | 2.32 | +1.2 | 4.7 | -4.7 | +0.3 | -3.6 | +6.0 |
| 2020 $3-+ | 6,235 | 694 | 11.1 | 18.98 | -10.5 | 5.3 | -20.8 | -16.2 | -10.0 | -11.1 |
| 2021 $1.5-3 | 1,300 | 581 | 44.7 | 2.32 | +0.6 | 3.2 | -6.0 | +0.2 | -7.1 | +8.3 |
| 2021 $3-+ | 7,836 | 1,085 | 13.8 | 15.15 | -4.9 | 3.7 | -15.0 | -7.6 | -2.6 | -7.2 |
| 2022 $1.5-3 | 1,773 | 775 | 43.7 | 2.31 | -2.1 | 2.7 | -8.2 | -2.5 | -3.5 | -0.8 |
| 2022 $3-+ | 8,906 | 1,270 | 14.3 | 11.52 | -12.1 | 3.0 | -20.0 | -14.5 | -9.5 | -14.7 |
| 2023 $1.5-3 | 2,245 | 983 | 43.8 | 2.27 | -3.3 | 2.4 | -9.8 | -3.6 | -1.4 | -5.2 |
| 2023 $3-+ | 9,407 | 1,446 | 15.4 | 11.51 | -5.3 | 3.3 | -15.8 | -8.0 | -6.8 | -3.7 |
| 2024 $1.5-3 | 2,356 | 994 | 42.2 | 2.28 | -7.0 | 2.3 | -13.6 | -7.3 | -5.7 | -8.4 |
| 2024 $3-+ | 9,835 | 1,402 | 14.3 | 11.91 | -13.7 | 2.8 | -21.9 | -15.3 | -10.9 | -16.5 |
| 2025 $1.5-3 | 2,596 | 1,091 | 42.0 | 2.26 | -8.8 | 2.2 | -14.6 | -9.0 | -6.2 | -11.2 |
| 2025 $3-+ | 10,160 | 1,546 | 15.2 | 11.70 | -8.5 | 2.8 | -17.1 | -10.3 | -11.4 | -5.6 |
| 2026 $1.5-3 | 2,052 | 856 | 41.7 | 2.27 | -9.3 | 2.4 | -13.4 | -9.6 | -6.7 | -11.9 |
| 2026 $3-+ | 8,055 | 1,199 | 14.9 | 12.20 | -13.9 | 2.9 | -21.3 | -15.6 | -17.9 | -9.9 |

### 5b. Dutch the top 4 to an equal fixed return, bet only when total outlay < threshold x return

Stake on each runner = 1 / Top price, so a winner among the four returns 1 unit; outlay = sum of the four implied probabilities. Threshold 0.8 is the requested rule (edge of at least 20% before any miss). ROI is profit / total outlay; "strike" is the share of bet races where the winner was in the four.

| variant | threshold | races_bet | strike_pct | avg_outlay | roi_on_outlay_pct | roi_se | half1 | half2 |
|---|---|---|---|---|---|---|---|---|
| model top 4 (base + class_par), 2023-2026 | 0.8 | 38667 | 59.3 | 0.637 | -6.9 | 0.4 | -6.9 | -6.9 |
| model top 4 (base + class_par), 2023-2026 | 0.9 | 52062 | 64.3 | 0.691 | -7.0 | 0.3 | -6.7 | -7.2 |
| model top 4 (base + class_par), 2023-2026 | 1.0 | 61864 | 67.7 | 0.732 | -7.4 | 0.3 | -7.1 | -7.7 |
| market top 4 (shortest Top prices), 2023-2026 | 0.8 | 27622 | 65.6 | 0.689 | -4.8 | 0.4 | -4.3 | -5.2 |
| market top 4 (shortest Top prices), 2023-2026 | 1.0 | 59421 | 74.9 | 0.797 | -6.1 | 0.2 | -5.6 | -6.5 |
| TR rank top 4 (real toprate_rating), Apr-Oct 2026 | 0.8 | 2386 | 66.3 | 0.708 | -6.3 | 1.3 | -6.6 | -6.0 |
| TR rank top 4 (real toprate_rating), Apr-Oct 2026 | 0.9 | 4096 | 71.9 | 0.767 | -6.3 | 0.9 | -5.9 | -6.7 |
| TR rank top 4 (real toprate_rating), Apr-Oct 2026 | 1.0 | 5626 | 76.1 | 0.816 | -6.7 | 0.7 | -6.3 | -7.0 |
| TR top 4 in races with a locked-rule pick, Apr-Oct 2026 | 0.8 | 271 | 70.1 | 0.714 | -1.8 | 3.8 | +2.0 | -5.5 |
| TR top 4 in races with a locked-rule pick, no outlay cap | 1.0 | 727 | 79.2 | 0.828 | -4.4 | 1.8 | -2.3 | -6.4 |
| model top 4 settled at SP (outlay cap on SP), 2023-2026 | 0.8 | 28818 | 54.7 | 0.649 | -15.6 | 0.4 | -16.5 | -14.8 |
| model top 4 settled at SP, no cap | 1.0 | 54931 | 65.0 | 0.767 | -15.3 | 0.3 | -15.6 | -14.9 |
| TR top 4 settled at SP, Apr-Oct 2026 | 0.8 | 1283 | 62.0 | 0.725 | -14.5 | 1.9 | -14.9 | -14.1 |
| TR top 4 settled at SP, no cap | 1.0 | 4565 | 72.9 | 0.854 | -14.6 | 0.7 | -14.4 | -14.8 |


---

## Notes on the numbers

* **Test 1.** Winner WPR minus par is not flat down the ladder: -4 to -7 for Group, Listed and most BM/CLS rungs, but -12.2 for Open (no black type) and -11.0 / -11.3 at the BM 94+ and below-62 ends. If the ladder is meant to be in WPR points, Open (no black type) at 100 is the clear outlier (generic Open races are mostly open handicaps).
  The "known bug" (class_move off `trackGrading`, which is the going number) had already been fixed in the retired `wpr_projection.py` with a rung ladder; the trackGrading row is that old behaviour for comparison. CLS2 to CLS6, RSTnn and R0MW/R1MW are not on the supplied ladder and were mapped by assumption (see `class_par.py`).
* **Test 2.** At 1.47 points per length XR is compressed against WPR (TOF averages +5.8 for beaten runners), so raw "TOF < 0" is a narrow cut. The 2.15 points per length and race-relative versions are in table 2c. Rear-third settlers almost always have a positive TOF, which is why the specified flag is so rare.
  On the real rule only 16 picks carry the specified flag (99 with the race-relative version, +26.2% at Top, s.e. 23.8): too few to read either way. TOF rank 1 as a stand-alone pick picks $50 longshots and loses 28%.
* **Test 3.** In rule P the widest-gap quartile (least compressed) has the worst ROI (-16.0%) because it holds the longest prices; compression is mostly a proxy for price. Gate rows on the real rule swing between -15.7% and +10.6% with s.e. 8 to 12 points, which is noise-sized.
* **Test 4.** Position 1 at the 800m call wins 21.1% of the time, 2nd 14.1%, down to 2.7% for 13th or worse; the cumulative share passes 75% at the 6th position over all fields. Projected map position (average 800m position of the last 3 starts) correlates 0.43 with the actual call.
  `results/race_shape_projected.csv.gz` (not committed, regenerate with `t4_golden8.py`) holds the projected shape values for inspection.
* **Test 5.** The Dutch outlay test uses the Top price both to choose races (outlay < 0.8) and to settle them, so it is biased in the bettor's favour; the SP rows are the fair check.

## What would make these tests sharper

* The locked rule's real inputs for 2016 to 2025 (the racing-model repo) would turn the 885-bet sample into one with thousands of bets.
* A pre-race fixed price history (opening or mid prices exist for only about 21% of 2026 runs here) would replace the Top / SP bracket.
* Per-runner last-400m times, if the racing-model repo holds them, would replace the length-to-seconds conversion.
