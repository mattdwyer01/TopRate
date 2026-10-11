# betsignal: market-residual win model (EXPERIMENTAL)

Produces, for every runner in a fully drawn and priced race, a win probability, a model price (1 / probability) and an edge
(probability x price - 1), and flags two bet tiers. Shown in the dashboard's Bets tab and as the Model $ / Edge columns on the Race table.
It is a separate model from the WPR projection (`projection/`), which is unchanged and still drives Proj, Base, Adj, SM and the gap lines.

## How it works
1. Start from the market: each runner's fixed price becomes an implied probability, normalised across the race (`pm`).
2. LightGBM (binary win/not-win, `init_score = logit(pm)`, so it learns only a correction to the market) on 36 features: recent WPRs
   (last 3, best, career average, relative to the field), days since last run, win rate, last-start market probability and result against it,
   weight, barrier, distance and weight change, going, class, track, age, sex, jockey and trainer win rate and excess over the market
   (measured on results up to the previous day). Heavily regularised, 3 seeds averaged, early stopped on the latest year.
3. Renormalise within the race: `pmod`. Edge `ev = pmod x price`.
4. Tiers (`score.py: tier()`): **Select** = non-favourite with ev > 1.20 at $3 to $20, or favourite with ev > 1.30 at $3+. **Volume** = ev > 1.05 at $3+.
   Stakes (frontend `lib/betSignals.ts`): Select 2u, Volume 0.25u, 1u = $50.

## Files
- `features.py`  two paths that must agree: `batch_features` (training) and `build_state` + `serve_features` (live, from per-horse /
  jockey / trainer state). `check_equivalence.py` proves they match (all 36 features exact; first starters have no age or sex in the live
  files, so training blanks them too).
- `train.py`  trains and saves `models/bet_seed{1,2,3}.txt` + `meta.json` (committed). `models/state.pkl` is NOT committed (13 MB, rebuilt from the results files by `score.py`, cached by the workflow).
- `score.py`  scores unstarted races, writes `bet_signals.json` (latest pass `now` and frozen pass `fz` per run, 10 days) and the append-only
  `bet_signal_log.csv.gz`. A race is scored only when every runner has a horse id, jockey, trainer, barrier, weight and a fixed price, and no runner
  has a recent run the results files do not hold yet (those lag a few days).
- `backfill.py`  writes `bet_signals_history.json` (compact, read once by the dashboard under the live file): past days scored out of sample, flagged `sp` (a model trained only on days before the window, against the closing starting price) or `last` (the production model against the last recorded fixed price, for the days after the results files end). Neither is a price taken before the jump, so the Bets scoreboard keeps them apart from live bets. Re-run it by hand (about 8 minutes) to extend the window.
- `backtest.py`  walk-forward backtest with the production code. `forward_check.py`  the live check from the log.
- Workflows: `.github/workflows/bet_signal.yml` (score; trigger from cron-job.org every 5 minutes in racing hours, like `price_refresh.yml`),
  `bet_signal_train.yml` (weekly retrain + manual).

## The rating (frontend)
The Race page's Rating is these win probabilities on the ATW scale (`frontend/src/lib/betSignals.ts`, `RATING_PER_LN = 3.66`, level from the field's mean WPR projection);
see the CLAUDE.md entry for the calibration. A race without full signals uses the WPR projection.

## Evidence and caveats (read before trusting it)
- Backtest 2022 to 2026, walk-forward with the production code (`backtest.py`), at CLOSING SP (6,660 Volume-or-Select bets, 599 Select):
  Select 120 bets a year (0.7 a Saturday), win 25.7%, avg $7.11, ROI +53.1%, years +41 +82 +42 +65 +32, quarters +42 +76 +45 +49, +30.4% without the
  10 biggest winners, +37.7% with a price 10% worse than SP. Volume including Select: 10.1 bets a Saturday, ROI +1.7%, -2.2% without the 10 biggest winners.
  Volume bets alone (not Select): -3.4% ROI, -13.1% with a price 10% worse. So Volume is the action tier and costs profit; stake it small.
  Staking (Volume/Select units): 0.25/2 gives +117u a year at SP (+51u with a 10% worse price), 0/2 gives +127u (+90u). 1 unit = $50.
- The tier thresholds were chosen after looking at these same years, so true figures will be lower.
- The model's overall log-loss is slightly WORSE than the market's; the edge sits in the rare runners where it disagrees strongly. It is not a better
  price for the whole field. 83% of raw EV > 1.15 bets are market favourites that lose about 0%: the profit is in non-favourites and in very confident favourites.
- SP is not a price you can get before the jump. The pre-race read (fixed prices 5 to 30 minutes out, 112 races) was inconclusive. The Bets scoreboard
  judges each bet at the price when the last pass was made at least 5 minutes before the jump: that is the real test. It needs months.
- More features, more seeds and bigger trees did not help (tested): the edge is limited by the information in these inputs.
- Research notes that preceded this: within-2 WPR win betting was -15.9% ROI at every cut; no filter (price, favourite, speed map, overlay) fixed it.
