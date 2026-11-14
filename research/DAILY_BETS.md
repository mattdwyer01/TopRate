# Daily bets

The owner's manual betting rules, the script that lists a day's bets, and the running results. Nothing here places a bet.

## Build the day's list

From the repo root, on the latest `main`:

```
python research/daily_bets.py 2026-11-14            # whole day
python research/daily_bets.py 2026-11-14 --from 17:45   # only races from 5:45pm Melbourne time
```

It needs node 22+ (it computes the dashboard Rating with `frontend/src/lib/raceModel.ts` itself, so the figures match the race page). It reads
`toprate_data.json`, `wpr_projection_log.csv.gz` (newer projections win over the payload), `trip_map.json` plus `data/trip_map_archive/`, and
`runners.csv` through `volume_rules.py`. Output is one line per bet in time order, with the watch list; quaddies that do not qualify are listed on
stderr with the reason. About 10 seconds.

Before the first bet of the day, and again around 5:45pm for the night meetings, run `projection_daily.yml` in fast mode (about 12 minutes; GitHub
keeps only one waiting run, so a newer queued run can replace yours) and rebuild the list after it finishes.

## Rules ($50 = 1 unit)

- **Win, $50 at the fixed price**: the top runner by the dashboard Rating leads the second by 2 points or more, price over $2, no first starter or
  1 to 2 run horse in the race, not a bush meeting (the meeting's biggest race $20k or less).
- **Volume v2, $25 a race split equally, settled at Betfair SP**: as coded in `volume_rules.py` (first third on the trip map, fixed price $3 or more,
  within 2 of the top when the top-rated runner qualifies, within 4 when no qualifier is within 1 of the top, otherwise no bet; fields of 8+; the same
  first-starter, light-horse and bush skips). **Same-horse rule (13 Nov 2026)**: when the Volume horse is also the win bet, bet the win only; other
  Volume horses in that race share the $25.
- **Watch list**: runners priced $2.50 to $3.40 and what changes if they cross $3. Check once, 15 to 30 minutes before the jump, and ignore later moves
  (price log 13 to 21 Oct: about 12% of runners near $3 end on the other side at the jump whether checked 60 or 15 minutes out).
- **Quaddie, $25 flexi**: each leg's pool is every runner within 2 Rating points of the top plus those within 6 forecast in the first half of the trip
  map; over 600 combinations, every leg uses within 4 instead. Only at meetings whose biggest race is $40k or more, no first starter in any leg (the
  script checks the projection log, `nruns == 0`, because the payload's first-starter label can be blank), legs averaging 8 or more runners. Early
  quaddie ends on race max(4, N-4), late quaddie on the last race.
- **Heavy tracks (14 Nov 2026)**: all stakes halved at meetings rated Heavy 8 or worse when the list is made (win $25, Volume $12.50 a race, quaddie
  $12.50 flexi). The going comes from the TAB poller; when a track is upgraded the next list goes back to full stakes, bets already placed stay as placed.
- **No quinellas or exactas** (every structure lost on 18 Oct to 12 Nov).
- **Betfair commission**: 10% on NSW racing, 8% elsewhere.
- **Bonus bets**: use them on a runner around $5 to $10 (a bonus bet returns only the winnings).

## Results

18 Oct to 12 Nov is a backtest on corrected ratings (TAB dividends, Volume at Betfair SP where the files exist, else the fixed price);
13 Nov on is real bets.

| Date | Win | Volume v2 | Quaddie | Day | Staked | Running total |
|---|---|---|---|---|---|---|
| Sat 18 Oct | -200.00 | +6.97 | -50.00 | -243.03 | 575 | -243.03 |
| Sun 19 Oct | +57.50 | -43.16 | 0.00 | +14.34 | 225 | -228.69 |
| Tue 21 Oct | +45.00 | +293.08 | +79.36 | +417.44 | 725 | +188.75 |
| Wed 22 Oct | 0.00 | -100.00 | 0.00 | -100.00 | 100 | +88.75 |
| Thu 23 Oct | -150.00 | -169.71 | -57.93 | -377.65 | 600 | -288.90 |
| Sat 24 Oct | +345.00 | +409.49 | +576.05 | +1,330.53 | 2,350 | +1,041.63 |
| Sun 25 Oct | -200.00 | +78.97 | -83.64 | -204.67 | 675 | +836.96 |
| Mon 26 Oct | -50.00 | -7.50 | 0.00 | -57.50 | 150 | +779.46 |
| Tue 27 Oct | +160.00 | +136.45 | 0.00 | +296.45 | 275 | +1,075.91 |
| Wed 28 Oct | +95.00 | +230.83 | -41.85 | +283.98 | 575 | +1,359.89 |
| Thu 29 Oct | -100.00 | -36.33 | -25.00 | -161.33 | 200 | +1,198.56 |
| Fri 30 Oct | +105.00 | +305.25 | -25.00 | +385.25 | 675 | +1,583.81 |
| Sat 31 Oct | +150.00 | +858.69 | -178.87 | +829.81 | 1,775 | +2,413.63 |
| Sun 1 Nov | 0.00 | -100.10 | -33.94 | -134.04 | 350 | +2,279.58 |
| Mon 2 Nov | +137.50 | -25.00 | 0.00 | +112.50 | 175 | +2,392.08 |
| Tue 3 Nov | -155.00 | -264.81 | +285.23 | -134.57 | 1,500 | +2,257.51 |
| Wed 4 Nov | +227.50 | +818.83 | 0.00 | +1,046.33 | 500 | +3,303.84 |
| Thu 5 Nov | +65.00 | -114.00 | +67.56 | +18.56 | 450 | +3,322.40 |
| Fri 6 Nov | +62.50 | -300.00 | +86.51 | -150.99 | 400 | +3,171.41 |
| Sat 7 Nov | -60.00 | +118.07 | -170.73 | -112.67 | 1,275 | +3,058.74 |
| Sun 8 Nov | +40.00 | -46.52 | +13.31 | +6.79 | 425 | +3,065.53 |
| Mon 9 Nov | +70.00 | -100.00 | 0.00 | -30.00 | 150 | +3,035.53 |
| Tue 10 Nov | 0.00 | -75.00 | +13.23 | -61.77 | 100 | +2,973.76 |
| Wed 11 Nov | +140.00 | -250.00 | +729.74 | +619.74 | 575 | +3,593.50 |
| Thu 12 Nov | -70.00 | +8.33 | -50.00 | -111.67 | 500 | +3,481.83 |
| Fri 13 Nov (real) | +47.50 | +339.73 | +94.59 | +481.82 | 875 | +3,963.65 |
| **Sat 14 Nov (real)** | -316.25 | -131.94 | -101.50 | -549.69 | 1,412 | **+3,413.96** |

| Bet type | Bets | Hits | Staked | P&L | ROI |
|---|---|---|---|---|---|
| Win | 105 | 40 | $5,225 | +$446.25 | +8.5% |
| Volume v2 | 665 | 110 | $10,025 | +$1,840.62 | +18.4% |
| Quaddie | 94 | 35 | $2,338 | +$1,127.10 | +48.2% |
| **Total** | 864 | 185 | **$17,587** | **+$3,413.96** | **+19.4%** |

14 Nov counts the 52 bets ticked as placed on the bet page (Volume winners provisional at the TAB win dividend less commission until the Betfair
SP file is in; Caribbean Villa, Dunkeld R4, was a watch-list bet taken at fixed $3). Not counted: Sha Tin R10 and R11 Volume, Toowoomba R4 Volume and
the Toowoomba R7 win bet (not placed), the Darwin bets (skipped by choice), Mathematician (firmed to $1.80) and a 4-leg multi tracked with no stake
(lost the last leg). All 61 rule bets as listed came to -$658.
Volume v2 on the blended Rating instead of the plain Proj (`research/v2_blend_backtest.py`, run from a checkout of main, 14 Nov 2026; 14 Oct to 13 Nov,
1,630 resulted races, 1,846 of 1,966 with a direct score for every runner; last fixed price and Betfair SP after commission, BSP missing for about half
of 11 to 13 Nov so those fall back to the fixed price): plain Proj 712 bets, 127 wins, +20.5% fixed, +36.5% Betfair (+1.1% without the 10 best);
blended 623 bets, 117 wins, +5.2% fixed, +15.7% Betfair (-11.2% without the 10 best). From 5 Nov both lose (-17.6% vs -21.9% at Betfair). 427 bets
differ: the 258 only the plain Proj takes returned +61% flat at the fixed price, the 169 only the blend takes +6%. Volume stays on the plain Proj.
13 Nov also had a Geelong early quaddie placed outside the rules (first starters in three legs; -$10.64, not counted). Mon 20 Oct had no bets.
Open: Volume for 10 to 12 Nov is still at the fixed price until the Betfair files for those days are in. The quaddie rule and its 600 cut were
chosen on these same weeks, so the backtest rows flatter it; judge the rules on the real days.
