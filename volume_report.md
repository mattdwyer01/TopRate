# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 467; bets still open 34.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 168 | 343 | 38 | $4187 | $3584 | $-603 | -14.4% | -10.5% |
| Volume v2 | 125 | 213 | 25 | $3125 | $2978 | $-147 | -4.7% | 0.4% |
| Volume v3 (P cut) | 109 | 162 | 22 | $2712 | $2563 | $-150 | -5.5% | -2.7% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 44 (profit at the logged fixed price $36, ROI 4.8%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

## The same bets at the Betfair starting price, after commission (10% NSW, 8% elsewhere)

Only bets whose Betfair price has arrived (Betfair publishes a day or more after the race).

| Rule | Bets with a Betfair price | Staked | Returned | Profit | ROI at Betfair | ROI at logged price, same bets |
|---|---|---|---|---|---|---|
| Volume v1 | 237 | $2862 | $2927 | $65 | 2.3% | -13.9% |
| Volume v2 | 163 | $2275 | $2638 | $363 | 15.9% | -3.6% |
| Volume v3 (P cut) | 104 | $1737 | $1616 | $-122 | -7.0% | -8.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 42 | $-278 | 27 | $-183 | 24 | $-186 |
| 2026-11-09 | 16 | $-106 | 10 | $-150 | 7 | $25 |
| 2026-11-10 | 11 | $-99 | 5 | $-36 | 8 | $-47 |
| 2026-11-12 | 2 | $-25 | 2 | $-25 | 0 | $0 |
| 2026-11-13 | 64 | $-20 | 32 | $131 | 34 | $118 |
| 2026-11-14 | 30 | $-92 | 12 | $-95 | 16 | $-42 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 343 | $-603 | -14.4% | 213 | $-147 | -4.7% | 162 | $-150 | -5.5% |
| Meeting minimum prize $30k+ | 196 | $-109 | -4.5% | 119 | $315 | 18.3% | 106 | $-143 | -8.3% |
| Meeting minimum prize $40k+ | 146 | $375 | 20.5% | 94 | $615 | 45.6% | 76 | $195 | 15.3% |
| Meeting minimum prize $50k+ | 104 | $543 | 42.6% | 66 | $459 | 51.0% | 52 | $222 | 25.4% |
| Good or firm going (1 to 4) | 259 | $-471 | -15.0% | 159 | $-28 | -1.2% | 128 | $-83 | -4.0% |
| $30k+ and good/firm | 143 | $255 | 14.3% | 88 | $537 | 42.9% | 79 | $176 | 14.1% |
| $40k+ and good/firm | 102 | $613 | 46.3% | 68 | $737 | 75.6% | 54 | $414 | 46.0% |
| Field of 8 or more | 294 | $-193 | -5.5% | 191 | $95 | 3.4% | 138 | $65 | 2.9% |
| Field of 5 to 7 | 49 | $-410 | -58.6% | 22 | $-242 | -74.4% | 24 | $-214 | -45.1% |
| $40k+ and field of 8+ | 132 | $492 | 30.3% | 91 | $640 | 48.3% | 70 | $320 | 27.8% |
| P(first third) 0.7+ | 101 | $-287 | -25.6% | 60 | $-235 | -27.5% | 101 | $-288 | -17.3% |
| P(first third) 0.5 to 0.7 | 115 | $449 | 28.7% | 67 | $599 | 53.7% | 61 | $139 | 13.3% |
| P(first third) under 0.5 | 81 | $-462 | -48.6% | 48 | $-284 | -41.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 108 | $-322 | -23.2% | 76 | $27 | 2.4% | 48 | $68 | 7.6% |
| 3+ earlier races, under 25% won from first third | 65 | $-502 | -71.8% | 33 | $-347 | -77.0% | 28 | $-338 | -71.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 39 | $-427 | -95.0% | 17 | $-255 | -85.0% | 20 | $-350 | -100.0% |

## Races checked without a bet, by reason

- ok: 234
- first starter, light-history or no-Proj runner: 147
- bush meeting: 84
- field under 5: 2
