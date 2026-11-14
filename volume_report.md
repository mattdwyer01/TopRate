# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 462; bets still open 37.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 165 | 338 | 37 | $4112 | $3509 | $-603 | -14.7% | -10.7% |
| Volume v2 | 125 | 213 | 25 | $3125 | $2978 | $-147 | -4.7% | 0.4% |
| Volume v3 (P cut) | 107 | 159 | 21 | $2662 | $2488 | $-175 | -6.6% | -3.7% |

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
| 2026-11-14 | 25 | $-92 | 12 | $-95 | 13 | $-68 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 338 | $-603 | -14.7% | 213 | $-147 | -4.7% | 159 | $-175 | -6.6% |
| Meeting minimum prize $30k+ | 193 | $-134 | -5.7% | 119 | $315 | 18.3% | 103 | $-168 | -10.0% |
| Meeting minimum prize $40k+ | 143 | $350 | 19.7% | 94 | $615 | 45.6% | 73 | $170 | 13.8% |
| Meeting minimum prize $50k+ | 101 | $518 | 42.3% | 66 | $459 | 51.0% | 49 | $197 | 23.9% |
| Good or firm going (1 to 4) | 257 | $-521 | -16.7% | 159 | $-28 | -1.2% | 126 | $-133 | -6.5% |
| $30k+ and good/firm | 141 | $205 | 11.7% | 88 | $537 | 42.9% | 77 | $126 | 10.3% |
| $40k+ and good/firm | 100 | $563 | 43.3% | 68 | $737 | 75.6% | 52 | $364 | 41.6% |
| Field of 8 or more | 290 | $-218 | -6.3% | 191 | $95 | 3.4% | 136 | $15 | 0.7% |
| Field of 5 to 7 | 48 | $-385 | -57.0% | 22 | $-242 | -74.4% | 23 | $-189 | -42.0% |
| $40k+ and field of 8+ | 130 | $442 | 27.6% | 91 | $640 | 48.3% | 68 | $270 | 24.0% |
| P(first third) 0.7+ | 99 | $-250 | -23.1% | 60 | $-235 | -27.5% | 99 | $-251 | -15.4% |
| P(first third) 0.5 to 0.7 | 113 | $399 | 25.9% | 67 | $599 | 53.7% | 60 | $76 | 7.4% |
| P(first third) under 0.5 | 80 | $-450 | -47.9% | 48 | $-284 | -41.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 63 | $-552 | -81.9% | 33 | $-347 | -77.0% | 26 | $-388 | -86.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 39 | $-427 | -95.0% | 17 | $-255 | -85.0% | 20 | $-350 | -100.0% |

## Races checked without a bet, by reason

- ok: 232
- first starter, light-history or no-Proj runner: 146
- bush meeting: 82
- field under 5: 2
