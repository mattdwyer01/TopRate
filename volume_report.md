# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 449; bets still open 32.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 160 | 328 | 35 | $3987 | $3432 | $-555 | -13.9% | -9.8% |
| Volume v2 | 120 | 207 | 23 | $3000 | $2823 | $-177 | -5.9% | -0.6% |
| Volume v3 (P cut) | 103 | 155 | 20 | $2562 | $2378 | $-185 | -7.2% | -4.2% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 38 (profit at the logged fixed price $6, ROI 0.9%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 15 | $-45 | 6 | $-125 | 9 | $-78 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 328 | $-555 | -13.9% | 207 | $-177 | -5.9% | 155 | $-185 | -7.2% |
| Meeting minimum prize $30k+ | 185 | $-111 | -4.9% | 114 | $260 | 16.0% | 99 | $-178 | -11.3% |
| Meeting minimum prize $40k+ | 135 | $372 | 22.2% | 89 | $560 | 44.8% | 69 | $160 | 14.2% |
| Meeting minimum prize $50k+ | 95 | $570 | 49.6% | 62 | $489 | 59.3% | 46 | $272 | 36.3% |
| Good or firm going (1 to 4) | 254 | $-526 | -17.2% | 157 | $-88 | -3.9% | 124 | $-193 | -9.7% |
| $30k+ and good/firm | 138 | $200 | 11.7% | 86 | $477 | 39.7% | 75 | $66 | 5.6% |
| $40k+ and good/firm | 97 | $558 | 44.6% | 66 | $677 | 73.2% | 50 | $304 | 36.8% |
| Field of 8 or more | 280 | $-170 | -5.1% | 185 | $65 | 2.4% | 132 | $5 | 0.2% |
| Field of 5 to 7 | 48 | $-385 | -57.0% | 22 | $-242 | -74.4% | 23 | $-189 | -42.0% |
| $40k+ and field of 8+ | 122 | $465 | 31.0% | 86 | $585 | 47.8% | 64 | $260 | 25.3% |
| P(first third) 0.7+ | 96 | $-261 | -25.1% | 58 | $-295 | -36.6% | 96 | $-286 | -18.4% |
| P(first third) 0.5 to 0.7 | 110 | $414 | 27.6% | 65 | $591 | 54.9% | 59 | $101 | 10.1% |
| P(first third) under 0.5 | 76 | $-406 | -45.4% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 58 | $-525 | -84.0% | 30 | $-342 | -85.4% | 24 | $-338 | -84.4% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 34 | $-400 | -100.0% | 14 | $-250 | -100.0% | 18 | $-300 | -100.0% |

## Races checked without a bet, by reason

- ok: 225
- first starter, light-history or no-Proj runner: 144
- bush meeting: 78
- field under 5: 2
