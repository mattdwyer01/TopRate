# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 423; bets still open 15.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 156 | 320 | 34 | $3887 | $3334 | $-553 | -14.2% | -10.0% |
| Volume v2 | 117 | 203 | 23 | $2925 | $2823 | $-102 | -3.5% | 1.9% |
| Volume v3 (P cut) | 99 | 149 | 19 | $2462 | $2280 | $-182 | -7.4% | -4.3% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 34 (profit at the logged fixed price $81, ROI 14.7%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 7 | $-42 | 2 | $-50 | 3 | $-75 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 320 | $-553 | -14.2% | 203 | $-102 | -3.5% | 149 | $-182 | -7.4% |
| Meeting minimum prize $30k+ | 178 | $-36 | -1.7% | 110 | $335 | 21.6% | 94 | $-103 | -6.9% |
| Meeting minimum prize $40k+ | 128 | $447 | 27.9% | 85 | $635 | 54.0% | 64 | $235 | 22.3% |
| Meeting minimum prize $50k+ | 88 | $645 | 60.0% | 58 | $564 | 75.2% | 41 | $347 | 51.4% |
| Good or firm going (1 to 4) | 251 | $-501 | -16.5% | 155 | $-63 | -2.8% | 122 | $-168 | -8.6% |
| $30k+ and good/firm | 135 | $225 | 13.4% | 84 | $502 | 42.7% | 73 | $91 | 7.9% |
| $40k+ and good/firm | 94 | $583 | 47.6% | 64 | $702 | 78.0% | 48 | $329 | 41.1% |
| Field of 8 or more | 273 | $-95 | -2.9% | 181 | $140 | 5.4% | 127 | $80 | 3.9% |
| Field of 5 to 7 | 47 | $-457 | -70.4% | 22 | $-242 | -74.4% | 22 | $-262 | -61.6% |
| $40k+ and field of 8+ | 115 | $540 | 37.9% | 82 | $660 | 57.4% | 59 | $335 | 35.2% |
| P(first third) 0.7+ | 94 | $-240 | -23.6% | 58 | $-295 | -36.6% | 94 | $-261 | -17.0% |
| P(first third) 0.5 to 0.7 | 104 | $396 | 27.8% | 61 | $666 | 66.5% | 55 | $79 | 8.5% |
| P(first third) under 0.5 | 76 | $-406 | -45.4% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 58 | $-525 | -84.0% | 30 | $-342 | -85.4% | 24 | $-338 | -84.4% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 32 | $-375 | -100.0% | 13 | $-225 | -100.0% | 17 | $-275 | -100.0% |

## Races checked without a bet, by reason

- ok: 211
- first starter, light-history or no-Proj runner: 141
- bush meeting: 69
- field under 5: 2
