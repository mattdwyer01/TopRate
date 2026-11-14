# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 418; bets still open 16.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 155 | 319 | 34 | $3862 | $3334 | $-528 | -13.7% | -9.4% |
| Volume v2 | 116 | 202 | 23 | $2900 | $2823 | $-77 | -2.7% | 2.8% |
| Volume v3 (P cut) | 98 | 148 | 19 | $2437 | $2280 | $-157 | -6.4% | -3.3% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 33 (profit at the logged fixed price $106, ROI 20.2%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 6 | $-18 | 1 | $-25 | 2 | $-50 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 319 | $-528 | -13.7% | 202 | $-77 | -2.7% | 148 | $-157 | -6.4% |
| Meeting minimum prize $30k+ | 177 | $-11 | -0.5% | 109 | $360 | 23.6% | 93 | $-78 | -5.3% |
| Meeting minimum prize $40k+ | 127 | $472 | 30.0% | 84 | $660 | 57.4% | 63 | $260 | 25.3% |
| Meeting minimum prize $50k+ | 87 | $670 | 63.8% | 57 | $589 | 81.3% | 40 | $372 | 57.2% |
| Good or firm going (1 to 4) | 251 | $-501 | -16.5% | 155 | $-63 | -2.8% | 122 | $-168 | -8.6% |
| $30k+ and good/firm | 135 | $225 | 13.4% | 84 | $502 | 42.7% | 73 | $91 | 7.9% |
| $40k+ and good/firm | 94 | $583 | 47.6% | 64 | $702 | 78.0% | 48 | $329 | 41.1% |
| Field of 8 or more | 272 | $-70 | -2.2% | 180 | $165 | 6.4% | 126 | $105 | 5.2% |
| Field of 5 to 7 | 47 | $-457 | -70.4% | 22 | $-242 | -74.4% | 22 | $-262 | -61.6% |
| $40k+ and field of 8+ | 114 | $565 | 40.3% | 81 | $685 | 60.9% | 58 | $360 | 38.9% |
| P(first third) 0.7+ | 94 | $-240 | -23.6% | 58 | $-295 | -36.6% | 94 | $-261 | -17.0% |
| P(first third) 0.5 to 0.7 | 103 | $421 | 30.1% | 60 | $691 | 70.8% | 54 | $104 | 11.4% |
| P(first third) under 0.5 | 76 | $-406 | -45.4% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 57 | $-500 | -83.3% | 29 | $-317 | -84.4% | 23 | $-312 | -83.3% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 31 | $-350 | -100.0% | 12 | $-200 | -100.0% | 16 | $-250 | -100.0% |

## Races checked without a bet, by reason

- ok: 211
- first starter, light-history or no-Proj runner: 139
- bush meeting: 66
- field under 5: 2
