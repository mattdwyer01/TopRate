# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 450; bets still open 34.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 161 | 329 | 35 | $4012 | $3432 | $-580 | -14.5% | -10.4% |
| Volume v2 | 121 | 208 | 23 | $3025 | $2823 | $-202 | -6.7% | -1.4% |
| Volume v3 (P cut) | 104 | 156 | 20 | $2587 | $2378 | $-210 | -8.1% | -5.1% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 39 (profit at the logged fixed price $-19, ROI -2.9%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 16 | $-70 | 7 | $-150 | 10 | $-102 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 329 | $-580 | -14.5% | 208 | $-202 | -6.7% | 156 | $-210 | -8.1% |
| Meeting minimum prize $30k+ | 186 | $-136 | -6.0% | 115 | $235 | 14.2% | 100 | $-203 | -12.7% |
| Meeting minimum prize $40k+ | 136 | $347 | 20.4% | 90 | $535 | 42.0% | 70 | $135 | 11.7% |
| Meeting minimum prize $50k+ | 96 | $545 | 46.4% | 63 | $464 | 54.6% | 47 | $247 | 31.9% |
| Good or firm going (1 to 4) | 255 | $-551 | -17.9% | 158 | $-113 | -5.0% | 125 | $-218 | -10.8% |
| $30k+ and good/firm | 139 | $175 | 10.1% | 87 | $452 | 36.9% | 76 | $41 | 3.4% |
| $40k+ and good/firm | 98 | $533 | 41.8% | 67 | $652 | 68.6% | 51 | $279 | 32.8% |
| Field of 8 or more | 281 | $-195 | -5.9% | 186 | $40 | 1.5% | 133 | $-20 | -1.0% |
| Field of 5 to 7 | 48 | $-385 | -57.0% | 22 | $-242 | -74.4% | 23 | $-189 | -42.0% |
| $40k+ and field of 8+ | 123 | $440 | 28.8% | 87 | $560 | 44.8% | 65 | $235 | 22.3% |
| P(first third) 0.7+ | 96 | $-261 | -25.1% | 58 | $-295 | -36.6% | 96 | $-286 | -18.4% |
| P(first third) 0.5 to 0.7 | 111 | $389 | 25.5% | 66 | $566 | 51.4% | 60 | $76 | 7.4% |
| P(first third) under 0.5 | 76 | $-406 | -45.4% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 58 | $-525 | -84.0% | 30 | $-342 | -85.4% | 24 | $-338 | -84.4% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 34 | $-400 | -100.0% | 14 | $-250 | -100.0% | 18 | $-300 | -100.0% |

## Races checked without a bet, by reason

- ok: 226
- first starter, light-history or no-Proj runner: 144
- bush meeting: 78
- field under 5: 2
