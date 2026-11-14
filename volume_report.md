# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 511; bets still open 25.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 195 | 411 | 50 | $4862 | $4500 | $-362 | -7.4% | -4.1% |
| Volume v2 | 142 | 245 | 31 | $3550 | $3303 | $-247 | -7.0% | -2.5% |
| Volume v3 (P cut) | 130 | 192 | 28 | $3237 | $3314 | $77 | 2.4% | 4.7% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 76 (profit at the logged fixed price $-64, ROI -5.4%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 98 | $148 | 44 | $-195 | 46 | $184 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 411 | $-362 | -7.4% | 245 | $-247 | -7.0% | 192 | $77 | 2.4% |
| Meeting minimum prize $30k+ | 249 | $84 | 2.9% | 143 | $217 | 10.7% | 127 | $-155 | -7.4% |
| Meeting minimum prize $40k+ | 199 | $567 | 24.7% | 118 | $517 | 31.3% | 97 | $182 | 11.0% |
| Meeting minimum prize $50k+ | 139 | $530 | 33.2% | 82 | $437 | 39.7% | 68 | $97 | 8.4% |
| Good or firm going (1 to 4) | 285 | $-375 | -11.2% | 168 | $-129 | -5.3% | 138 | $-45 | -2.0% |
| $30k+ and good/firm | 169 | $351 | 17.8% | 97 | $436 | 31.7% | 89 | $214 | 15.0% |
| $40k+ and good/firm | 128 | $709 | 46.5% | 77 | $636 | 57.8% | 64 | $451 | 42.0% |
| Field of 8 or more | 355 | $-33 | -0.8% | 223 | $-5 | -0.2% | 165 | $260 | 9.6% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 178 | $603 | 29.8% | 115 | $542 | 33.3% | 88 | $276 | 18.7% |
| P(first third) 0.7+ | 121 | $-180 | -13.4% | 71 | $-278 | -27.2% | 121 | $-172 | -8.5% |
| P(first third) 0.5 to 0.7 | 148 | $712 | 37.7% | 85 | $561 | 41.4% | 71 | $249 | 20.5% |
| P(first third) under 0.5 | 96 | $-592 | -54.8% | 51 | $-303 | -43.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 135 | $-101 | -6.0% | 86 | $0 | 0.0% | 61 | $444 | 39.9% |
| 3+ earlier races, under 25% won from first third | 79 | $-527 | -63.9% | 39 | $-384 | -69.8% | 33 | $-438 | -76.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 51 | $-452 | -78.7% | 23 | $-292 | -73.1% | 24 | $-450 | -100.0% |

## Races checked without a bet, by reason

- ok: 268
- first starter, light-history or no-Proj runner: 149
- bush meeting: 92
- field under 5: 2
