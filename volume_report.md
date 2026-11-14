# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 504; bets still open 39.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 185 | 386 | 47 | $4612 | $4352 | $-260 | -5.6% | -2.1% |
| Volume v2 | 136 | 236 | 30 | $3400 | $3272 | $-128 | -3.8% | 0.9% |
| Volume v3 (P cut) | 122 | 179 | 27 | $3037 | $3268 | $230 | 7.6% | 10.1% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 67 (profit at the logged fixed price $55, ROI 5.4%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 73 | $250 | 35 | $-76 | 33 | $338 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 386 | $-260 | -5.6% | 236 | $-128 | -3.8% | 179 | $230 | 7.6% |
| Meeting minimum prize $30k+ | 232 | $116 | 4.3% | 140 | $292 | 15.0% | 120 | $-30 | -1.5% |
| Meeting minimum prize $40k+ | 182 | $599 | 27.9% | 115 | $592 | 37.6% | 90 | $307 | 20.1% |
| Meeting minimum prize $50k+ | 129 | $630 | 42.0% | 80 | $487 | 46.3% | 62 | $197 | 18.8% |
| Good or firm going (1 to 4) | 273 | $-334 | -10.3% | 166 | $-79 | -3.3% | 133 | $30 | 1.4% |
| $30k+ and good/firm | 157 | $392 | 20.9% | 95 | $486 | 36.7% | 84 | $289 | 21.4% |
| $40k+ and good/firm | 116 | $750 | 52.6% | 75 | $686 | 65.3% | 59 | $526 | 52.6% |
| Field of 8 or more | 330 | $68 | 1.8% | 214 | $114 | 3.7% | 152 | $413 | 16.5% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 161 | $636 | 33.9% | 112 | $617 | 39.8% | 81 | $401 | 29.7% |
| P(first third) 0.7+ | 112 | $-110 | -8.9% | 66 | $-230 | -24.4% | 112 | $-77 | -4.1% |
| P(first third) 0.5 to 0.7 | 138 | $680 | 37.7% | 81 | $632 | 49.2% | 67 | $308 | 26.6% |
| P(first third) under 0.5 | 90 | $-527 | -51.9% | 51 | $-303 | -43.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 120 | $-42 | -2.7% | 81 | $19 | 1.6% | 54 | $498 | 49.1% |
| 3+ earlier races, under 25% won from first third | 73 | $-536 | -69.1% | 37 | $-334 | -66.8% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 47 | $-461 | -87.8% | 21 | $-242 | -69.3% | 22 | $-400 | -100.0% |

## Races checked without a bet, by reason

- ok: 262
- first starter, light-history or no-Proj runner: 149
- bush meeting: 91
- field under 5: 2
