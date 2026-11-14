# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 496; bets still open 43.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 180 | 373 | 44 | $4487 | $4024 | $-463 | -10.3% | -6.6% |
| Volume v2 | 132 | 229 | 28 | $3300 | $3157 | $-143 | -4.3% | 0.5% |
| Volume v3 (P cut) | 118 | 173 | 25 | $2937 | $2987 | $49 | 1.7% | 4.3% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 60 (profit at the logged fixed price $40, ROI 4.3%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 60 | $47 | 28 | $-91 | 27 | $156 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 373 | $-463 | -10.3% | 229 | $-143 | -4.3% | 173 | $49 | 1.7% |
| Meeting minimum prize $30k+ | 219 | $-86 | -3.3% | 133 | $277 | 15.0% | 114 | $-212 | -11.3% |
| Meeting minimum prize $40k+ | 169 | $397 | 19.6% | 108 | $577 | 39.1% | 84 | $126 | 8.8% |
| Meeting minimum prize $50k+ | 118 | $615 | 44.0% | 74 | $447 | 45.8% | 58 | $203 | 20.9% |
| Good or firm going (1 to 4) | 266 | $-497 | -15.6% | 165 | $-54 | -2.3% | 130 | $-133 | -6.3% |
| $30k+ and good/firm | 150 | $229 | 12.6% | 94 | $511 | 39.3% | 81 | $126 | 9.7% |
| $40k+ and good/firm | 109 | $587 | 42.7% | 74 | $711 | 69.4% | 56 | $364 | 38.3% |
| Field of 8 or more | 317 | $-134 | -3.6% | 207 | $99 | 3.3% | 146 | $232 | 9.6% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 148 | $433 | 24.8% | 105 | $602 | 41.5% | 75 | $220 | 17.6% |
| P(first third) 0.7+ | 109 | $-80 | -6.6% | 64 | $-192 | -21.2% | 109 | $-27 | -1.5% |
| P(first third) 0.5 to 0.7 | 129 | $442 | 25.8% | 76 | $579 | 47.5% | 64 | $76 | 6.9% |
| P(first third) under 0.5 | 89 | $-522 | -51.7% | 51 | $-303 | -43.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 118 | $-229 | -15.1% | 80 | $44 | 3.7% | 52 | $310 | 31.4% |
| 3+ earlier races, under 25% won from first third | 73 | $-536 | -69.1% | 37 | $-334 | -66.8% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 47 | $-461 | -87.8% | 21 | $-242 | -69.3% | 22 | $-400 | -100.0% |

## Races checked without a bet, by reason

- ok: 256
- first starter, light-history or no-Proj runner: 148
- bush meeting: 90
- field under 5: 2
