# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 510; bets still open 30.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 193 | 405 | 49 | $4812 | $4442 | $-370 | -7.7% | -4.3% |
| Volume v2 | 140 | 243 | 31 | $3500 | $3303 | $-197 | -5.6% | -1.1% |
| Volume v3 (P cut) | 128 | 189 | 28 | $3187 | $3314 | $127 | 4.0% | 6.4% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 74 (profit at the logged fixed price $-14, ROI -1.2%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 92 | $140 | 42 | $-145 | 43 | $234 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 405 | $-370 | -7.7% | 243 | $-197 | -5.6% | 189 | $127 | 4.0% |
| Meeting minimum prize $30k+ | 243 | $76 | 2.7% | 141 | $267 | 13.5% | 124 | $-105 | -5.1% |
| Meeting minimum prize $40k+ | 193 | $559 | 24.8% | 116 | $567 | 35.4% | 94 | $232 | 14.5% |
| Meeting minimum prize $50k+ | 136 | $555 | 35.3% | 81 | $462 | 42.9% | 66 | $122 | 10.9% |
| Good or firm going (1 to 4) | 282 | $-350 | -10.6% | 167 | $-104 | -4.3% | 136 | $-20 | -0.9% |
| $30k+ and good/firm | 166 | $376 | 19.3% | 96 | $461 | 34.2% | 87 | $239 | 17.1% |
| $40k+ and good/firm | 125 | $734 | 49.0% | 76 | $661 | 61.5% | 62 | $476 | 45.4% |
| Field of 8 or more | 349 | $-42 | -1.0% | 221 | $45 | 1.4% | 162 | $310 | 11.6% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 172 | $595 | 30.1% | 113 | $592 | 37.6% | 85 | $326 | 22.9% |
| P(first third) 0.7+ | 119 | $-163 | -12.3% | 70 | $-253 | -25.4% | 119 | $-147 | -7.4% |
| P(first third) 0.5 to 0.7 | 145 | $679 | 36.4% | 84 | $586 | 44.1% | 70 | $274 | 23.0% |
| P(first third) under 0.5 | 95 | $-584 | -54.4% | 51 | $-303 | -43.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 135 | $-101 | -6.0% | 86 | $0 | 0.0% | 61 | $444 | 39.9% |
| 3+ earlier races, under 25% won from first third | 73 | $-536 | -69.1% | 37 | $-334 | -66.8% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 48 | $-486 | -88.3% | 22 | $-267 | -71.3% | 23 | $-425 | -100.0% |

## Races checked without a bet, by reason

- ok: 267
- first starter, light-history or no-Proj runner: 149
- bush meeting: 92
- field under 5: 2
