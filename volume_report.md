# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 507; bets still open 32.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 190 | 398 | 48 | $4737 | $4382 | $-355 | -7.5% | -4.0% |
| Volume v2 | 139 | 242 | 31 | $3475 | $3303 | $-172 | -4.9% | -0.4% |
| Volume v3 (P cut) | 126 | 187 | 28 | $3137 | $3314 | $177 | 5.6% | 8.1% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 73 (profit at the logged fixed price $11, ROI 1.0%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 85 | $156 | 41 | $-120 | 41 | $284 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 398 | $-355 | -7.5% | 242 | $-172 | -4.9% | 187 | $177 | 5.6% |
| Meeting minimum prize $30k+ | 237 | $66 | 2.4% | 141 | $267 | 13.5% | 123 | $-80 | -4.0% |
| Meeting minimum prize $40k+ | 187 | $549 | 25.0% | 116 | $567 | 35.4% | 93 | $257 | 16.3% |
| Meeting minimum prize $50k+ | 134 | $580 | 37.5% | 81 | $462 | 42.9% | 65 | $147 | 13.4% |
| Good or firm going (1 to 4) | 278 | $-384 | -11.7% | 167 | $-104 | -4.3% | 136 | $-20 | -0.9% |
| $30k+ and good/firm | 162 | $342 | 17.7% | 96 | $461 | 34.2% | 87 | $239 | 17.1% |
| $40k+ and good/firm | 121 | $700 | 47.5% | 76 | $661 | 61.5% | 62 | $476 | 45.4% |
| Field of 8 or more | 342 | $-26 | -0.7% | 220 | $70 | 2.2% | 160 | $360 | 13.8% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 166 | $586 | 30.4% | 113 | $592 | 37.6% | 84 | $351 | 25.1% |
| P(first third) 0.7+ | 117 | $-125 | -9.7% | 69 | $-228 | -23.5% | 117 | $-97 | -5.0% |
| P(first third) 0.5 to 0.7 | 143 | $638 | 34.6% | 84 | $586 | 44.1% | 70 | $274 | 23.0% |
| P(first third) under 0.5 | 92 | $-565 | -53.6% | 51 | $-303 | -43.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 129 | $-111 | -6.8% | 86 | $0 | 0.0% | 60 | $469 | 43.1% |
| 3+ earlier races, under 25% won from first third | 73 | $-536 | -69.1% | 37 | $-334 | -66.8% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 47 | $-461 | -87.8% | 21 | $-242 | -69.3% | 22 | $-400 | -100.0% |

## Races checked without a bet, by reason

- ok: 264
- first starter, light-history or no-Proj runner: 149
- bush meeting: 92
- field under 5: 2
