# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 522; bets still open 22.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 202 | 423 | 51 | $5037 | $4600 | $-437 | -8.7% | -5.4% |
| Volume v2 | 146 | 251 | 32 | $3650 | $3403 | $-247 | -6.8% | -2.4% |
| Volume v3 (P cut) | 134 | 196 | 29 | $3337 | $3414 | $77 | 2.3% | 4.6% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 82 (profit at the logged fixed price $-64, ROI -5.0%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 110 | $73 | 50 | $-195 | 50 | $184 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 423 | $-437 | -8.7% | 251 | $-247 | -6.8% | 196 | $77 | 2.3% |
| Meeting minimum prize $30k+ | 256 | $-16 | -0.5% | 148 | $142 | 6.8% | 129 | $-205 | -9.6% |
| Meeting minimum prize $40k+ | 206 | $467 | 19.5% | 123 | $442 | 25.6% | 99 | $132 | 7.8% |
| Meeting minimum prize $50k+ | 142 | $480 | 29.1% | 83 | $412 | 36.6% | 69 | $72 | 6.1% |
| Good or firm going (1 to 4) | 291 | $-450 | -13.2% | 172 | $-179 | -7.2% | 140 | $-95 | -4.2% |
| $30k+ and good/firm | 175 | $276 | 13.5% | 101 | $386 | 27.1% | 91 | $164 | 11.1% |
| $40k+ and good/firm | 134 | $634 | 39.6% | 81 | $586 | 51.0% | 66 | $401 | 35.7% |
| Field of 8 or more | 367 | $-108 | -2.5% | 229 | $-5 | -0.2% | 169 | $260 | 9.2% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 185 | $503 | 23.7% | 120 | $467 | 27.5% | 90 | $226 | 14.8% |
| P(first third) 0.7+ | 124 | $-121 | -8.8% | 73 | $-211 | -20.0% | 124 | $-147 | -7.0% |
| P(first third) 0.5 to 0.7 | 153 | $629 | 31.9% | 86 | $536 | 38.9% | 72 | $224 | 18.1% |
| P(first third) under 0.5 | 100 | $-642 | -56.8% | 54 | $-344 | -46.4% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 142 | $-201 | -11.3% | 91 | $-75 | -5.6% | 63 | $394 | 33.9% |
| 3+ earlier races, under 25% won from first third | 79 | $-527 | -63.9% | 39 | $-384 | -69.8% | 33 | $-438 | -76.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 51 | $-452 | -78.7% | 23 | $-292 | -73.1% | 24 | $-450 | -100.0% |

## Races checked without a bet, by reason

- ok: 275
- first starter, light-history or no-Proj runner: 153
- bush meeting: 92
- field under 5: 2
