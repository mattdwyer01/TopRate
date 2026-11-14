# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 514; bets still open 23.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 198 | 417 | 51 | $4937 | $4600 | $-337 | -6.8% | -3.5% |
| Volume v2 | 144 | 249 | 32 | $3600 | $3403 | $-197 | -5.5% | -1.1% |
| Volume v3 (P cut) | 133 | 195 | 29 | $3312 | $3414 | $102 | 3.1% | 5.4% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 80 (profit at the logged fixed price $-14, ROI -1.1%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 104 | $173 | 48 | $-145 | 49 | $209 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 417 | $-337 | -6.8% | 249 | $-197 | -5.5% | 195 | $102 | 3.1% |
| Meeting minimum prize $30k+ | 254 | $34 | 1.2% | 146 | $192 | 9.4% | 129 | $-205 | -9.6% |
| Meeting minimum prize $40k+ | 204 | $517 | 22.0% | 121 | $492 | 29.4% | 99 | $132 | 7.8% |
| Meeting minimum prize $50k+ | 141 | $505 | 31.1% | 82 | $437 | 39.7% | 69 | $72 | 6.1% |
| Good or firm going (1 to 4) | 290 | $-425 | -12.5% | 171 | $-154 | -6.3% | 140 | $-95 | -4.2% |
| $30k+ and good/firm | 174 | $301 | 14.9% | 100 | $411 | 29.4% | 91 | $164 | 11.1% |
| $40k+ and good/firm | 133 | $659 | 41.9% | 80 | $611 | 54.3% | 66 | $401 | 35.7% |
| Field of 8 or more | 361 | $-8 | -0.2% | 227 | $45 | 1.4% | 168 | $285 | 10.2% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 183 | $553 | 26.7% | 118 | $517 | 31.3% | 90 | $226 | 14.8% |
| P(first third) 0.7+ | 123 | $-113 | -8.2% | 73 | $-211 | -20.0% | 123 | $-122 | -5.9% |
| P(first third) 0.5 to 0.7 | 150 | $687 | 35.9% | 85 | $561 | 41.4% | 72 | $224 | 18.1% |
| P(first third) under 0.5 | 98 | $-609 | -55.5% | 53 | $-319 | -44.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 140 | $-151 | -8.7% | 89 | $-25 | -1.9% | 63 | $394 | 33.9% |
| 3+ earlier races, under 25% won from first third | 79 | $-527 | -63.9% | 39 | $-384 | -69.8% | 33 | $-438 | -76.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 51 | $-452 | -78.7% | 23 | $-292 | -73.1% | 24 | $-450 | -100.0% |

## Races checked without a bet, by reason

- ok: 270
- first starter, light-history or no-Proj runner: 150
- bush meeting: 92
- field under 5: 2
