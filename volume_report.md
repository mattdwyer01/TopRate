# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 525; bets still open 20.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 204 | 427 | 51 | $5087 | $4600 | $-487 | -9.6% | -6.3% |
| Volume v2 | 148 | 254 | 32 | $3700 | $3403 | $-297 | -8.0% | -3.7% |
| Volume v3 (P cut) | 136 | 200 | 29 | $3387 | $3414 | $27 | 0.8% | 3.1% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 85 (profit at the logged fixed price $-114, ROI -8.6%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 114 | $23 | 53 | $-245 | 54 | $134 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 427 | $-487 | -9.6% | 254 | $-297 | -8.0% | 200 | $27 | 0.8% |
| Meeting minimum prize $30k+ | 259 | $-41 | -1.4% | 150 | $117 | 5.5% | 132 | $-230 | -10.6% |
| Meeting minimum prize $40k+ | 209 | $442 | 18.2% | 125 | $417 | 23.8% | 102 | $107 | 6.2% |
| Meeting minimum prize $50k+ | 145 | $455 | 27.2% | 85 | $387 | 33.6% | 72 | $47 | 3.9% |
| Good or firm going (1 to 4) | 291 | $-450 | -13.2% | 172 | $-179 | -7.2% | 140 | $-95 | -4.2% |
| $30k+ and good/firm | 175 | $276 | 13.5% | 101 | $386 | 27.1% | 91 | $164 | 11.1% |
| $40k+ and good/firm | 134 | $634 | 39.6% | 81 | $586 | 51.0% | 66 | $401 | 35.7% |
| Field of 8 or more | 371 | $-158 | -3.7% | 232 | $-55 | -1.6% | 173 | $210 | 7.3% |
| Field of 5 to 7 | 56 | $-329 | -42.4% | 22 | $-242 | -74.4% | 27 | $-183 | -34.8% |
| $40k+ and field of 8+ | 188 | $478 | 22.3% | 122 | $442 | 25.6% | 93 | $201 | 13.0% |
| P(first third) 0.7+ | 127 | $-163 | -11.4% | 76 | $-261 | -23.7% | 127 | $-189 | -8.8% |
| P(first third) 0.5 to 0.7 | 154 | $620 | 31.3% | 86 | $536 | 38.9% | 73 | $216 | 17.3% |
| P(first third) under 0.5 | 100 | $-642 | -56.8% | 54 | $-344 | -46.4% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 142 | $-201 | -11.3% | 91 | $-75 | -5.6% | 63 | $394 | 33.9% |
| 3+ earlier races, under 25% won from first third | 79 | $-527 | -63.9% | 39 | $-384 | -69.8% | 33 | $-438 | -76.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 54 | $-477 | -79.6% | 25 | $-317 | -74.7% | 27 | $-475 | -100.0% |

## Races checked without a bet, by reason

- ok: 277
- first starter, light-history or no-Proj runner: 154
- bush meeting: 92
- field under 5: 2
