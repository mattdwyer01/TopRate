# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 486; bets still open 34.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 176 | 366 | 41 | $4387 | $3725 | $-662 | -15.1% | -11.3% |
| Volume v2 | 130 | 226 | 27 | $3250 | $3065 | $-185 | -5.7% | -0.8% |
| Volume v3 (P cut) | 115 | 169 | 22 | $2862 | $2563 | $-300 | -10.5% | -7.8% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 57 (profit at the logged fixed price $-2, ROI -0.3%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 53 | $-151 | 25 | $-133 | 23 | $-192 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 366 | $-662 | -15.1% | 226 | $-185 | -5.7% | 169 | $-300 | -10.5% |
| Meeting minimum prize $30k+ | 215 | $-118 | -4.6% | 131 | $302 | 16.5% | 112 | $-268 | -14.5% |
| Meeting minimum prize $40k+ | 165 | $366 | 18.5% | 106 | $602 | 41.5% | 82 | $70 | 5.0% |
| Meeting minimum prize $50k+ | 116 | $559 | 40.7% | 74 | $447 | 45.8% | 56 | $147 | 15.5% |
| Good or firm going (1 to 4) | 266 | $-497 | -15.6% | 165 | $-54 | -2.3% | 130 | $-133 | -6.3% |
| $30k+ and good/firm | 150 | $229 | 12.6% | 94 | $511 | 39.3% | 81 | $126 | 9.7% |
| $40k+ and good/firm | 109 | $587 | 42.7% | 74 | $711 | 69.4% | 56 | $364 | 38.3% |
| Field of 8 or more | 312 | $-277 | -7.6% | 204 | $56 | 1.9% | 144 | $-60 | -2.6% |
| Field of 5 to 7 | 54 | $-385 | -51.3% | 22 | $-242 | -74.4% | 25 | $-239 | -47.8% |
| $40k+ and field of 8+ | 146 | $458 | 26.6% | 103 | $627 | 44.0% | 75 | $220 | 17.6% |
| P(first third) 0.7+ | 105 | $-317 | -27.5% | 63 | $-260 | -29.5% | 105 | $-376 | -21.4% |
| P(first third) 0.5 to 0.7 | 126 | $480 | 28.6% | 74 | $604 | 50.5% | 64 | $76 | 6.9% |
| P(first third) under 0.5 | 89 | $-522 | -51.7% | 51 | $-303 | -43.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 115 | $-397 | -27.1% | 79 | $-23 | -2.0% | 50 | $18 | 1.9% |
| 3+ earlier races, under 25% won from first third | 71 | $-511 | -68.1% | 35 | $-309 | -65.1% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 45 | $-436 | -87.2% | 19 | $-217 | -66.9% | 22 | $-400 | -100.0% |

## Races checked without a bet, by reason

- ok: 248
- first starter, light-history or no-Proj runner: 147
- bush meeting: 89
- field under 5: 2
