# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 469; bets still open 32.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 169 | 347 | 39 | $4212 | $3609 | $-603 | -14.3% | -10.4% |
| Volume v2 | 126 | 217 | 26 | $3150 | $3002 | $-148 | -4.7% | 0.4% |
| Volume v3 (P cut) | 110 | 163 | 22 | $2737 | $2563 | $-175 | -6.4% | -3.6% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 48 (profit at the logged fixed price $35, ROI 4.5%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 34 | $-93 | 16 | $-96 | 17 | $-68 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 347 | $-603 | -14.3% | 217 | $-148 | -4.7% | 163 | $-175 | -6.4% |
| Meeting minimum prize $30k+ | 200 | $-109 | -4.5% | 123 | $314 | 18.0% | 107 | $-168 | -9.6% |
| Meeting minimum prize $40k+ | 150 | $374 | 20.2% | 98 | $614 | 44.7% | 77 | $170 | 13.0% |
| Meeting minimum prize $50k+ | 104 | $543 | 42.6% | 66 | $459 | 51.0% | 52 | $222 | 25.4% |
| Good or firm going (1 to 4) | 263 | $-472 | -14.9% | 163 | $-29 | -1.2% | 129 | $-108 | -5.2% |
| $30k+ and good/firm | 147 | $254 | 14.1% | 92 | $536 | 42.0% | 80 | $151 | 11.9% |
| $40k+ and good/firm | 106 | $612 | 45.4% | 72 | $736 | 73.6% | 55 | $389 | 42.0% |
| Field of 8 or more | 298 | $-193 | -5.5% | 195 | $94 | 3.3% | 139 | $40 | 1.8% |
| Field of 5 to 7 | 49 | $-410 | -58.6% | 22 | $-242 | -74.4% | 24 | $-214 | -45.1% |
| $40k+ and field of 8+ | 136 | $492 | 29.8% | 95 | $639 | 47.4% | 71 | $295 | 25.1% |
| P(first third) 0.7+ | 102 | $-294 | -26.0% | 61 | $-241 | -28.0% | 102 | $-313 | -18.5% |
| P(first third) 0.5 to 0.7 | 117 | $461 | 29.2% | 69 | $611 | 54.2% | 61 | $139 | 13.3% |
| P(first third) under 0.5 | 82 | $-468 | -48.9% | 49 | $-290 | -42.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 108 | $-322 | -23.2% | 76 | $27 | 2.4% | 48 | $68 | 7.6% |
| 3+ earlier races, under 25% won from first third | 65 | $-502 | -71.8% | 33 | $-347 | -77.0% | 28 | $-338 | -71.1% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 39 | $-427 | -95.0% | 17 | $-255 | -85.0% | 20 | $-350 | -100.0% |

## Races checked without a bet, by reason

- ok: 236
- first starter, light-history or no-Proj runner: 147
- bush meeting: 84
- field under 5: 2
