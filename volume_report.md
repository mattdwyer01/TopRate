# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 342; bets still open 18.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 130 | 272 | 29 | $3237 | $2897 | $-340 | -10.5% | -9.0% |
| Volume v2 | 103 | 181 | 20 | $2575 | $2509 | $-65 | -2.5% | -0.6% |
| Volume v3 (P cut) | 80 | 123 | 16 | $1987 | $1988 | $0 | 0.0% | -3.4% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 12 (profit at the logged fixed price $118, ROI 58.8%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

## The same bets at the Betfair starting price, after commission (10% NSW, 8% elsewhere)

Only bets whose Betfair price has arrived (Betfair publishes a day or more after the race).

| Rule | Bets with a Betfair price | Staked | Returned | Profit | ROI at Betfair | ROI at logged price, same bets |
|---|---|---|---|---|---|---|
| Volume v1 | 235 | $2837 | $2927 | $90 | 3.2% | -13.1% |
| Volume v2 | 161 | $2250 | $2638 | $388 | 17.2% | -2.6% |
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
| 2026-11-13 | 23 | $150 | 12 | $118 | 11 | $225 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 272 | $-340 | -10.5% | 181 | $-65 | -2.5% | 123 | $0 | 0.0% |
| Meeting minimum prize $30k+ | 143 | $106 | 6.3% | 96 | $352 | 26.5% | 75 | $60 | 5.2% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 218 | $-280 | -10.8% | 141 | $57 | 2.9% | 105 | $-35 | -2.1% |
| $30k+ and good/firm | 113 | $400 | 29.1% | 76 | $627 | 59.7% | 62 | $229 | 24.1% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 232 | $75 | 2.8% | 159 | $176 | 7.8% | 104 | $212 | 13.2% |
| Field of 5 to 7 | 40 | $-415 | -79.1% | 22 | $-242 | -74.4% | 19 | $-212 | -56.5% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 79 | $-115 | -13.5% | 51 | $-199 | -28.1% | 79 | $-48 | -3.8% |
| P(first third) 0.5 to 0.7 | 86 | $424 | 36.4% | 52 | $582 | 68.0% | 44 | $49 | 6.7% |
| P(first third) under 0.5 | 61 | $-347 | -51.8% | 40 | $-221 | -41.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 94 | $-352 | -29.6% | 68 | $-78 | -7.8% | 40 | $-12 | -1.7% |
| 3+ earlier races, under 25% won from first third | 42 | $-367 | -86.3% | 23 | $-242 | -80.6% | 14 | $-225 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 24 | $-225 | -100.0% | 10 | $-150 | -100.0% | 12 | $-175 | -100.0% |

## Races checked without a bet, by reason

- ok: 181
- first starter, light-history or no-Proj runner: 112
- bush meeting: 47
- field under 5: 2
