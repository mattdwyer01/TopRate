# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 356; bets still open 14.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 136 | 285 | 29 | $3387 | $2897 | $-490 | -14.5% | -13.0% |
| Volume v2 | 106 | 187 | 20 | $2650 | $2509 | $-140 | -5.3% | -3.4% |
| Volume v3 (P cut) | 84 | 129 | 16 | $2087 | $1988 | $-100 | -4.8% | -8.0% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 18 (profit at the logged fixed price $43, ROI 15.5%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 36 | $0 | 18 | $43 | 17 | $125 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 285 | $-490 | -14.5% | 187 | $-140 | -5.3% | 129 | $-100 | -4.8% |
| Meeting minimum prize $30k+ | 147 | $56 | 3.2% | 96 | $352 | 26.5% | 76 | $35 | 2.9% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 229 | $-405 | -14.9% | 145 | $7 | 0.3% | 110 | $-110 | -6.4% |
| $30k+ and good/firm | 117 | $350 | 24.6% | 76 | $627 | 59.7% | 63 | $204 | 20.9% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 244 | $-50 | -1.8% | 165 | $101 | 4.4% | 110 | $112 | 6.5% |
| Field of 5 to 7 | 41 | $-440 | -80.0% | 22 | $-242 | -74.4% | 19 | $-212 | -56.5% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 84 | $-161 | -17.9% | 54 | $-228 | -30.9% | 84 | $-136 | -10.1% |
| P(first third) 0.5 to 0.7 | 90 | $374 | 30.8% | 53 | $574 | 66.4% | 45 | $36 | 4.9% |
| P(first third) under 0.5 | 65 | $-401 | -55.4% | 42 | $-259 | -45.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 102 | $-427 | -33.8% | 73 | $-128 | -12.2% | 45 | $-87 | -10.8% |
| 3+ earlier races, under 25% won from first third | 42 | $-367 | -86.3% | 23 | $-242 | -80.6% | 14 | $-225 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 25 | $-250 | -100.0% | 11 | $-175 | -100.0% | 12 | $-175 | -100.0% |

## Races checked without a bet, by reason

- ok: 187
- first starter, light-history or no-Proj runner: 120
- bush meeting: 47
- field under 5: 2
