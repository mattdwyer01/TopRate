# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 365; bets still open 20.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 140 | 290 | 30 | $3487 | $3002 | $-485 | -13.9% | -12.5% |
| Volume v2 | 108 | 189 | 21 | $2700 | $2614 | $-85 | -3.2% | -1.3% |
| Volume v3 (P cut) | 86 | 131 | 17 | $2137 | $2093 | $-45 | -2.1% | -5.2% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 20 (profit at the logged fixed price $98, ROI 30.0%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 41 | $5 | 20 | $98 | 19 | $180 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 290 | $-485 | -13.9% | 189 | $-85 | -3.2% | 131 | $-45 | -2.1% |
| Meeting minimum prize $30k+ | 149 | $6 | 0.4% | 97 | $327 | 24.2% | 76 | $35 | 2.9% |
| Meeting minimum prize $40k+ | 111 | $406 | 30.1% | 78 | $552 | 52.5% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 78 | $738 | 82.0% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 234 | $-400 | -14.2% | 147 | $62 | 3.0% | 112 | $-55 | -3.1% |
| $30k+ and good/firm | 119 | $300 | 20.4% | 77 | $602 | 56.0% | 63 | $204 | 20.9% |
| $40k+ and good/firm | 90 | $575 | 50.0% | 63 | $727 | 83.1% | 45 | $379 | 50.5% |
| Field of 8 or more | 248 | $-20 | -0.7% | 167 | $156 | 6.6% | 112 | $167 | 9.5% |
| Field of 5 to 7 | 42 | $-465 | -80.9% | 22 | $-242 | -74.4% | 19 | $-212 | -56.5% |
| $40k+ and field of 8+ | 103 | $506 | 40.5% | 75 | $577 | 56.3% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 85 | $-174 | -19.1% | 54 | $-228 | -30.9% | 85 | $-161 | -11.8% |
| P(first third) 0.5 to 0.7 | 92 | $429 | 33.9% | 54 | $654 | 73.5% | 46 | $116 | 15.1% |
| P(first third) under 0.5 | 67 | $-438 | -57.6% | 43 | $-284 | -47.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 103 | $-347 | -26.9% | 74 | $-48 | -4.5% | 46 | $-7 | -0.9% |
| 3+ earlier races, under 25% won from first third | 45 | $-417 | -87.7% | 23 | $-242 | -80.6% | 15 | $-250 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 28 | $-300 | -100.0% | 11 | $-175 | -100.0% | 13 | $-200 | -100.0% |

## Races checked without a bet, by reason

- ok: 194
- first starter, light-history or no-Proj runner: 122
- bush meeting: 47
- field under 5: 2
