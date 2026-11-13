# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 353; bets still open 16.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 134 | 281 | 29 | $3337 | $2897 | $-440 | -13.2% | -11.7% |
| Volume v2 | 105 | 184 | 20 | $2625 | $2509 | $-115 | -4.4% | -2.4% |
| Volume v3 (P cut) | 83 | 127 | 16 | $2062 | $1988 | $-75 | -3.6% | -6.9% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 15 (profit at the logged fixed price $68, ROI 27.0%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 32 | $50 | 15 | $68 | 15 | $150 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 281 | $-440 | -13.2% | 184 | $-115 | -4.4% | 127 | $-75 | -3.6% |
| Meeting minimum prize $30k+ | 146 | $81 | 4.7% | 96 | $352 | 26.5% | 76 | $35 | 2.9% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 225 | $-355 | -13.3% | 142 | $32 | 1.6% | 108 | $-85 | -5.0% |
| $30k+ and good/firm | 116 | $375 | 26.8% | 76 | $627 | 59.7% | 63 | $204 | 20.9% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 241 | $-25 | -0.9% | 162 | $126 | 5.5% | 108 | $137 | 8.1% |
| Field of 5 to 7 | 40 | $-415 | -79.1% | 22 | $-242 | -74.4% | 19 | $-212 | -56.5% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 82 | $-145 | -16.4% | 52 | $-211 | -29.3% | 82 | $-111 | -8.4% |
| P(first third) 0.5 to 0.7 | 88 | $408 | 34.5% | 52 | $582 | 68.0% | 45 | $36 | 4.9% |
| P(first third) under 0.5 | 65 | $-401 | -55.4% | 42 | $-259 | -45.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 99 | $-402 | -32.5% | 70 | $-103 | -10.1% | 43 | $-62 | -7.9% |
| 3+ earlier races, under 25% won from first third | 42 | $-367 | -86.3% | 23 | $-242 | -80.6% | 14 | $-225 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 25 | $-250 | -100.0% | 11 | $-175 | -100.0% | 12 | $-175 | -100.0% |

## Races checked without a bet, by reason

- ok: 185
- first starter, light-history or no-Proj runner: 119
- bush meeting: 47
- field under 5: 2
