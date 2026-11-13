# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 369; bets still open 18.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 144 | 298 | 30 | $3587 | $3002 | $-585 | -16.3% | -15.0% |
| Volume v2 | 109 | 190 | 21 | $2725 | $2614 | $-110 | -4.1% | -2.2% |
| Volume v3 (P cut) | 89 | 136 | 17 | $2212 | $2093 | $-120 | -5.4% | -8.4% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 21 (profit at the logged fixed price $73, ROI 20.7%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 49 | $-95 | 21 | $73 | 24 | $105 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 298 | $-585 | -16.3% | 190 | $-110 | -4.1% | 136 | $-120 | -5.4% |
| Meeting minimum prize $30k+ | 156 | $-69 | -3.7% | 97 | $327 | 24.2% | 81 | $-40 | -3.2% |
| Meeting minimum prize $40k+ | 116 | $356 | 25.5% | 78 | $552 | 52.5% | 57 | $260 | 28.8% |
| Meeting minimum prize $50k+ | 80 | $713 | 77.0% | 55 | $639 | 94.7% | 37 | $447 | 77.8% |
| Good or firm going (1 to 4) | 239 | $-475 | -16.5% | 148 | $37 | 1.7% | 115 | $-105 | -5.7% |
| $30k+ and good/firm | 123 | $250 | 16.4% | 77 | $602 | 56.0% | 66 | $154 | 15.0% |
| $40k+ and good/firm | 92 | $550 | 46.9% | 63 | $727 | 83.1% | 47 | $354 | 45.6% |
| Field of 8 or more | 254 | $-95 | -3.2% | 168 | $131 | 5.5% | 115 | $117 | 6.5% |
| Field of 5 to 7 | 44 | $-490 | -81.7% | 22 | $-242 | -74.4% | 21 | $-237 | -59.2% |
| $40k+ and field of 8+ | 106 | $481 | 37.8% | 75 | $577 | 56.3% | 53 | $335 | 40.6% |
| P(first third) 0.7+ | 87 | $-199 | -21.2% | 54 | $-228 | -30.9% | 87 | $-198 | -14.1% |
| P(first third) 0.5 to 0.7 | 96 | $392 | 30.1% | 54 | $654 | 73.5% | 49 | $79 | 9.8% |
| P(first third) under 0.5 | 69 | $-476 | -59.6% | 44 | $-309 | -49.6% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 104 | $-372 | -28.3% | 75 | $-73 | -6.7% | 46 | $-7 | -0.9% |
| 3+ earlier races, under 25% won from first third | 47 | $-442 | -88.3% | 23 | $-242 | -80.6% | 17 | $-275 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 30 | $-325 | -100.0% | 11 | $-175 | -100.0% | 15 | $-225 | -100.0% |

## Races checked without a bet, by reason

- ok: 198
- first starter, light-history or no-Proj runner: 122
- bush meeting: 47
- field under 5: 2
