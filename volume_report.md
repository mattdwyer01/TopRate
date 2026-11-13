# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 331; bets still open 20.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 125 | 259 | 27 | $3112 | $2747 | $-365 | -11.7% | -10.2% |
| Volume v2 | 99 | 173 | 18 | $2475 | $2359 | $-115 | -4.7% | -2.6% |
| Volume v3 (P cut) | 76 | 114 | 14 | $1887 | $1688 | $-200 | -10.6% | -14.1% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 4 (profit at the logged fixed price $68, ROI 67.5%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 10 | $125 | 4 | $68 | 2 | $25 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 259 | $-365 | -11.7% | 173 | $-115 | -4.7% | 114 | $-200 | -10.6% |
| Meeting minimum prize $30k+ | 135 | $156 | 9.5% | 93 | $377 | 29.0% | 68 | $110 | 10.0% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 207 | $-243 | -9.8% | 135 | $70 | 3.6% | 97 | $-85 | -5.4% |
| $30k+ and good/firm | 105 | $450 | 34.0% | 73 | $652 | 63.6% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 219 | $50 | 1.9% | 151 | $126 | 5.9% | 95 | $12 | 0.8% |
| Field of 5 to 7 | 40 | $-415 | -79.1% | 22 | $-242 | -74.4% | 19 | $-212 | -56.5% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 71 | $-122 | -15.3% | 47 | $-224 | -33.4% | 71 | $-98 | -8.3% |
| P(first third) 0.5 to 0.7 | 85 | $349 | 30.3% | 51 | $507 | 60.1% | 43 | $-101 | -14.3% |
| P(first third) under 0.5 | 57 | $-290 | -47.4% | 37 | $-171 | -35.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 92 | $-414 | -35.6% | 66 | $-141 | -14.4% | 39 | $-162 | -22.8% |
| 3+ earlier races, under 25% won from first third | 42 | $-367 | -86.3% | 23 | $-242 | -80.6% | 14 | $-225 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 24 | $-225 | -100.0% | 10 | $-150 | -100.0% | 12 | $-175 | -100.0% |

## Races checked without a bet, by reason

- ok: 175
- first starter, light-history or no-Proj runner: 109
- bush meeting: 45
- field under 5: 2
