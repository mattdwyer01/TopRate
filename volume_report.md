# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 476; bets still open 29.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 172 | 356 | 40 | $4287 | $3650 | $-637 | -14.9% | -11.0% |
| Volume v2 | 127 | 219 | 27 | $3175 | $3065 | $-110 | -3.5% | 1.5% |
| Volume v3 (P cut) | 113 | 166 | 22 | $2812 | $2563 | $-250 | -8.9% | -6.1% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 50 (profit at the logged fixed price $73, ROI 9.1%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 43 | $-126 | 18 | $-58 | 20 | $-142 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 356 | $-637 | -14.9% | 219 | $-110 | -3.5% | 166 | $-250 | -8.9% |
| Meeting minimum prize $30k+ | 206 | $-118 | -4.8% | 125 | $352 | 19.8% | 109 | $-218 | -12.1% |
| Meeting minimum prize $40k+ | 156 | $366 | 19.2% | 100 | $652 | 46.6% | 79 | $120 | 8.9% |
| Meeting minimum prize $50k+ | 107 | $559 | 43.0% | 68 | $497 | 53.7% | 53 | $197 | 21.9% |
| Good or firm going (1 to 4) | 263 | $-472 | -14.9% | 163 | $-29 | -1.2% | 129 | $-108 | -5.2% |
| $30k+ and good/firm | 147 | $254 | 14.1% | 92 | $536 | 42.0% | 80 | $151 | 11.9% |
| $40k+ and good/firm | 106 | $612 | 45.4% | 72 | $736 | 73.6% | 55 | $389 | 42.0% |
| Field of 8 or more | 304 | $-202 | -5.7% | 197 | $131 | 4.6% | 141 | $-10 | -0.4% |
| Field of 5 to 7 | 52 | $-435 | -60.0% | 22 | $-242 | -74.4% | 25 | $-239 | -47.8% |
| $40k+ and field of 8+ | 139 | $508 | 30.3% | 97 | $677 | 49.2% | 72 | $270 | 22.5% |
| P(first third) 0.7+ | 104 | $-310 | -27.1% | 62 | $-253 | -29.0% | 104 | $-363 | -20.8% |
| P(first third) 0.5 to 0.7 | 119 | $486 | 30.5% | 70 | $661 | 58.0% | 62 | $114 | 10.6% |
| P(first third) under 0.5 | 87 | $-510 | -51.1% | 49 | $-290 | -42.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 111 | $-347 | -24.5% | 76 | $27 | 2.4% | 49 | $43 | 4.7% |
| 3+ earlier races, under 25% won from first third | 71 | $-511 | -68.1% | 35 | $-309 | -65.1% | 30 | $-388 | -73.8% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 45 | $-436 | -87.2% | 19 | $-217 | -66.9% | 22 | $-400 | -100.0% |

## Races checked without a bet, by reason

- ok: 240
- first starter, light-history or no-Proj runner: 147
- bush meeting: 87
- field under 5: 2
