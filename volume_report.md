# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 456; bets still open 32.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 163 | 335 | 37 | $4062 | $3509 | $-553 | -13.6% | -9.6% |
| Volume v2 | 123 | 211 | 25 | $3075 | $2978 | $-97 | -3.2% | 2.0% |
| Volume v3 (P cut) | 106 | 158 | 21 | $2637 | $2488 | $-150 | -5.7% | -2.8% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 42 (profit at the logged fixed price $86, ROI 12.3%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 22 | $-42 | 10 | $-45 | 12 | $-42 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 335 | $-553 | -13.6% | 211 | $-97 | -3.2% | 158 | $-150 | -5.7% |
| Meeting minimum prize $30k+ | 192 | $-109 | -4.7% | 118 | $340 | 20.0% | 102 | $-143 | -8.7% |
| Meeting minimum prize $40k+ | 142 | $375 | 21.4% | 93 | $640 | 48.3% | 72 | $195 | 16.2% |
| Meeting minimum prize $50k+ | 100 | $543 | 45.2% | 65 | $484 | 55.3% | 48 | $222 | 27.8% |
| Good or firm going (1 to 4) | 257 | $-521 | -16.7% | 159 | $-28 | -1.2% | 126 | $-133 | -6.5% |
| $30k+ and good/firm | 141 | $205 | 11.7% | 88 | $537 | 42.9% | 77 | $126 | 10.3% |
| $40k+ and good/firm | 100 | $563 | 43.3% | 68 | $737 | 75.6% | 52 | $364 | 41.6% |
| Field of 8 or more | 287 | $-168 | -5.0% | 189 | $145 | 5.3% | 135 | $40 | 1.8% |
| Field of 5 to 7 | 48 | $-385 | -57.0% | 22 | $-242 | -74.4% | 23 | $-189 | -42.0% |
| $40k+ and field of 8+ | 129 | $467 | 29.7% | 90 | $665 | 51.2% | 67 | $295 | 26.8% |
| P(first third) 0.7+ | 98 | $-225 | -21.2% | 59 | $-210 | -25.3% | 98 | $-226 | -14.1% |
| P(first third) 0.5 to 0.7 | 113 | $399 | 25.9% | 67 | $599 | 53.7% | 60 | $76 | 7.4% |
| P(first third) under 0.5 | 78 | $-425 | -46.5% | 47 | $-259 | -39.4% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 62 | $-527 | -81.2% | 32 | $-322 | -75.7% | 25 | $-362 | -85.3% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 38 | $-402 | -94.7% | 16 | $-230 | -83.6% | 19 | $-325 | -100.0% |

## Races checked without a bet, by reason

- ok: 228
- first starter, light-history or no-Proj runner: 145
- bush meeting: 81
- field under 5: 2
