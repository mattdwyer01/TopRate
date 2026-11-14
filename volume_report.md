# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 453; bets still open 35.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 162 | 331 | 36 | $4037 | $3487 | $-550 | -13.6% | -9.6% |
| Volume v2 | 122 | 209 | 24 | $3050 | $2933 | $-117 | -3.8% | 1.4% |
| Volume v3 (P cut) | 105 | 157 | 21 | $2612 | $2488 | $-125 | -4.8% | -1.8% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 40 (profit at the logged fixed price $66, ROI 9.8%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 18 | $-40 | 8 | $-65 | 11 | $-18 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 331 | $-550 | -13.6% | 209 | $-117 | -3.8% | 157 | $-125 | -4.8% |
| Meeting minimum prize $30k+ | 188 | $-106 | -4.6% | 116 | $320 | 19.1% | 101 | $-118 | -7.3% |
| Meeting minimum prize $40k+ | 138 | $377 | 21.9% | 91 | $620 | 47.7% | 71 | $220 | 18.7% |
| Meeting minimum prize $50k+ | 96 | $545 | 46.4% | 63 | $464 | 54.6% | 47 | $247 | 31.9% |
| Good or firm going (1 to 4) | 257 | $-521 | -16.7% | 159 | $-28 | -1.2% | 126 | $-133 | -6.5% |
| $30k+ and good/firm | 141 | $205 | 11.7% | 88 | $537 | 42.9% | 77 | $126 | 10.3% |
| $40k+ and good/firm | 100 | $563 | 43.3% | 68 | $737 | 75.6% | 52 | $364 | 41.6% |
| Field of 8 or more | 283 | $-165 | -4.9% | 187 | $125 | 4.6% | 134 | $65 | 3.0% |
| Field of 5 to 7 | 48 | $-385 | -57.0% | 22 | $-242 | -74.4% | 23 | $-189 | -42.0% |
| $40k+ and field of 8+ | 125 | $470 | 30.3% | 88 | $645 | 50.6% | 66 | $320 | 29.7% |
| P(first third) 0.7+ | 97 | $-219 | -20.8% | 59 | $-210 | -25.3% | 97 | $-201 | -12.7% |
| P(first third) 0.5 to 0.7 | 111 | $389 | 25.5% | 66 | $566 | 51.4% | 60 | $76 | 7.4% |
| P(first third) under 0.5 | 77 | $-418 | -46.1% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 58 | $-525 | -84.0% | 30 | $-342 | -85.4% | 24 | $-338 | -84.4% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 34 | $-400 | -100.0% | 14 | $-250 | -100.0% | 18 | $-300 | -100.0% |

## Races checked without a bet, by reason

- ok: 227
- first starter, light-history or no-Proj runner: 145
- bush meeting: 79
- field under 5: 2
