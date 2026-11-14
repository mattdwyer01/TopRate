# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 442; bets still open 26.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 158 | 325 | 34 | $3937 | $3334 | $-603 | -15.3% | -11.1% |
| Volume v2 | 119 | 206 | 23 | $2975 | $2823 | $-152 | -5.1% | 0.2% |
| Volume v3 (P cut) | 101 | 152 | 19 | $2512 | $2280 | $-232 | -9.2% | -6.2% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 37 (profit at the logged fixed price $31, ROI 5.1%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 12 | $-92 | 5 | $-100 | 6 | $-125 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 325 | $-603 | -15.3% | 206 | $-152 | -5.1% | 152 | $-232 | -9.2% |
| Meeting minimum prize $30k+ | 183 | $-86 | -3.9% | 113 | $285 | 17.8% | 97 | $-153 | -9.9% |
| Meeting minimum prize $40k+ | 133 | $397 | 24.1% | 88 | $585 | 47.8% | 67 | $185 | 16.8% |
| Meeting minimum prize $50k+ | 93 | $595 | 52.9% | 61 | $514 | 64.3% | 44 | $297 | 41.0% |
| Good or firm going (1 to 4) | 254 | $-526 | -17.2% | 157 | $-88 | -3.9% | 124 | $-193 | -9.7% |
| $30k+ and good/firm | 138 | $200 | 11.7% | 86 | $477 | 39.7% | 75 | $66 | 5.6% |
| $40k+ and good/firm | 97 | $558 | 44.6% | 66 | $677 | 73.2% | 50 | $304 | 36.8% |
| Field of 8 or more | 278 | $-145 | -4.4% | 184 | $90 | 3.4% | 130 | $30 | 1.4% |
| Field of 5 to 7 | 47 | $-457 | -70.4% | 22 | $-242 | -74.4% | 22 | $-262 | -61.6% |
| $40k+ and field of 8+ | 120 | $490 | 33.2% | 85 | $610 | 50.8% | 62 | $285 | 28.5% |
| P(first third) 0.7+ | 95 | $-249 | -24.2% | 58 | $-295 | -36.6% | 95 | $-273 | -17.7% |
| P(first third) 0.5 to 0.7 | 108 | $354 | 24.2% | 64 | $616 | 58.6% | 57 | $41 | 4.3% |
| P(first third) under 0.5 | 76 | $-406 | -45.4% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 58 | $-525 | -84.0% | 30 | $-342 | -85.4% | 24 | $-338 | -84.4% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 34 | $-400 | -100.0% | 14 | $-250 | -100.0% | 18 | $-300 | -100.0% |

## Races checked without a bet, by reason

- ok: 221
- first starter, light-history or no-Proj runner: 143
- bush meeting: 76
- field under 5: 2
