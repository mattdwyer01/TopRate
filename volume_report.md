# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 428; bets still open 17.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 157 | 322 | 34 | $3912 | $3334 | $-578 | -14.8% | -10.6% |
| Volume v2 | 118 | 204 | 23 | $2950 | $2823 | $-127 | -4.3% | 1.1% |
| Volume v3 (P cut) | 100 | 150 | 19 | $2487 | $2280 | $-207 | -8.3% | -5.2% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 35 (profit at the logged fixed price $56, ROI 9.7%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-14 | 9 | $-68 | 3 | $-75 | 4 | $-100 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 322 | $-578 | -14.8% | 204 | $-127 | -4.3% | 150 | $-207 | -8.3% |
| Meeting minimum prize $30k+ | 180 | $-61 | -2.8% | 111 | $310 | 19.7% | 95 | $-128 | -8.4% |
| Meeting minimum prize $40k+ | 130 | $422 | 26.0% | 86 | $610 | 50.8% | 65 | $210 | 19.5% |
| Meeting minimum prize $50k+ | 90 | $620 | 56.4% | 59 | $539 | 69.6% | 42 | $322 | 46.0% |
| Good or firm going (1 to 4) | 251 | $-501 | -16.5% | 155 | $-63 | -2.8% | 122 | $-168 | -8.6% |
| $30k+ and good/firm | 135 | $225 | 13.4% | 84 | $502 | 42.7% | 73 | $91 | 7.9% |
| $40k+ and good/firm | 94 | $583 | 47.6% | 64 | $702 | 78.0% | 48 | $329 | 41.1% |
| Field of 8 or more | 275 | $-120 | -3.7% | 182 | $115 | 4.4% | 128 | $55 | 2.6% |
| Field of 5 to 7 | 47 | $-457 | -70.4% | 22 | $-242 | -74.4% | 22 | $-262 | -61.6% |
| $40k+ and field of 8+ | 117 | $515 | 35.5% | 83 | $635 | 54.0% | 60 | $310 | 31.8% |
| P(first third) 0.7+ | 94 | $-240 | -23.6% | 58 | $-295 | -36.6% | 94 | $-261 | -17.0% |
| P(first third) 0.5 to 0.7 | 106 | $371 | 25.6% | 62 | $641 | 62.4% | 56 | $54 | 5.6% |
| P(first third) under 0.5 | 76 | $-406 | -45.4% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 58 | $-525 | -84.0% | 30 | $-342 | -85.4% | 24 | $-338 | -84.4% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 34 | $-400 | -100.0% | 14 | $-250 | -100.0% | 18 | $-300 | -100.0% |

## Races checked without a bet, by reason

- ok: 215
- first starter, light-history or no-Proj runner: 141
- bush meeting: 70
- field under 5: 2
