# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-14; races checked 380; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 151 | 313 | 33 | $3762 | $3252 | $-510 | -13.6% | -12.3% |
| Volume v2 | 115 | 201 | 23 | $2875 | $2823 | $-52 | -1.8% | -0.0% |
| Volume v3 (P cut) | 96 | 146 | 19 | $2387 | $2280 | $-107 | -4.5% | -7.3% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 32 (profit at the logged fixed price $131, ROI 26.2%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 64 | $-20 | 32 | $131 | 34 | $118 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 313 | $-510 | -13.6% | 201 | $-52 | -1.8% | 146 | $-107 | -4.5% |
| Meeting minimum prize $30k+ | 171 | $6 | 0.3% | 108 | $385 | 25.7% | 91 | $-28 | -2.0% |
| Meeting minimum prize $40k+ | 121 | $490 | 33.2% | 83 | $685 | 60.9% | 61 | $310 | 31.8% |
| Meeting minimum prize $50k+ | 81 | $688 | 72.4% | 56 | $614 | 87.7% | 38 | $422 | 70.4% |
| Good or firm going (1 to 4) | 250 | $-559 | -18.5% | 155 | $-63 | -2.8% | 122 | $-168 | -8.6% |
| $30k+ and good/firm | 134 | $167 | 10.1% | 84 | $502 | 42.7% | 73 | $91 | 7.9% |
| $40k+ and good/firm | 93 | $525 | 43.8% | 64 | $702 | 78.0% | 48 | $329 | 41.1% |
| Field of 8 or more | 269 | $-20 | -0.6% | 179 | $190 | 7.4% | 125 | $130 | 6.5% |
| Field of 5 to 7 | 44 | $-490 | -81.7% | 22 | $-242 | -74.4% | 21 | $-237 | -59.2% |
| $40k+ and field of 8+ | 111 | $615 | 45.5% | 80 | $710 | 64.5% | 57 | $385 | 42.7% |
| P(first third) 0.7+ | 92 | $-215 | -21.7% | 57 | $-270 | -34.6% | 92 | $-211 | -14.2% |
| P(first third) 0.5 to 0.7 | 102 | $433 | 31.3% | 60 | $691 | 70.8% | 54 | $104 | 11.4% |
| P(first third) under 0.5 | 73 | $-426 | -51.2% | 46 | $-246 | -38.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 105 | $-272 | -20.3% | 76 | $27 | 2.4% | 47 | $93 | 10.7% |
| 3+ earlier races, under 25% won from first third | 57 | $-500 | -83.3% | 29 | $-317 | -84.4% | 23 | $-312 | -83.3% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 31 | $-350 | -100.0% | 12 | $-200 | -100.0% | 16 | $-250 | -100.0% |

## Races checked without a bet, by reason

- ok: 203
- first starter, light-history or no-Proj runner: 123
- bush meeting: 52
- field under 5: 2
