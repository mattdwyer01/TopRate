# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 373; bets still open 17.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 148 | 306 | 31 | $3687 | $3085 | $-602 | -16.3% | -15.0% |
| Volume v2 | 113 | 198 | 22 | $2825 | $2698 | $-127 | -4.5% | -2.7% |
| Volume v3 (P cut) | 93 | 142 | 17 | $2312 | $2093 | $-220 | -9.5% | -12.4% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 29 (profit at the logged fixed price $56, ROI 12.4%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 57 | $-111 | 29 | $56 | 30 | $5 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 306 | $-602 | -16.3% | 198 | $-127 | -4.5% | 142 | $-220 | -9.5% |
| Meeting minimum prize $30k+ | 164 | $-85 | -4.3% | 105 | $310 | 21.4% | 87 | $-140 | -10.4% |
| Meeting minimum prize $40k+ | 120 | $390 | 26.9% | 82 | $585 | 53.2% | 60 | $210 | 22.1% |
| Meeting minimum prize $50k+ | 81 | $688 | 72.4% | 56 | $614 | 87.7% | 38 | $422 | 70.4% |
| Good or firm going (1 to 4) | 244 | $-550 | -18.6% | 153 | $-38 | -1.7% | 119 | $-180 | -9.4% |
| $30k+ and good/firm | 128 | $175 | 11.0% | 82 | $527 | 45.8% | 70 | $79 | 7.2% |
| $40k+ and good/firm | 93 | $525 | 43.8% | 64 | $702 | 78.0% | 48 | $329 | 41.1% |
| Field of 8 or more | 262 | $-112 | -3.6% | 176 | $115 | 4.6% | 121 | $17 | 0.9% |
| Field of 5 to 7 | 44 | $-490 | -81.7% | 22 | $-242 | -74.4% | 21 | $-237 | -59.2% |
| $40k+ and field of 8+ | 110 | $515 | 38.8% | 79 | $610 | 56.7% | 56 | $285 | 32.5% |
| P(first third) 0.7+ | 90 | $-240 | -24.6% | 57 | $-270 | -34.6% | 90 | $-248 | -17.1% |
| P(first third) 0.5 to 0.7 | 100 | $342 | 25.3% | 58 | $604 | 64.3% | 52 | $29 | 3.4% |
| P(first third) under 0.5 | 70 | $-401 | -49.7% | 45 | $-234 | -37.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 104 | $-372 | -28.3% | 75 | $-73 | -6.7% | 46 | $-7 | -0.9% |
| 3+ earlier races, under 25% won from first third | 51 | $-492 | -89.4% | 27 | $-292 | -83.3% | 20 | $-325 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 31 | $-350 | -100.0% | 12 | $-200 | -100.0% | 16 | $-250 | -100.0% |

## Races checked without a bet, by reason

- ok: 202
- first starter, light-history or no-Proj runner: 122
- bush meeting: 47
- field under 5: 2
