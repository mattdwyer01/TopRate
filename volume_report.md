# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-13; races checked 372; bets still open 20.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 146 | 300 | 30 | $3637 | $3002 | $-635 | -17.5% | -16.1% |
| Volume v2 | 111 | 192 | 21 | $2775 | $2614 | $-160 | -5.8% | -3.9% |
| Volume v3 (P cut) | 91 | 138 | 17 | $2262 | $2093 | $-170 | -7.5% | -10.5% |

## Volume v2 from 2026-11-13: fields of 8+ only, judged at the Betfair starting price after commission

Bets settled 23 (profit at the logged fixed price $23, ROI 5.6%). With a Betfair price 0: staked $0, returned $0, profit $0, ROI None%.

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
| 2026-11-13 | 51 | $-145 | 23 | $23 | 26 | $55 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 300 | $-635 | -17.5% | 192 | $-160 | -5.8% | 138 | $-170 | -7.5% |
| Meeting minimum prize $30k+ | 158 | $-119 | -6.2% | 99 | $277 | 19.8% | 83 | $-90 | -7.0% |
| Meeting minimum prize $40k+ | 117 | $331 | 23.3% | 79 | $527 | 49.0% | 58 | $235 | 25.4% |
| Meeting minimum prize $50k+ | 81 | $688 | 72.4% | 56 | $614 | 87.7% | 38 | $422 | 70.4% |
| Good or firm going (1 to 4) | 241 | $-525 | -17.9% | 150 | $-13 | -0.6% | 117 | $-155 | -8.2% |
| $30k+ and good/firm | 125 | $200 | 12.7% | 79 | $552 | 49.0% | 68 | $104 | 9.7% |
| $40k+ and good/firm | 93 | $525 | 43.8% | 64 | $702 | 78.0% | 48 | $329 | 41.1% |
| Field of 8 or more | 256 | $-145 | -4.8% | 170 | $81 | 3.3% | 117 | $67 | 3.6% |
| Field of 5 to 7 | 44 | $-490 | -81.7% | 22 | $-242 | -74.4% | 21 | $-237 | -59.2% |
| $40k+ and field of 8+ | 107 | $456 | 35.1% | 76 | $552 | 52.5% | 54 | $310 | 36.4% |
| P(first third) 0.7+ | 88 | $-224 | -23.3% | 55 | $-253 | -33.2% | 88 | $-223 | -15.6% |
| P(first third) 0.5 to 0.7 | 97 | $367 | 27.6% | 55 | $629 | 68.8% | 50 | $54 | 6.5% |
| P(first third) under 0.5 | 69 | $-476 | -59.6% | 44 | $-309 | -49.6% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 104 | $-372 | -28.3% | 75 | $-73 | -6.7% | 46 | $-7 | -0.9% |
| 3+ earlier races, under 25% won from first third | 48 | $-467 | -88.9% | 24 | $-267 | -82.1% | 18 | $-300 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 31 | $-350 | -100.0% | 12 | $-200 | -100.0% | 16 | $-250 | -100.0% |

## Races checked without a bet, by reason

- ok: 201
- first starter, light-history or no-Proj runner: 122
- bush meeting: 47
- field under 5: 2
