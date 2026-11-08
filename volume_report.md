# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 253; bets still open 9.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 104 | 218 | 21 | $2600 | $2389 | $-210 | -8.1% | -7.9% |
| Volume v2 | 84 | 151 | 15 | $2100 | $2153 | $53 | 2.5% | 4.3% |
| Volume v3 (P cut) | 62 | 96 | 11 | $1550 | $1373 | $-177 | -11.4% | -18.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 40 | $-228 | 26 | $-158 | 23 | $-161 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 218 | $-210 | -8.1% | 151 | $53 | 2.5% | 96 | $-177 | -11.4% |
| Meeting minimum prize $30k+ | 134 | $181 | 11.2% | 92 | $402 | 31.5% | 68 | $110 | 10.0% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 168 | $30 | 1.5% | 115 | $356 | 22.2% | 80 | $-13 | -1.0% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 188 | $80 | 3.6% | 134 | $245 | 13.4% | 83 | $-65 | -5.1% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 60 | $-114 | -16.7% | 40 | $-142 | -25.8% | 60 | $-134 | -13.7% |
| P(first third) 0.5 to 0.7 | 66 | $409 | 46.9% | 42 | $510 | 75.9% | 36 | $-43 | -7.5% |
| P(first third) under 0.5 | 46 | $-202 | -40.8% | 31 | $-88 | -21.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 72 | $-327 | -36.3% | 58 | $-58 | -7.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 35 | $-292 | -83.3% | 17 | $-167 | -74.1% | 12 | $-175 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 142
- first starter, light-history or no-Proj runner: 78
- bush meeting: 33
