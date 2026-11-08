# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 249; bets still open 6.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 102 | 214 | 21 | $2550 | $2389 | $-160 | -6.3% | -6.1% |
| Volume v2 | 82 | 147 | 15 | $2050 | $2153 | $103 | 5.0% | 6.8% |
| Volume v3 (P cut) | 61 | 94 | 11 | $1525 | $1373 | $-152 | -10.0% | -16.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 36 | $-178 | 22 | $-108 | 21 | $-136 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 214 | $-160 | -6.3% | 147 | $103 | 5.0% | 94 | $-152 | -10.0% |
| Meeting minimum prize $30k+ | 130 | $231 | 14.7% | 88 | $452 | 36.9% | 66 | $135 | 12.5% |
| Meeting minimum prize $40k+ | 105 | $506 | 40.5% | 73 | $627 | 64.3% | 51 | $335 | 40.6% |
| Meeting minimum prize $50k+ | 73 | $813 | 98.5% | 51 | $689 | 110.3% | 33 | $497 | 94.7% |
| Good or firm going (1 to 4) | 168 | $30 | 1.5% | 115 | $356 | 22.2% | 80 | $-13 | -1.0% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 184 | $130 | 6.0% | 130 | $295 | 16.6% | 81 | $-40 | -3.2% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 98 | $581 | 49.5% | 70 | $652 | 68.6% | 49 | $385 | 49.6% |
| P(first third) 0.7+ | 58 | $-97 | -14.6% | 38 | $-125 | -23.4% | 58 | $-109 | -11.5% |
| P(first third) 0.5 to 0.7 | 65 | $417 | 48.3% | 41 | $519 | 78.1% | 36 | $-43 | -7.5% |
| P(first third) under 0.5 | 45 | $-178 | -37.6% | 30 | $-63 | -16.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 72 | $-327 | -36.3% | 58 | $-58 | -7.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 35 | $-292 | -83.3% | 17 | $-167 | -74.1% | 12 | $-175 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 139
- first starter, light-history or no-Proj runner: 77
- bush meeting: 33
