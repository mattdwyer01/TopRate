# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 247; bets still open 6.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 101 | 213 | 21 | $2525 | $2389 | $-135 | -5.4% | -5.1% |
| Volume v2 | 81 | 146 | 15 | $2025 | $2153 | $128 | 6.3% | 8.1% |
| Volume v3 (P cut) | 60 | 93 | 11 | $1500 | $1373 | $-127 | -8.5% | -15.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 35 | $-153 | 21 | $-83 | 20 | $-111 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 213 | $-135 | -5.4% | 146 | $128 | 6.3% | 93 | $-127 | -8.5% |
| Meeting minimum prize $30k+ | 130 | $231 | 14.7% | 88 | $452 | 36.9% | 66 | $135 | 12.5% |
| Meeting minimum prize $40k+ | 105 | $506 | 40.5% | 73 | $627 | 64.3% | 51 | $335 | 40.6% |
| Meeting minimum prize $50k+ | 73 | $813 | 98.5% | 51 | $689 | 110.3% | 33 | $497 | 94.7% |
| Good or firm going (1 to 4) | 167 | $55 | 2.7% | 114 | $381 | 24.2% | 79 | $12 | 1.0% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 183 | $155 | 7.3% | 129 | $320 | 18.3% | 80 | $-15 | -1.3% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 98 | $581 | 49.5% | 70 | $652 | 68.6% | 49 | $385 | 49.6% |
| P(first third) 0.7+ | 58 | $-97 | -14.6% | 38 | $-125 | -23.4% | 58 | $-109 | -11.5% |
| P(first third) 0.5 to 0.7 | 64 | $442 | 52.8% | 40 | $544 | 85.0% | 35 | $-18 | -3.3% |
| P(first third) under 0.5 | 45 | $-178 | -37.6% | 30 | $-63 | -16.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 72 | $-327 | -36.3% | 58 | $-58 | -7.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 35 | $-292 | -83.3% | 17 | $-167 | -74.1% | 12 | $-175 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 137
- first starter, light-history or no-Proj runner: 77
- bush meeting: 33
