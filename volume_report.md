# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 243; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 98 | 206 | 19 | $2450 | $2281 | $-169 | -6.9% | -6.7% |
| Volume v2 | 78 | 140 | 13 | $1950 | $2020 | $70 | 3.6% | 5.5% |
| Volume v3 (P cut) | 58 | 89 | 10 | $1450 | $1323 | $-127 | -8.8% | -16.1% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 28 | $-186 | 15 | $-142 | 16 | $-111 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 206 | $-169 | -6.9% | 140 | $70 | 3.6% | 89 | $-127 | -8.8% |
| Meeting minimum prize $30k+ | 126 | $231 | 15.2% | 85 | $427 | 36.3% | 63 | $110 | 10.4% |
| Meeting minimum prize $40k+ | 105 | $506 | 40.5% | 73 | $627 | 64.3% | 51 | $335 | 40.6% |
| Meeting minimum prize $50k+ | 73 | $813 | 98.5% | 51 | $689 | 110.3% | 33 | $497 | 94.7% |
| Good or firm going (1 to 4) | 160 | $21 | 1.1% | 108 | $322 | 21.5% | 75 | $12 | 1.0% |
| $30k+ and good/firm | 100 | $475 | 38.0% | 69 | $652 | 68.6% | 52 | $254 | 29.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 176 | $121 | 5.9% | 123 | $262 | 15.6% | 76 | $-15 | -1.3% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 98 | $581 | 49.5% | 70 | $652 | 68.6% | 49 | $385 | 49.6% |
| P(first third) 0.7+ | 56 | $-81 | -12.5% | 37 | $-113 | -21.6% | 56 | $-93 | -9.9% |
| P(first third) 0.5 to 0.7 | 60 | $384 | 48.7% | 36 | $465 | 79.4% | 33 | $-35 | -6.7% |
| P(first third) under 0.5 | 44 | $-169 | -36.5% | 29 | $-55 | -14.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 71 | $-302 | -34.5% | 57 | $-33 | -4.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 32 | $-325 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 135
- first starter, light-history or no-Proj runner: 75
- bush meeting: 33
