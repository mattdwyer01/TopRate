# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-09; races checked 285; bets still open 13.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 113 | 233 | 22 | $2812 | $2471 | $-342 | -12.1% | -11.2% |
| Volume v2 | 90 | 159 | 15 | $2250 | $2153 | $-97 | -4.3% | -1.7% |
| Volume v3 (P cut) | 68 | 103 | 12 | $1687 | $1535 | $-152 | -9.0% | -15.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 42 | $-278 | 27 | $-183 | 24 | $-186 |
| 2026-11-09 | 13 | $-81 | 7 | $-125 | 6 | $50 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 233 | $-342 | -12.1% | 159 | $-97 | -4.3% | 103 | $-152 | -9.0% |
| Meeting minimum prize $30k+ | 134 | $181 | 11.2% | 92 | $402 | 31.5% | 68 | $110 | 10.0% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 183 | $-102 | -4.5% | 123 | $206 | 11.8% | 87 | $12 | 0.9% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 200 | $-2 | -0.1% | 140 | $120 | 6.2% | 89 | $-15 | -1.1% |
| Field of 5 to 7 | 33 | $-340 | -75.6% | 19 | $-217 | -72.2% | 14 | $-137 | -45.6% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 66 | $-108 | -14.3% | 44 | $-217 | -34.7% | 66 | $-84 | -7.7% |
| P(first third) 0.5 to 0.7 | 70 | $334 | 35.3% | 43 | $485 | 69.6% | 37 | $-68 | -11.4% |
| P(first third) under 0.5 | 51 | $-265 | -47.4% | 34 | $-138 | -30.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 82 | $-465 | -44.8% | 63 | $-158 | -17.6% | 37 | $-112 | -17.0% |
| 3+ earlier races, under 25% won from first third | 35 | $-292 | -83.3% | 17 | $-167 | -74.1% | 12 | $-175 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 154
- first starter, light-history or no-Proj runner: 90
- bush meeting: 40
- field under 5: 1
