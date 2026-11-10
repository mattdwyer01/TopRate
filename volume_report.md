# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-10; races checked 292; bets still open 15.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 114 | 236 | 22 | $2837 | $2471 | $-367 | -12.9% | -11.1% |
| Volume v2 | 91 | 162 | 15 | $2275 | $2153 | $-122 | -5.3% | -2.8% |
| Volume v3 (P cut) | 69 | 104 | 12 | $1712 | $1535 | $-177 | -10.3% | -13.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 42 | $-278 | 27 | $-183 | 24 | $-186 |
| 2026-11-09 | 16 | $-106 | 10 | $-150 | 7 | $25 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 236 | $-367 | -12.9% | 162 | $-122 | -5.3% | 104 | $-177 | -10.3% |
| Meeting minimum prize $30k+ | 134 | $181 | 11.2% | 92 | $402 | 31.5% | 68 | $110 | 10.0% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 186 | $-127 | -5.6% | 126 | $181 | 10.2% | 88 | $-13 | -0.9% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 200 | $-2 | -0.1% | 140 | $120 | 6.2% | 89 | $-15 | -1.1% |
| Field of 5 to 7 | 36 | $-365 | -76.8% | 22 | $-242 | -74.4% | 15 | $-162 | -49.8% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 67 | $-116 | -15.2% | 45 | $-225 | -35.5% | 67 | $-109 | -9.8% |
| P(first third) 0.5 to 0.7 | 71 | $325 | 34.1% | 44 | $477 | 67.6% | 37 | $-68 | -11.4% |
| P(first third) under 0.5 | 52 | $-273 | -48.2% | 35 | $-146 | -31.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 82 | $-465 | -44.8% | 63 | $-158 | -17.6% | 37 | $-112 | -17.0% |
| 3+ earlier races, under 25% won from first third | 38 | $-317 | -84.4% | 20 | $-192 | -76.7% | 13 | $-200 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 158
- first starter, light-history or no-Proj runner: 93
- bush meeting: 40
- field under 5: 1
