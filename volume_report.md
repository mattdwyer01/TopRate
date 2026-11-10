# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-10; races checked 298; bets still open 11.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 117 | 243 | 22 | $2912 | $2471 | $-442 | -15.2% | -13.4% |
| Volume v2 | 93 | 165 | 15 | $2325 | $2153 | $-172 | -7.4% | -4.9% |
| Volume v3 (P cut) | 72 | 110 | 12 | $1787 | $1535 | $-252 | -14.1% | -17.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 42 | $-278 | 27 | $-183 | 24 | $-186 |
| 2026-11-09 | 16 | $-106 | 10 | $-150 | 7 | $25 |
| 2026-11-10 | 7 | $-75 | 3 | $-50 | 6 | $-75 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 243 | $-442 | -15.2% | 165 | $-172 | -7.4% | 110 | $-252 | -14.1% |
| Meeting minimum prize $30k+ | 134 | $181 | 11.2% | 92 | $402 | 31.5% | 68 | $110 | 10.0% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 193 | $-202 | -8.6% | 129 | $131 | 7.2% | 94 | $-88 | -5.8% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 204 | $-52 | -2.1% | 143 | $70 | 3.5% | 92 | $-65 | -4.5% |
| Field of 5 to 7 | 39 | $-390 | -78.0% | 22 | $-242 | -74.4% | 18 | $-187 | -53.3% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 69 | $-133 | -17.0% | 45 | $-225 | -35.5% | 69 | $-126 | -11.1% |
| P(first third) 0.5 to 0.7 | 76 | $267 | 26.4% | 47 | $427 | 56.5% | 41 | $-126 | -19.2% |
| P(first third) under 0.5 | 52 | $-273 | -48.2% | 35 | $-146 | -31.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 82 | $-465 | -44.8% | 63 | $-158 | -17.6% | 37 | $-112 | -17.0% |
| 3+ earlier races, under 25% won from first third | 40 | $-342 | -85.4% | 21 | $-217 | -78.8% | 14 | $-225 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 22 | $-200 | -100.0% | 8 | $-125 | -100.0% | 12 | $-175 | -100.0% |

## Races checked without a bet, by reason

- ok: 162
- first starter, light-history or no-Proj runner: 95
- bush meeting: 40
- field under 5: 1
