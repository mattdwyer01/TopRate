# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-09; races checked 283; bets still open 18.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 110 | 228 | 22 | $2737 | $2471 | $-267 | -9.7% | -8.8% |
| Volume v2 | 88 | 156 | 15 | $2200 | $2153 | $-47 | -2.1% | 0.5% |
| Volume v3 (P cut) | 66 | 101 | 12 | $1637 | $1535 | $-102 | -6.2% | -12.7% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 42 | $-278 | 27 | $-183 | 24 | $-186 |
| 2026-11-09 | 8 | $-6 | 4 | $-75 | 4 | $100 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 228 | $-267 | -9.7% | 156 | $-47 | -2.1% | 101 | $-102 | -6.2% |
| Meeting minimum prize $30k+ | 134 | $181 | 11.2% | 92 | $402 | 31.5% | 68 | $110 | 10.0% |
| Meeting minimum prize $40k+ | 109 | $456 | 35.1% | 77 | $577 | 56.3% | 53 | $310 | 36.4% |
| Meeting minimum prize $50k+ | 77 | $763 | 87.2% | 55 | $639 | 94.7% | 35 | $472 | 85.8% |
| Good or firm going (1 to 4) | 178 | $-27 | -1.2% | 120 | $256 | 15.0% | 85 | $62 | 4.6% |
| $30k+ and good/firm | 104 | $475 | 36.6% | 72 | $677 | 67.7% | 55 | $279 | 31.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 197 | $48 | 2.1% | 139 | $145 | 7.5% | 88 | $10 | 0.7% |
| Field of 5 to 7 | 31 | $-315 | -74.1% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 102 | $531 | 43.4% | 74 | $602 | 60.2% | 51 | $360 | 45.0% |
| P(first third) 0.7+ | 65 | $-95 | -12.8% | 43 | $-204 | -33.3% | 65 | $-59 | -5.6% |
| P(first third) 0.5 to 0.7 | 68 | $371 | 40.9% | 42 | $510 | 75.9% | 36 | $-43 | -7.5% |
| P(first third) under 0.5 | 49 | $-240 | -44.9% | 33 | $-125 | -28.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 79 | $-415 | -42.0% | 62 | $-133 | -15.2% | 36 | $-87 | -13.7% |
| 3+ earlier races, under 25% won from first third | 35 | $-292 | -83.3% | 17 | $-167 | -74.1% | 12 | $-175 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 154
- first starter, light-history or no-Proj runner: 89
- bush meeting: 40
