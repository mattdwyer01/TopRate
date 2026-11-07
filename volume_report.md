# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 152; bets still open 15.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 53 | 110 | 7 | $1325 | $730 | $-595 | -44.9% | -39.8% |
| Volume v2 | 42 | 75 | 6 | $1050 | $695 | $-355 | -33.8% | -27.4% |
| Volume v3 (P cut) | 24 | 38 | 2 | $600 | $179 | $-421 | -70.2% | -70.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 25 | $158 | 17 | $197 | 12 | $-21 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 110 | $-595 | -44.9% | 75 | $-355 | -33.8% | 38 | $-421 | -70.2% |
| Meeting minimum prize $30k+ | 63 | $-380 | -49.0% | 42 | $-215 | -37.4% | 27 | $-246 | -57.9% |
| Meeting minimum prize $40k+ | 49 | $-180 | -31.3% | 34 | $-65 | -15.3% | 17 | $-71 | -28.5% |
| Meeting minimum prize $50k+ | 38 | $-30 | -7.1% | 26 | $60 | 20.0% | 11 | $4 | 2.1% |
| Good or firm going (1 to 4) | 88 | $-517 | -49.3% | 55 | $-278 | -35.8% | 33 | $-321 | -64.2% |
| $30k+ and good/firm | 48 | $-205 | -34.2% | 28 | $-40 | -10.0% | 23 | $-171 | -48.9% |
| $40k+ and good/firm | 40 | $-105 | -21.0% | 25 | $10 | 2.9% | 17 | $-71 | -28.5% |
| Field of 8 or more | 95 | $-395 | -35.1% | 66 | $-205 | -22.8% | 34 | $-321 | -64.2% |
| Field of 5 to 7 | 15 | $-200 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 46 | $-155 | -28.2% | 31 | $-40 | -10.0% | 17 | $-71 | -28.5% |
| P(first third) 0.7+ | 25 | $-132 | -45.1% | 15 | $-88 | -41.2% | 25 | $-252 | -58.6% |
| P(first third) 0.5 to 0.7 | 24 | $-68 | -22.3% | 15 | $4 | 1.8% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 15 | $-92 | -52.1% | 7 | $-44 | -34.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 28 | $-200 | -57.1% | 24 | $-175 | -53.8% | 12 | $-175 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 78
- first starter, light-history or no-Proj runner: 55
- bush meeting: 19
