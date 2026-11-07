# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 167; bets still open 9.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 59 | 123 | 7 | $1475 | $730 | $-745 | -50.5% | -45.9% |
| Volume v2 | 47 | 87 | 6 | $1175 | $695 | $-480 | -40.9% | -35.1% |
| Volume v3 (P cut) | 27 | 43 | 2 | $675 | $179 | $-496 | -73.5% | -73.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 38 | $8 | 29 | $72 | 17 | $-96 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 123 | $-745 | -50.5% | 87 | $-480 | -40.9% | 43 | $-496 | -73.5% |
| Meeting minimum prize $30k+ | 71 | $-480 | -54.9% | 50 | $-315 | -46.7% | 32 | $-321 | -64.2% |
| Meeting minimum prize $40k+ | 57 | $-280 | -41.5% | 42 | $-165 | -31.4% | 22 | $-146 | -45.0% |
| Meeting minimum prize $50k+ | 45 | $-105 | -21.0% | 33 | $-15 | -4.0% | 16 | $-71 | -28.5% |
| Good or firm going (1 to 4) | 97 | $-642 | -54.7% | 63 | $-378 | -43.1% | 38 | $-396 | -68.9% |
| $30k+ and good/firm | 56 | $-305 | -43.6% | 36 | $-140 | -28.0% | 28 | $-246 | -57.9% |
| $40k+ and good/firm | 48 | $-205 | -34.2% | 33 | $-90 | -20.0% | 22 | $-146 | -45.0% |
| Field of 8 or more | 107 | $-520 | -41.6% | 78 | $-330 | -32.2% | 39 | $-396 | -68.9% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 54 | $-255 | -39.2% | 39 | $-140 | -28.0% | 22 | $-146 | -45.0% |
| P(first third) 0.7+ | 29 | $-182 | -53.2% | 19 | $-138 | -52.4% | 29 | $-319 | -64.1% |
| P(first third) 0.5 to 0.7 | 29 | $-125 | -34.4% | 19 | $-27 | -10.2% | 14 | $-177 | -100.0% |
| P(first third) under 0.5 | 19 | $-136 | -61.6% | 11 | $-88 | -50.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 35 | $-275 | -64.7% | 31 | $-250 | -62.5% | 14 | $-225 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 85
- first starter, light-history or no-Proj runner: 58
- bush meeting: 24
