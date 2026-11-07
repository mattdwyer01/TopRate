# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 166; bets still open 10.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 58 | 122 | 7 | $1450 | $730 | $-720 | -49.7% | -45.0% |
| Volume v2 | 46 | 86 | 6 | $1150 | $695 | $-455 | -39.6% | -33.7% |
| Volume v3 (P cut) | 27 | 43 | 2 | $675 | $179 | $-496 | -73.5% | -73.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 37 | $33 | 28 | $97 | 17 | $-96 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 122 | $-720 | -49.7% | 86 | $-455 | -39.6% | 43 | $-496 | -73.5% |
| Meeting minimum prize $30k+ | 70 | $-455 | -53.5% | 49 | $-290 | -44.6% | 32 | $-321 | -64.2% |
| Meeting minimum prize $40k+ | 56 | $-255 | -39.2% | 41 | $-140 | -28.0% | 22 | $-146 | -45.0% |
| Meeting minimum prize $50k+ | 45 | $-105 | -21.0% | 33 | $-15 | -4.0% | 16 | $-71 | -28.5% |
| Good or firm going (1 to 4) | 96 | $-617 | -53.7% | 62 | $-352 | -41.5% | 38 | $-396 | -68.9% |
| $30k+ and good/firm | 55 | $-280 | -41.5% | 35 | $-115 | -24.2% | 28 | $-246 | -57.9% |
| $40k+ and good/firm | 47 | $-180 | -31.3% | 32 | $-65 | -15.3% | 22 | $-146 | -45.0% |
| Field of 8 or more | 106 | $-495 | -40.4% | 77 | $-305 | -30.5% | 39 | $-396 | -68.9% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 53 | $-230 | -36.8% | 38 | $-115 | -24.2% | 22 | $-146 | -45.0% |
| P(first third) 0.7+ | 29 | $-182 | -53.2% | 19 | $-138 | -52.4% | 29 | $-319 | -64.1% |
| P(first third) 0.5 to 0.7 | 29 | $-125 | -34.4% | 19 | $-27 | -10.2% | 14 | $-177 | -100.0% |
| P(first third) under 0.5 | 18 | $-111 | -56.7% | 10 | $-63 | -42.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 35 | $-275 | -64.7% | 31 | $-250 | -62.5% | 14 | $-225 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 84
- first starter, light-history or no-Proj runner: 58
- bush meeting: 24
