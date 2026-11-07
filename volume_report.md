# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 182; bets still open 17.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 63 | 131 | 8 | $1575 | $780 | $-795 | -50.5% | -46.2% |
| Volume v2 | 51 | 93 | 7 | $1275 | $845 | $-430 | -33.7% | -28.4% |
| Volume v3 (P cut) | 30 | 48 | 2 | $750 | $179 | $-571 | -76.2% | -76.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 46 | $-42 | 35 | $122 | 22 | $-171 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 131 | $-795 | -50.5% | 93 | $-430 | -33.7% | 48 | $-571 | -76.2% |
| Meeting minimum prize $30k+ | 79 | $-530 | -54.4% | 56 | $-265 | -34.2% | 37 | $-396 | -68.9% |
| Meeting minimum prize $40k+ | 65 | $-330 | -42.6% | 48 | $-115 | -18.4% | 27 | $-221 | -55.3% |
| Meeting minimum prize $50k+ | 47 | $-155 | -28.2% | 35 | $-65 | -15.3% | 17 | $-96 | -35.0% |
| Good or firm going (1 to 4) | 105 | $-692 | -54.3% | 69 | $-327 | -33.6% | 43 | $-471 | -72.5% |
| $30k+ and good/firm | 64 | $-355 | -44.4% | 42 | $-90 | -15.0% | 33 | $-321 | -64.2% |
| $40k+ and good/firm | 56 | $-255 | -36.4% | 39 | $-40 | -7.3% | 27 | $-221 | -55.3% |
| Field of 8 or more | 115 | $-570 | -42.2% | 84 | $-280 | -24.9% | 44 | $-471 | -72.5% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 62 | $-305 | -40.7% | 45 | $-90 | -15.0% | 27 | $-221 | -55.3% |
| P(first third) 0.7+ | 32 | $-207 | -56.4% | 20 | $-146 | -53.9% | 32 | $-357 | -66.6% |
| P(first third) 0.5 to 0.7 | 32 | $-183 | -43.5% | 22 | $-85 | -26.5% | 16 | $-215 | -100.0% |
| P(first third) under 0.5 | 21 | $-103 | -43.3% | 13 | $29 | 13.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 39 | $-275 | -57.9% | 33 | $-150 | -33.3% | 17 | $-275 | -100.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 94
- first starter, light-history or no-Proj runner: 59
- bush meeting: 29
