# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 134; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 46 | 98 | 5 | $1150 | $492 | $-657 | -57.2% | -51.3% |
| Volume v2 | 36 | 66 | 4 | $900 | $457 | $-442 | -49.2% | -41.7% |
| Volume v3 (P cut) | 20 | 33 | 2 | $500 | $179 | $-321 | -64.2% | -64.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 13 | $95 | 8 | $110 | 7 | $79 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 98 | $-657 | -57.2% | 66 | $-442 | -49.2% | 33 | $-321 | -64.2% |
| Meeting minimum prize $30k+ | 54 | $-405 | -62.3% | 35 | $-265 | -55.8% | 23 | $-171 | -48.9% |
| Meeting minimum prize $40k+ | 40 | $-205 | -45.6% | 27 | $-115 | -35.4% | 13 | $4 | 2.1% |
| Meeting minimum prize $50k+ | 30 | $-80 | -24.6% | 20 | $-15 | -6.7% | 7 | $79 | 78.8% |
| Good or firm going (1 to 4) | 79 | $-542 | -58.6% | 48 | $-328 | -48.5% | 29 | $-246 | -57.9% |
| $30k+ and good/firm | 39 | $-230 | -48.4% | 21 | $-90 | -30.0% | 19 | $-96 | -35.0% |
| $40k+ and good/firm | 31 | $-130 | -34.7% | 18 | $-40 | -16.0% | 13 | $4 | 2.1% |
| Field of 8 or more | 85 | $-482 | -49.5% | 58 | $-318 | -41.0% | 30 | $-246 | -57.9% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 37 | $-180 | -42.3% | 24 | $-90 | -30.0% | 13 | $4 | 2.1% |
| P(first third) 0.7+ | 20 | $-77 | -32.6% | 12 | $-58 | -31.8% | 20 | $-152 | -46.0% |
| P(first third) 0.5 to 0.7 | 20 | $-231 | -100.0% | 11 | $-146 | -100.0% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 12 | $-47 | -35.4% | 5 | $-11 | -11.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 23 | $-300 | -100.0% | 19 | $-275 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 68
- first starter, light-history or no-Proj runner: 53
- bush meeting: 13
