# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 124; bets still open 7.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 44 | 95 | 4 | $1100 | $408 | $-692 | -63.0% | -56.8% |
| Volume v2 | 36 | 66 | 4 | $900 | $457 | $-442 | -49.2% | -41.7% |
| Volume v3 (P cut) | 18 | 31 | 1 | $450 | $94 | $-356 | -79.2% | -79.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 10 | $60 | 8 | $110 | 5 | $44 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 95 | $-692 | -63.0% | 66 | $-442 | -49.2% | 31 | $-356 | -79.2% |
| Meeting minimum prize $30k+ | 51 | $-440 | -73.3% | 35 | $-265 | -55.8% | 21 | $-206 | -68.7% |
| Meeting minimum prize $40k+ | 37 | $-240 | -60.0% | 27 | $-115 | -35.4% | 11 | $-31 | -25.0% |
| Meeting minimum prize $50k+ | 27 | $-115 | -41.8% | 20 | $-15 | -6.7% | 5 | $44 | 87.5% |
| Good or firm going (1 to 4) | 76 | $-577 | -66.0% | 48 | $-328 | -48.5% | 27 | $-281 | -75.0% |
| $30k+ and good/firm | 36 | $-265 | -62.4% | 21 | $-90 | -30.0% | 17 | $-131 | -58.3% |
| $40k+ and good/firm | 28 | $-165 | -50.8% | 18 | $-40 | -16.0% | 11 | $-31 | -25.0% |
| Field of 8 or more | 82 | $-517 | -55.9% | 58 | $-318 | -41.0% | 28 | $-281 | -75.0% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 34 | $-215 | -57.3% | 24 | $-90 | -30.0% | 11 | $-31 | -25.0% |
| P(first third) 0.7+ | 19 | $-137 | -64.7% | 12 | $-58 | -31.8% | 19 | $-212 | -69.4% |
| P(first third) 0.5 to 0.7 | 19 | $-218 | -100.0% | 11 | $-146 | -100.0% | 12 | $-144 | -100.0% |
| P(first third) under 0.5 | 11 | $-34 | -28.7% | 5 | $-11 | -11.3% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 23 | $-300 | -100.0% | 19 | $-275 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 63
- first starter, light-history or no-Proj runner: 52
- bush meeting: 9
