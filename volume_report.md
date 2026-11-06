# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 85; bets still open 4.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 34 | 70 | 2 | $850 | $248 | $-602 | -70.9% | -62.9% |
| Volume v2 | 28 | 51 | 2 | $700 | $248 | $-452 | -64.6% | -55.0% |
| Volume v3 (P cut) | 11 | 16 | 0 | $275 | $0 | $-275 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 24 | $-300 | 13 | $-225 | 16 | $-275 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 70 | $-602 | -70.9% | 51 | $-452 | -64.6% | 16 | $-275 | -100.0% |
| Meeting minimum prize $30k+ | 35 | $-425 | -100.0% | 24 | $-325 | -100.0% | 10 | $-175 | -100.0% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 51 | $-487 | -78.0% | 33 | $-337 | -71.1% | 12 | $-200 | -100.0% |
| $30k+ and good/firm | 20 | $-250 | -100.0% | 10 | $-150 | -100.0% | 6 | $-100 | -100.0% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| Field of 8 or more | 57 | $-427 | -63.3% | 43 | $-327 | -57.0% | 13 | $-200 | -100.0% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% | 0 | $0 | None% |
| P(first third) 0.7+ | 9 | $-125 | -100.0% | 6 | $-112 | -100.0% | 9 | $-175 | -100.0% |
| P(first third) 0.5 to 0.7 | 11 | $-125 | -100.0% | 5 | $-62 | -100.0% | 7 | $-100 | -100.0% |
| P(first third) under 0.5 | 4 | $-50 | -100.0% | 2 | $-50 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 16 | $-200 | -100.0% | 15 | $-200 | -100.0% | 3 | $-50 | -100.0% |
| 3+ earlier races, under 25% won from first third | 21 | $-225 | -100.0% | 10 | $-150 | -100.0% | 7 | $-100 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 12 | $-125 | -100.0% | 4 | $-75 | -100.0% | 7 | $-100 | -100.0% |

## Races checked without a bet, by reason

- ok: 47
- first starter, light-history or no-Proj runner: 38
