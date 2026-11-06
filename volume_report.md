# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 66; bets still open 1.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 25 | 50 | 2 | $625 | $248 | $-377 | -60.4% | -49.6% |
| Volume v2 | 21 | 40 | 2 | $525 | $248 | $-277 | -52.9% | -40.0% |
| Volume v3 (P cut) | 3 | 3 | 0 | $75 | $0 | $-75 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 4 | $-75 | 2 | $-50 | 3 | $-75 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 50 | $-377 | -60.4% | 40 | $-277 | -52.9% | 3 | $-75 | -100.0% |
| Meeting minimum prize $30k+ | 23 | $-275 | -100.0% | 17 | $-200 | -100.0% | 2 | $-50 | -100.0% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 36 | $-337 | -71.1% | 26 | $-237 | -63.3% | 2 | $-50 | -100.0% |
| $30k+ and good/firm | 13 | $-175 | -100.0% | 7 | $-100 | -100.0% | 1 | $-25 | -100.0% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| Field of 8 or more | 37 | $-202 | -45.0% | 32 | $-152 | -38.1% | 0 | $0 | None% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% | 0 | $0 | None% |
| P(first third) 0.7+ | 2 | $-38 | -100.0% | 2 | $-50 | -100.0% | 2 | $-50 | -100.0% |
| P(first third) 0.5 to 0.7 | 2 | $-38 | -100.0% | 0 | $0 | None% | 1 | $-25 | -100.0% |
| P(first third) under 0.5 | 0 | $0 | None% | 0 | $0 | None% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 11 | $-125 | -100.0% | 11 | $-125 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, under 25% won from first third | 10 | $-125 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% | 0 | $0 | None% |

## Races checked without a bet, by reason

- ok: 34
- first starter, light-history or no-Proj runner: 32
