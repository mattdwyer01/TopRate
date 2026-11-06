# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 60; bets still open 3.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 23 | 47 | 2 | $575 | $248 | $-327 | -57.0% | -45.2% |
| Volume v2 | 20 | 39 | 2 | $500 | $248 | $-252 | -50.5% | -37.0% |
| Volume v3 (P cut) | 1 | 1 | 0 | $25 | $0 | $-25 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 1 | $-25 | 1 | $-25 | 1 | $-25 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 47 | $-327 | -57.0% | 39 | $-252 | -50.5% | 1 | $-25 | -100.0% |
| Meeting minimum prize $30k+ | 22 | $-250 | -100.0% | 17 | $-200 | -100.0% | 1 | $-25 | -100.0% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 33 | $-287 | -67.6% | 25 | $-212 | -60.7% | 0 | $0 | None% |
| $30k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| Field of 8 or more | 37 | $-202 | -45.0% | 32 | $-152 | -38.1% | 0 | $0 | None% |
| Field of 5 to 7 | 10 | $-125 | -100.0% | 7 | $-100 | -100.0% | 1 | $-25 | -100.0% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% | 0 | $0 | None% |
| P(first third) 0.7+ | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% |
| P(first third) 0.5 to 0.7 | 0 | $0 | None% | 0 | $0 | None% | 0 | $0 | None% |
| P(first third) under 0.5 | 0 | $0 | None% | 0 | $0 | None% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 11 | $-125 | -100.0% | 11 | $-125 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, under 25% won from first third | 10 | $-125 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% | 0 | $0 | None% |

## Races checked without a bet, by reason

- ok: 33
- first starter, light-history or no-Proj runner: 27
