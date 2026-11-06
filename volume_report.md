# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 58; bets still open 2.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 22 | 46 | 2 | $550 | $248 | $-302 | -55.0% | -42.7% |
| Volume v2 | 19 | 38 | 2 | $475 | $248 | $-227 | -47.9% | -33.7% |
| Volume v3 (P cut) | 0 | 0 | 0 | $0 | $0 | $0 | None% | None% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 46 | $-302 | -55.0% | 38 | $-227 | -47.9% | 0 | $0 | None% |
| Meeting minimum prize $30k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 33 | $-287 | -67.6% | 25 | $-212 | -60.7% | 0 | $0 | None% |
| $30k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| Field of 8 or more | 37 | $-202 | -45.0% | 32 | $-152 | -38.1% | 0 | $0 | None% |
| Field of 5 to 7 | 9 | $-100 | -100.0% | 6 | $-75 | -100.0% | 0 | $0 | None% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% | 0 | $0 | None% |
| P(first third) 0.7+ | 0 | $0 | None% | 0 | $0 | None% | 0 | $0 | None% |
| P(first third) 0.5 to 0.7 | 0 | $0 | None% | 0 | $0 | None% | 0 | $0 | None% |
| P(first third) under 0.5 | 0 | $0 | None% | 0 | $0 | None% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 11 | $-125 | -100.0% | 11 | $-125 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, under 25% won from first third | 10 | $-125 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% | 0 | $0 | None% |

## Races checked without a bet, by reason

- ok: 32
- first starter, light-history or no-Proj runner: 26
