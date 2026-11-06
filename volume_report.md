# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 80; bets still open 9.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 30 | 61 | 2 | $750 | $248 | $-502 | -67.0% | -58.0% |
| Volume v2 | 25 | 46 | 2 | $625 | $248 | $-377 | -60.4% | -49.6% |
| Volume v3 (P cut) | 7 | 10 | 0 | $175 | $0 | $-175 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 15 | $-200 | 8 | $-150 | 10 | $-175 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 61 | $-502 | -67.0% | 46 | $-377 | -60.4% | 10 | $-175 | -100.0% |
| Meeting minimum prize $30k+ | 28 | $-350 | -100.0% | 21 | $-275 | -100.0% | 5 | $-100 | -100.0% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 44 | $-412 | -75.0% | 30 | $-287 | -67.6% | 8 | $-125 | -100.0% |
| $30k+ and good/firm | 15 | $-200 | -100.0% | 9 | $-125 | -100.0% | 3 | $-50 | -100.0% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| Field of 8 or more | 48 | $-327 | -57.0% | 38 | $-252 | -50.5% | 7 | $-100 | -100.0% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% | 0 | $0 | None% |
| P(first third) 0.7+ | 4 | $-62 | -100.0% | 3 | $-62 | -100.0% | 4 | $-88 | -100.0% |
| P(first third) 0.5 to 0.7 | 9 | $-100 | -100.0% | 3 | $-38 | -100.0% | 6 | $-88 | -100.0% |
| P(first third) under 0.5 | 2 | $-38 | -100.0% | 2 | $-50 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 14 | $-175 | -100.0% | 13 | $-175 | -100.0% | 1 | $-25 | -100.0% |
| 3+ earlier races, under 25% won from first third | 16 | $-175 | -100.0% | 9 | $-125 | -100.0% | 4 | $-50 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 7 | $-75 | -100.0% | 3 | $-50 | -100.0% | 4 | $-50 | -100.0% |

## Races checked without a bet, by reason

- ok: 45
- first starter, light-history or no-Proj runner: 35
