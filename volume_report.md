# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 88; bets still open 5.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 36 | 74 | 2 | $900 | $248 | $-652 | -72.5% | -65.0% |
| Volume v2 | 30 | 55 | 2 | $750 | $248 | $-502 | -67.0% | -58.0% |
| Volume v3 (P cut) | 12 | 18 | 0 | $300 | $0 | $-300 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 28 | $-350 | 17 | $-275 | 18 | $-300 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 74 | $-652 | -72.5% | 55 | $-502 | -67.0% | 18 | $-300 | -100.0% |
| Meeting minimum prize $30k+ | 35 | $-425 | -100.0% | 24 | $-325 | -100.0% | 10 | $-175 | -100.0% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% | 0 | $0 | None% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 55 | $-537 | -79.6% | 37 | $-387 | -73.8% | 14 | $-225 | -100.0% |
| $30k+ and good/firm | 20 | $-250 | -100.0% | 10 | $-150 | -100.0% | 6 | $-100 | -100.0% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% | 0 | $0 | None% |
| Field of 8 or more | 61 | $-477 | -65.9% | 47 | $-377 | -60.4% | 15 | $-225 | -100.0% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% | 0 | $0 | None% |
| P(first third) 0.7+ | 11 | $-142 | -100.0% | 8 | $-129 | -100.0% | 11 | $-200 | -100.0% |
| P(first third) 0.5 to 0.7 | 12 | $-150 | -100.0% | 6 | $-88 | -100.0% | 7 | $-100 | -100.0% |
| P(first third) under 0.5 | 5 | $-58 | -100.0% | 3 | $-58 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 17 | $-225 | -100.0% | 16 | $-225 | -100.0% | 3 | $-50 | -100.0% |
| 3+ earlier races, under 25% won from first third | 24 | $-250 | -100.0% | 13 | $-175 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 15 | $-150 | -100.0% | 7 | $-100 | -100.0% | 9 | $-125 | -100.0% |

## Races checked without a bet, by reason

- ok: 48
- first starter, light-history or no-Proj runner: 40
