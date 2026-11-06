# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-06; races checked 92; bets still open 4.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 38 | 81 | 2 | $950 | $248 | $-702 | -73.9% | -66.8% |
| Volume v2 | 31 | 57 | 2 | $775 | $248 | $-527 | -68.1% | -59.4% |
| Volume v3 (P cut) | 14 | 23 | 0 | $350 | $0 | $-350 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 35 | $-400 | 19 | $-300 | 23 | $-350 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 81 | $-702 | -73.9% | 57 | $-527 | -68.1% | 23 | $-350 | -100.0% |
| Meeting minimum prize $30k+ | 37 | $-450 | -100.0% | 26 | $-350 | -100.0% | 13 | $-200 | -100.0% |
| Meeting minimum prize $40k+ | 23 | $-250 | -100.0% | 18 | $-200 | -100.0% | 3 | $-25 | -100.0% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 62 | $-587 | -81.0% | 39 | $-412 | -75.0% | 19 | $-275 | -100.0% |
| $30k+ and good/firm | 22 | $-275 | -100.0% | 12 | $-175 | -100.0% | 9 | $-125 | -100.0% |
| $40k+ and good/firm | 14 | $-175 | -100.0% | 9 | $-125 | -100.0% | 3 | $-25 | -100.0% |
| Field of 8 or more | 68 | $-527 | -68.1% | 49 | $-402 | -61.9% | 20 | $-275 | -100.0% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 20 | $-225 | -100.0% | 15 | $-175 | -100.0% | 3 | $-25 | -100.0% |
| P(first third) 0.7+ | 13 | $-152 | -100.0% | 8 | $-129 | -100.0% | 13 | $-225 | -100.0% |
| P(first third) 0.5 to 0.7 | 14 | $-175 | -100.0% | 8 | $-112 | -100.0% | 10 | $-125 | -100.0% |
| P(first third) under 0.5 | 8 | $-73 | -100.0% | 3 | $-58 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 19 | $-250 | -100.0% | 18 | $-250 | -100.0% | 6 | $-75 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 52
- first starter, light-history or no-Proj runner: 40
