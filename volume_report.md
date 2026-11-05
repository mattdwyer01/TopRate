# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-05; races checked 39; bets still open 2.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 13 | 28 | 1 | $325 | $110 | $-215 | -66.1% | -64.6% |
| Volume v2 | 10 | 21 | 1 | $250 | $110 | $-140 | -56.0% | -54.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit |
|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 |
| 2026-11-05 | 23 | $-250 | 16 | $-175 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |
|---|---|---|---|---|---|---|
| All bets | 28 | $-215 | -66.1% | 21 | $-140 | -56.0% |
| Meeting minimum prize $30k+ | 16 | $-150 | -100.0% | 12 | $-100 | -100.0% |
| Meeting minimum prize $40k+ | 16 | $-150 | -100.0% | 12 | $-100 | -100.0% |
| Meeting minimum prize $50k+ | 13 | $-125 | -100.0% | 9 | $-75 | -100.0% |
| Good or firm going (1 to 4) | 15 | $-200 | -100.0% | 8 | $-125 | -100.0% |
| $30k+ and good/firm | 7 | $-75 | -100.0% | 3 | $-25 | -100.0% |
| $40k+ and good/firm | 7 | $-75 | -100.0% | 3 | $-25 | -100.0% |
| Field of 8 or more | 19 | $-115 | -51.1% | 15 | $-65 | -37.1% |
| Field of 5 to 7 | 9 | $-100 | -100.0% | 6 | $-75 | -100.0% |
| $40k+ and field of 8+ | 13 | $-125 | -100.0% | 9 | $-75 | -100.0% |
| 3+ earlier races, 40%+ won from first third | 4 | $-50 | -100.0% | 4 | $-50 | -100.0% |
| 3+ earlier races, under 25% won from first third | 2 | $-25 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 0 | $0 | None% | 0 | $0 | None% |

## Races checked without a bet, by reason

- ok: 21
- first starter, light-history or no-Proj runner: 18
