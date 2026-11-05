# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-05; races checked 35; bets still open 5.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 11 | 25 | 1 | $275 | $110 | $-165 | -60.0% | -58.2% |
| Volume v2 | 9 | 20 | 1 | $225 | $110 | $-115 | -51.1% | -48.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit |
|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 |
| 2026-11-05 | 20 | $-200 | 15 | $-150 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |
|---|---|---|---|---|---|---|
| All bets | 25 | $-165 | -60.0% | 20 | $-115 | -51.1% |
| Meeting minimum prize $30k+ | 14 | $-125 | -100.0% | 12 | $-100 | -100.0% |
| Meeting minimum prize $40k+ | 14 | $-125 | -100.0% | 12 | $-100 | -100.0% |
| Meeting minimum prize $50k+ | 11 | $-100 | -100.0% | 9 | $-75 | -100.0% |
| Good or firm going (1 to 4) | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% |
| $30k+ and good/firm | 5 | $-50 | -100.0% | 3 | $-25 | -100.0% |
| $40k+ and good/firm | 5 | $-50 | -100.0% | 3 | $-25 | -100.0% |
| Field of 8 or more | 16 | $-65 | -37.1% | 14 | $-40 | -26.7% |
| Field of 5 to 7 | 9 | $-100 | -100.0% | 6 | $-75 | -100.0% |
| $40k+ and field of 8+ | 11 | $-100 | -100.0% | 9 | $-75 | -100.0% |
| 3+ earlier races, 40%+ won from first third | 3 | $-25 | -100.0% | 3 | $-25 | -100.0% |
| 3+ earlier races, under 25% won from first third | 0 | $0 | None% | 0 | $0 | None% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 0 | $0 | None% | 0 | $0 | None% |

## Races checked without a bet, by reason

- ok: 20
- first starter, light-history or no-Proj runner: 15
