# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-05; races checked 14; bets still open 7.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 4 | 7 | 1 | $100 | $110 | $10 | 10.0% | 15.0% |
| Volume v2 | 4 | 7 | 1 | $100 | $110 | $10 | 10.0% | 15.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit |
|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 |
| 2026-11-05 | 2 | $-25 | 2 | $-25 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |
|---|---|---|---|---|---|---|
| All bets | 7 | $10 | 10.0% | 7 | $10 | 10.0% |
| Meeting minimum prize $30k+ | 2 | $-25 | -100.0% | 2 | $-25 | -100.0% |
| Meeting minimum prize $40k+ | 2 | $-25 | -100.0% | 2 | $-25 | -100.0% |
| Meeting minimum prize $50k+ | 2 | $-25 | -100.0% | 2 | $-25 | -100.0% |
| Good or firm going (1 to 4) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% |
| $30k+ and good/firm | 0 | $0 | None% | 0 | $0 | None% |
| $40k+ and good/firm | 0 | $0 | None% | 0 | $0 | None% |
| Field of 8 or more | 7 | $10 | 10.0% | 7 | $10 | 10.0% |
| Field of 5 to 7 | 0 | $0 | None% | 0 | $0 | None% |
| $40k+ and field of 8+ | 2 | $-25 | -100.0% | 2 | $-25 | -100.0% |
| 3+ earlier races, 40%+ won from first third | 0 | $0 | None% | 0 | $0 | None% |
| 3+ earlier races, under 25% won from first third | 0 | $0 | None% | 0 | $0 | None% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 0 | $0 | None% | 0 | $0 | None% |

## Races checked without a bet, by reason

- ok: 9
- first starter, light-history or no-Proj runner: 5
