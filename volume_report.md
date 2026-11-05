# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-05; races checked 43; bets still open 5.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 15 | 30 | 1 | $375 | $110 | $-265 | -70.7% | -69.3% |
| Volume v2 | 12 | 23 | 1 | $300 | $110 | $-190 | -63.3% | -61.7% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit |
|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 |
| 2026-11-05 | 25 | $-300 | 18 | $-225 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |
|---|---|---|---|---|---|---|
| All bets | 30 | $-265 | -70.7% | 23 | $-190 | -63.3% |
| Meeting minimum prize $30k+ | 17 | $-175 | -100.0% | 13 | $-125 | -100.0% |
| Meeting minimum prize $40k+ | 17 | $-175 | -100.0% | 13 | $-125 | -100.0% |
| Meeting minimum prize $50k+ | 13 | $-125 | -100.0% | 9 | $-75 | -100.0% |
| Good or firm going (1 to 4) | 17 | $-250 | -100.0% | 10 | $-175 | -100.0% |
| $30k+ and good/firm | 8 | $-100 | -100.0% | 4 | $-50 | -100.0% |
| $40k+ and good/firm | 8 | $-100 | -100.0% | 4 | $-50 | -100.0% |
| Field of 8 or more | 21 | $-165 | -60.0% | 17 | $-115 | -51.1% |
| Field of 5 to 7 | 9 | $-100 | -100.0% | 6 | $-75 | -100.0% |
| $40k+ and field of 8+ | 14 | $-150 | -100.0% | 10 | $-100 | -100.0% |
| 3+ earlier races, 40%+ won from first third | 5 | $-75 | -100.0% | 5 | $-75 | -100.0% |
| 3+ earlier races, under 25% won from first third | 3 | $-50 | -100.0% | 1 | $-25 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% |

## Races checked without a bet, by reason

- ok: 23
- first starter, light-history or no-Proj runner: 20
