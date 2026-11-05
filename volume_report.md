# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-05; races checked 49; bets still open 7.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 19 | 38 | 1 | $475 | $110 | $-365 | -76.8% | -75.8% |
| Volume v2 | 16 | 30 | 1 | $400 | $110 | $-290 | -72.5% | -71.2% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit |
|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 |
| 2026-11-05 | 33 | $-400 | 25 | $-325 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |
|---|---|---|---|---|---|---|
| All bets | 38 | $-365 | -76.8% | 30 | $-290 | -72.5% |
| Meeting minimum prize $30k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% |
| Meeting minimum prize $40k+ | 21 | $-225 | -100.0% | 16 | $-175 | -100.0% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% |
| Good or firm going (1 to 4) | 25 | $-350 | -100.0% | 17 | $-275 | -100.0% |
| $30k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% |
| $40k+ and good/firm | 12 | $-150 | -100.0% | 7 | $-100 | -100.0% |
| Field of 8 or more | 29 | $-265 | -70.7% | 24 | $-215 | -66.2% |
| Field of 5 to 7 | 9 | $-100 | -100.0% | 6 | $-75 | -100.0% |
| $40k+ and field of 8+ | 18 | $-200 | -100.0% | 13 | $-150 | -100.0% |
| 3+ earlier races, 40%+ won from first third | 7 | $-100 | -100.0% | 7 | $-100 | -100.0% |
| 3+ earlier races, under 25% won from first third | 7 | $-100 | -100.0% | 4 | $-75 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% |

## Races checked without a bet, by reason

- ok: 28
- first starter, light-history or no-Proj runner: 21
