# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-05; races checked 47; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 16 | 33 | 1 | $400 | $110 | $-290 | -72.5% | -71.2% |
| Volume v2 | 13 | 25 | 1 | $325 | $110 | $-215 | -66.2% | -64.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit |
|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 |
| 2026-11-05 | 28 | $-325 | 20 | $-250 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI |
|---|---|---|---|---|---|---|
| All bets | 33 | $-290 | -72.5% | 25 | $-215 | -66.2% |
| Meeting minimum prize $30k+ | 20 | $-200 | -100.0% | 15 | $-150 | -100.0% |
| Meeting minimum prize $40k+ | 20 | $-200 | -100.0% | 15 | $-150 | -100.0% |
| Meeting minimum prize $50k+ | 16 | $-150 | -100.0% | 11 | $-100 | -100.0% |
| Good or firm going (1 to 4) | 20 | $-275 | -100.0% | 12 | $-200 | -100.0% |
| $30k+ and good/firm | 11 | $-125 | -100.0% | 6 | $-75 | -100.0% |
| $40k+ and good/firm | 11 | $-125 | -100.0% | 6 | $-75 | -100.0% |
| Field of 8 or more | 24 | $-190 | -63.3% | 19 | $-140 | -56.0% |
| Field of 5 to 7 | 9 | $-100 | -100.0% | 6 | $-75 | -100.0% |
| $40k+ and field of 8+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% |
| 3+ earlier races, 40%+ won from first third | 5 | $-75 | -100.0% | 5 | $-75 | -100.0% |
| 3+ earlier races, under 25% won from first third | 6 | $-75 | -100.0% | 3 | $-50 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 1 | $-25 | -100.0% | 1 | $-25 | -100.0% |

## Races checked without a bet, by reason

- ok: 27
- first starter, light-history or no-Proj runner: 20
