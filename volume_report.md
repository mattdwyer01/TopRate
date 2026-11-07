# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 196; bets still open 23.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 68 | 142 | 11 | $1700 | $1167 | $-532 | -31.3% | -27.3% |
| Volume v2 | 55 | 102 | 9 | $1375 | $1070 | $-305 | -22.2% | -17.3% |
| Volume v3 (P cut) | 34 | 54 | 5 | $850 | $754 | $-96 | -11.3% | -11.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 57 | $220 | 44 | $247 | 28 | $304 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 142 | $-532 | -31.3% | 102 | $-305 | -22.2% | 54 | $-96 | -11.3% |
| Meeting minimum prize $30k+ | 88 | $-242 | -22.6% | 63 | $-115 | -13.5% | 43 | $79 | 11.7% |
| Meeting minimum prize $40k+ | 74 | $-42 | -4.9% | 55 | $35 | 5.0% | 33 | $254 | 50.8% |
| Meeting minimum prize $50k+ | 54 | $158 | 25.2% | 40 | $110 | 23.2% | 21 | $404 | 115.4% |
| Good or firm going (1 to 4) | 114 | $-405 | -29.5% | 76 | $-177 | -16.9% | 49 | $4 | 0.5% |
| $30k+ and good/firm | 73 | $-67 | -7.5% | 49 | $60 | 8.9% | 39 | $154 | 25.6% |
| $40k+ and good/firm | 65 | $33 | 4.1% | 46 | $110 | 17.6% | 33 | $254 | 50.8% |
| Field of 8 or more | 126 | $-307 | -20.8% | 93 | $-155 | -12.7% | 50 | $4 | 0.5% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 71 | $-17 | -2.1% | 52 | $60 | 8.9% | 33 | $254 | 50.8% |
| P(first third) 0.7+ | 35 | $-13 | -3.2% | 22 | $-102 | -35.3% | 35 | $6 | 1.0% |
| P(first third) 0.5 to 0.7 | 36 | $-83 | -17.2% | 25 | $27 | 7.3% | 19 | $-102 | -38.6% |
| P(first third) under 0.5 | 25 | $-134 | -49.8% | 17 | $-2 | -1.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 48 | $-150 | -26.1% | 42 | $-25 | -4.5% | 21 | $63 | 17.9% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 103
- first starter, light-history or no-Proj runner: 61
- bush meeting: 32
