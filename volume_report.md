# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 202; bets still open 19.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 72 | 150 | 11 | $1800 | $1167 | $-632 | -35.1% | -31.4% |
| Volume v2 | 58 | 107 | 9 | $1450 | $1070 | $-380 | -26.2% | -21.6% |
| Volume v3 (P cut) | 38 | 59 | 5 | $950 | $754 | $-196 | -20.7% | -20.7% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 65 | $120 | 49 | $172 | 33 | $204 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 150 | $-632 | -35.1% | 107 | $-380 | -26.2% | 59 | $-196 | -20.7% |
| Meeting minimum prize $30k+ | 93 | $-317 | -27.6% | 67 | $-165 | -18.3% | 46 | $4 | 0.5% |
| Meeting minimum prize $40k+ | 79 | $-117 | -12.4% | 59 | $-15 | -2.0% | 36 | $179 | 31.1% |
| Meeting minimum prize $50k+ | 56 | $108 | 15.9% | 41 | $85 | 17.0% | 23 | $354 | 88.4% |
| Good or firm going (1 to 4) | 122 | $-505 | -34.2% | 81 | $-252 | -22.4% | 54 | $-96 | -11.3% |
| $30k+ and good/firm | 78 | $-142 | -14.6% | 53 | $10 | 1.4% | 42 | $79 | 11.7% |
| $40k+ and good/firm | 70 | $-42 | -4.9% | 50 | $60 | 8.9% | 36 | $179 | 31.1% |
| Field of 8 or more | 133 | $-382 | -24.7% | 98 | $-230 | -17.7% | 54 | $-71 | -8.6% |
| Field of 5 to 7 | 17 | $-250 | -100.0% | 9 | $-150 | -100.0% | 5 | $-125 | -100.0% |
| $40k+ and field of 8+ | 75 | $-67 | -7.5% | 56 | $10 | 1.4% | 35 | $204 | 37.1% |
| P(first third) 0.7+ | 38 | $-55 | -12.4% | 23 | $-110 | -37.1% | 38 | $-57 | -8.7% |
| P(first third) 0.5 to 0.7 | 39 | $-125 | -23.7% | 27 | $-23 | -5.4% | 21 | $-140 | -46.2% |
| P(first third) under 0.5 | 27 | $-151 | -52.8% | 19 | $-19 | -7.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 55 | $-225 | -34.6% | 46 | $-75 | -12.5% | 25 | $-12 | -2.9% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 108
- first starter, light-history or no-Proj runner: 61
- bush meeting: 33
