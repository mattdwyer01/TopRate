# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 200; bets still open 20.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 71 | 149 | 11 | $1775 | $1167 | $-607 | -34.2% | -30.4% |
| Volume v2 | 58 | 107 | 9 | $1450 | $1070 | $-380 | -26.2% | -21.6% |
| Volume v3 (P cut) | 37 | 58 | 5 | $925 | $754 | $-171 | -18.5% | -18.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 64 | $145 | 49 | $172 | 32 | $229 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 149 | $-607 | -34.2% | 107 | $-380 | -26.2% | 58 | $-171 | -18.5% |
| Meeting minimum prize $30k+ | 92 | $-292 | -26.0% | 67 | $-165 | -18.3% | 45 | $29 | 4.0% |
| Meeting minimum prize $40k+ | 78 | $-92 | -10.0% | 59 | $-15 | -2.0% | 35 | $204 | 37.1% |
| Meeting minimum prize $50k+ | 55 | $133 | 20.4% | 41 | $85 | 17.0% | 22 | $379 | 101.0% |
| Good or firm going (1 to 4) | 121 | $-480 | -33.1% | 81 | $-252 | -22.4% | 53 | $-71 | -8.6% |
| $30k+ and good/firm | 77 | $-117 | -12.4% | 53 | $10 | 1.4% | 41 | $104 | 16.0% |
| $40k+ and good/firm | 69 | $-17 | -2.1% | 50 | $60 | 8.9% | 35 | $204 | 37.1% |
| Field of 8 or more | 133 | $-382 | -24.7% | 98 | $-230 | -17.7% | 54 | $-71 | -8.6% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 75 | $-67 | -7.5% | 56 | $10 | 1.4% | 35 | $204 | 37.1% |
| P(first third) 0.7+ | 37 | $-30 | -7.1% | 23 | $-110 | -37.1% | 37 | $-32 | -5.1% |
| P(first third) 0.5 to 0.7 | 39 | $-125 | -23.7% | 27 | $-23 | -5.4% | 21 | $-140 | -46.2% |
| P(first third) under 0.5 | 27 | $-151 | -52.8% | 19 | $-19 | -7.5% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 54 | $-200 | -32.0% | 46 | $-75 | -12.5% | 24 | $13 | 3.1% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 107
- first starter, light-history or no-Proj runner: 61
- bush meeting: 32
