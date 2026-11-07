# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 191; bets still open 19.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 65 | 135 | 9 | $1625 | $942 | $-682 | -42.0% | -37.8% |
| Volume v2 | 52 | 95 | 7 | $1300 | $845 | $-455 | -35.0% | -29.8% |
| Volume v3 (P cut) | 32 | 52 | 3 | $800 | $341 | $-459 | -57.3% | -57.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 50 | $70 | 37 | $97 | 26 | $-59 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 135 | $-682 | -42.0% | 95 | $-455 | -35.0% | 52 | $-459 | -57.3% |
| Meeting minimum prize $30k+ | 83 | $-417 | -40.7% | 58 | $-290 | -36.3% | 41 | $-284 | -45.4% |
| Meeting minimum prize $40k+ | 69 | $-217 | -26.4% | 50 | $-140 | -21.5% | 31 | $-109 | -24.2% |
| Meeting minimum prize $50k+ | 49 | $-17 | -3.0% | 35 | $-65 | -15.3% | 19 | $41 | 13.8% |
| Good or firm going (1 to 4) | 109 | $-580 | -43.8% | 71 | $-352 | -35.3% | 47 | $-359 | -51.2% |
| $30k+ and good/firm | 68 | $-242 | -28.5% | 44 | $-115 | -18.4% | 37 | $-209 | -38.0% |
| $40k+ and good/firm | 60 | $-142 | -19.0% | 41 | $-65 | -11.3% | 31 | $-109 | -24.2% |
| Field of 8 or more | 119 | $-457 | -32.7% | 86 | $-305 | -26.5% | 48 | $-359 | -51.2% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 66 | $-192 | -24.1% | 47 | $-115 | -18.4% | 31 | $-109 | -24.2% |
| P(first third) 0.7+ | 34 | $-69 | -17.7% | 21 | $-158 | -55.9% | 34 | $-219 | -39.1% |
| P(first third) 0.5 to 0.7 | 34 | $-208 | -46.7% | 23 | $-98 | -29.2% | 18 | $-240 | -100.0% |
| P(first third) under 0.5 | 21 | $-103 | -43.3% | 13 | $29 | 13.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 41 | $-300 | -60.0% | 35 | $-175 | -36.8% | 19 | $-300 | -100.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 99
- first starter, light-history or no-Proj runner: 61
- bush meeting: 31
