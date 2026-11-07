# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 162; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 56 | 117 | 7 | $1400 | $730 | $-670 | -47.9% | -43.0% |
| Volume v2 | 44 | 81 | 6 | $1100 | $695 | $-405 | -36.8% | -30.7% |
| Volume v3 (P cut) | 26 | 42 | 2 | $650 | $179 | $-471 | -72.5% | -72.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 32 | $83 | 23 | $147 | 16 | $-71 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 117 | $-670 | -47.9% | 81 | $-405 | -36.8% | 42 | $-471 | -72.5% |
| Meeting minimum prize $30k+ | 69 | $-430 | -52.1% | 48 | $-265 | -42.4% | 31 | $-296 | -62.4% |
| Meeting minimum prize $40k+ | 55 | $-230 | -36.8% | 40 | $-115 | -24.2% | 21 | $-121 | -40.4% |
| Meeting minimum prize $50k+ | 44 | $-80 | -16.8% | 32 | $10 | 2.9% | 15 | $-46 | -20.6% |
| Good or firm going (1 to 4) | 95 | $-592 | -52.7% | 61 | $-328 | -39.7% | 37 | $-371 | -67.5% |
| $30k+ and good/firm | 54 | $-255 | -39.2% | 34 | $-90 | -20.0% | 27 | $-221 | -55.3% |
| $40k+ and good/firm | 46 | $-155 | -28.2% | 31 | $-40 | -10.0% | 21 | $-121 | -40.4% |
| Field of 8 or more | 101 | $-445 | -37.9% | 72 | $-255 | -26.8% | 38 | $-371 | -67.5% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 52 | $-205 | -34.2% | 37 | $-90 | -20.0% | 21 | $-121 | -40.4% |
| P(first third) 0.7+ | 28 | $-157 | -49.5% | 18 | $-113 | -47.4% | 28 | $-294 | -62.2% |
| P(first third) 0.5 to 0.7 | 28 | $-118 | -33.3% | 18 | $-21 | -8.1% | 14 | $-177 | -100.0% |
| P(first third) under 0.5 | 15 | $-92 | -52.1% | 7 | $-44 | -34.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 30 | $-225 | -60.0% | 26 | $-200 | -57.1% | 13 | $-200 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 83
- first starter, light-history or no-Proj runner: 57
- bush meeting: 22
