# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 204; bets still open 17.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 74 | 155 | 13 | $1850 | $1315 | $-534 | -28.9% | -25.2% |
| Volume v2 | 60 | 111 | 11 | $1500 | $1287 | $-213 | -14.2% | -9.7% |
| Volume v3 (P cut) | 40 | 62 | 6 | $1000 | $891 | $-109 | -10.9% | -10.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 70 | $218 | 53 | $339 | 36 | $291 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 155 | $-534 | -28.9% | 111 | $-213 | -14.2% | 62 | $-109 | -10.9% |
| Meeting minimum prize $30k+ | 98 | $-220 | -18.3% | 71 | $2 | 0.2% | 49 | $91 | 11.4% |
| Meeting minimum prize $40k+ | 84 | $-20 | -2.0% | 63 | $152 | 19.0% | 39 | $266 | 42.6% |
| Meeting minimum prize $50k+ | 59 | $162 | 23.1% | 44 | $139 | 26.5% | 25 | $329 | 77.4% |
| Good or firm going (1 to 4) | 127 | $-407 | -26.7% | 85 | $-86 | -7.3% | 57 | $-9 | -1.0% |
| $30k+ and good/firm | 83 | $-45 | -4.3% | 57 | $177 | 22.8% | 45 | $166 | 22.9% |
| $40k+ and good/firm | 75 | $55 | 6.0% | 54 | $227 | 31.3% | 39 | $266 | 42.6% |
| Field of 8 or more | 138 | $-285 | -17.8% | 102 | $-63 | -4.7% | 57 | $16 | 1.9% |
| Field of 5 to 7 | 17 | $-250 | -100.0% | 9 | $-150 | -100.0% | 5 | $-125 | -100.0% |
| $40k+ and field of 8+ | 80 | $30 | 3.2% | 60 | $177 | 22.8% | 38 | $291 | 48.5% |
| P(first third) 0.7+ | 39 | $2 | 0.4% | 24 | $2 | 0.6% | 39 | $56 | 8.3% |
| P(first third) 0.5 to 0.7 | 42 | $-154 | -27.8% | 29 | $-40 | -9.0% | 23 | $-165 | -50.3% |
| P(first third) under 0.5 | 28 | $-80 | -27.2% | 20 | $52 | 19.7% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 60 | $-127 | -18.2% | 50 | $92 | 14.1% | 28 | $75 | 15.8% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 109
- first starter, light-history or no-Proj runner: 62
- bush meeting: 33
