# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 235; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 94 | 197 | 19 | $2350 | $2281 | $-69 | -2.9% | -2.7% |
| Volume v2 | 74 | 133 | 13 | $1850 | $2020 | $170 | 9.2% | 11.2% |
| Volume v3 (P cut) | 56 | 85 | 10 | $1400 | $1323 | $-77 | -5.5% | -13.1% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 19 | $-86 | 8 | $-42 | 12 | $-61 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 197 | $-69 | -2.9% | 133 | $170 | 9.2% | 85 | $-77 | -5.5% |
| Meeting minimum prize $30k+ | 122 | $281 | 19.1% | 82 | $477 | 42.4% | 62 | $135 | 13.1% |
| Meeting minimum prize $40k+ | 103 | $531 | 43.4% | 72 | $652 | 68.6% | 50 | $360 | 45.0% |
| Meeting minimum prize $50k+ | 71 | $838 | 104.7% | 50 | $714 | 119.0% | 32 | $522 | 104.4% |
| Good or firm going (1 to 4) | 155 | $71 | 3.8% | 104 | $372 | 25.7% | 72 | $37 | 3.2% |
| $30k+ and good/firm | 98 | $500 | 40.9% | 67 | $677 | 73.2% | 52 | $254 | 29.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 167 | $221 | 11.4% | 116 | $362 | 23.0% | 72 | $35 | 3.1% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 96 | $606 | 52.7% | 69 | $677 | 73.2% | 48 | $410 | 54.6% |
| P(first third) 0.7+ | 54 | $-64 | -10.1% | 35 | $-88 | -17.7% | 54 | $-76 | -8.3% |
| P(first third) 0.5 to 0.7 | 57 | $417 | 55.3% | 35 | $477 | 83.3% | 31 | $-1 | -0.3% |
| P(first third) under 0.5 | 40 | $-119 | -28.8% | 25 | $8 | 2.6% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 32 | $-325 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 130
- first starter, light-history or no-Proj runner: 72
- bush meeting: 33
