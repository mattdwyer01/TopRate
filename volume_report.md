# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 238; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 95 | 200 | 19 | $2375 | $2281 | $-94 | -3.9% | -3.7% |
| Volume v2 | 75 | 135 | 13 | $1875 | $2020 | $145 | 7.7% | 9.7% |
| Volume v3 (P cut) | 57 | 88 | 10 | $1425 | $1323 | $-102 | -7.2% | -14.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 22 | $-111 | 10 | $-67 | 15 | $-86 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 200 | $-94 | -3.9% | 135 | $145 | 7.7% | 88 | $-102 | -7.2% |
| Meeting minimum prize $30k+ | 122 | $281 | 19.1% | 82 | $477 | 42.4% | 62 | $135 | 13.1% |
| Meeting minimum prize $40k+ | 103 | $531 | 43.4% | 72 | $652 | 68.6% | 50 | $360 | 45.0% |
| Meeting minimum prize $50k+ | 71 | $838 | 104.7% | 50 | $714 | 119.0% | 32 | $522 | 104.4% |
| Good or firm going (1 to 4) | 158 | $46 | 2.4% | 106 | $347 | 23.6% | 75 | $12 | 1.0% |
| $30k+ and good/firm | 98 | $500 | 40.9% | 67 | $677 | 73.2% | 52 | $254 | 29.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 170 | $196 | 9.9% | 118 | $337 | 21.0% | 75 | $10 | 0.8% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 96 | $606 | 52.7% | 69 | $677 | 73.2% | 48 | $410 | 54.6% |
| P(first third) 0.7+ | 56 | $-81 | -12.5% | 37 | $-113 | -21.6% | 56 | $-93 | -9.9% |
| P(first third) 0.5 to 0.7 | 58 | $409 | 53.6% | 35 | $477 | 83.3% | 32 | $-10 | -2.0% |
| P(first third) under 0.5 | 40 | $-119 | -28.8% | 25 | $8 | 2.6% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 32 | $-325 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 131
- first starter, light-history or no-Proj runner: 74
- bush meeting: 33
