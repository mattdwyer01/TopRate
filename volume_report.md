# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 233; bets still open 12.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 93 | 194 | 19 | $2325 | $2281 | $-44 | -1.9% | -1.6% |
| Volume v2 | 73 | 132 | 13 | $1825 | $2020 | $195 | 10.7% | 12.7% |
| Volume v3 (P cut) | 55 | 83 | 10 | $1375 | $1323 | $-52 | -3.8% | -11.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 16 | $-61 | 7 | $-17 | 10 | $-36 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 194 | $-44 | -1.9% | 132 | $195 | 10.7% | 83 | $-52 | -3.8% |
| Meeting minimum prize $30k+ | 119 | $306 | 21.1% | 81 | $502 | 45.6% | 60 | $160 | 16.0% |
| Meeting minimum prize $40k+ | 100 | $556 | 46.4% | 71 | $677 | 73.2% | 48 | $385 | 49.6% |
| Meeting minimum prize $50k+ | 68 | $863 | 111.3% | 49 | $739 | 128.6% | 30 | $547 | 115.2% |
| Good or firm going (1 to 4) | 155 | $71 | 3.8% | 104 | $372 | 25.7% | 72 | $37 | 3.2% |
| $30k+ and good/firm | 98 | $500 | 40.9% | 67 | $677 | 73.2% | 52 | $254 | 29.0% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 164 | $246 | 12.8% | 115 | $387 | 24.9% | 70 | $60 | 5.4% |
| Field of 5 to 7 | 30 | $-290 | -72.5% | 17 | $-192 | -69.7% | 13 | $-112 | -40.6% |
| $40k+ and field of 8+ | 93 | $631 | 56.1% | 68 | $702 | 78.0% | 46 | $435 | 59.9% |
| P(first third) 0.7+ | 52 | $-47 | -7.7% | 34 | $-63 | -13.3% | 52 | $-51 | -5.7% |
| P(first third) 0.5 to 0.7 | 57 | $417 | 55.3% | 35 | $477 | 83.3% | 31 | $-1 | -0.3% |
| P(first third) under 0.5 | 39 | $-111 | -27.4% | 25 | $8 | 2.6% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 32 | $-325 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 128
- first starter, light-history or no-Proj runner: 72
- bush meeting: 33
