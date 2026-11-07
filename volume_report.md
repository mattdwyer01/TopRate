# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 189; bets still open 22.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 64 | 133 | 8 | $1600 | $780 | $-820 | -51.2% | -47.0% |
| Volume v2 | 52 | 95 | 7 | $1300 | $845 | $-455 | -35.0% | -29.8% |
| Volume v3 (P cut) | 31 | 50 | 2 | $775 | $179 | $-596 | -76.9% | -76.9% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 48 | $-67 | 37 | $97 | 24 | $-196 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 133 | $-820 | -51.2% | 95 | $-455 | -35.0% | 50 | $-596 | -76.9% |
| Meeting minimum prize $30k+ | 81 | $-555 | -55.5% | 58 | $-290 | -36.3% | 39 | $-421 | -70.2% |
| Meeting minimum prize $40k+ | 67 | $-355 | -44.4% | 50 | $-140 | -21.5% | 29 | $-246 | -57.9% |
| Meeting minimum prize $50k+ | 47 | $-155 | -28.2% | 35 | $-65 | -15.3% | 17 | $-96 | -35.0% |
| Good or firm going (1 to 4) | 107 | $-717 | -55.2% | 71 | $-352 | -35.3% | 45 | $-496 | -73.5% |
| $30k+ and good/firm | 66 | $-380 | -46.1% | 44 | $-115 | -18.4% | 35 | $-346 | -66.0% |
| $40k+ and good/firm | 58 | $-280 | -38.6% | 41 | $-65 | -11.3% | 29 | $-246 | -57.9% |
| Field of 8 or more | 117 | $-595 | -43.3% | 86 | $-305 | -26.5% | 46 | $-496 | -73.5% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 64 | $-330 | -42.6% | 47 | $-115 | -18.4% | 29 | $-246 | -57.9% |
| P(first third) 0.7+ | 33 | $-219 | -57.8% | 21 | $-158 | -55.9% | 33 | $-369 | -67.4% |
| P(first third) 0.5 to 0.7 | 33 | $-195 | -45.1% | 23 | $-98 | -29.2% | 17 | $-227 | -100.0% |
| P(first third) under 0.5 | 21 | $-103 | -43.3% | 13 | $29 | 13.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 41 | $-300 | -60.0% | 35 | $-175 | -36.8% | 19 | $-300 | -100.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 99
- first starter, light-history or no-Proj runner: 60
- bush meeting: 30
