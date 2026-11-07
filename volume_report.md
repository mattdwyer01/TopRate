# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 104; bets still open 8.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 40 | 85 | 2 | $1000 | $248 | $-752 | -75.2% | -68.5% |
| Volume v2 | 32 | 58 | 2 | $800 | $248 | $-552 | -69.1% | -60.6% |
| Volume v3 (P cut) | 16 | 26 | 0 | $400 | $0 | $-400 | -100.0% | -100.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 85 | $-752 | -75.2% | 58 | $-552 | -69.1% | 26 | $-400 | -100.0% |
| Meeting minimum prize $30k+ | 41 | $-500 | -100.0% | 27 | $-375 | -100.0% | 16 | $-250 | -100.0% |
| Meeting minimum prize $40k+ | 27 | $-300 | -100.0% | 19 | $-225 | -100.0% | 6 | $-75 | -100.0% |
| Meeting minimum prize $50k+ | 17 | $-175 | -100.0% | 12 | $-125 | -100.0% | 0 | $0 | None% |
| Good or firm going (1 to 4) | 66 | $-637 | -82.3% | 40 | $-437 | -76.1% | 22 | $-325 | -100.0% |
| $30k+ and good/firm | 26 | $-325 | -100.0% | 13 | $-200 | -100.0% | 12 | $-175 | -100.0% |
| $40k+ and good/firm | 18 | $-225 | -100.0% | 10 | $-150 | -100.0% | 6 | $-75 | -100.0% |
| Field of 8 or more | 72 | $-577 | -70.0% | 50 | $-427 | -63.3% | 23 | $-325 | -100.0% |
| Field of 5 to 7 | 13 | $-175 | -100.0% | 8 | $-125 | -100.0% | 3 | $-75 | -100.0% |
| $40k+ and field of 8+ | 24 | $-275 | -100.0% | 16 | $-200 | -100.0% | 6 | $-75 | -100.0% |
| P(first third) 0.7+ | 15 | $-185 | -100.0% | 9 | $-154 | -100.0% | 15 | $-262 | -100.0% |
| P(first third) 0.5 to 0.7 | 15 | $-183 | -100.0% | 8 | $-112 | -100.0% | 11 | $-137 | -100.0% |
| P(first third) under 0.5 | 9 | $-82 | -100.0% | 3 | $-58 | -100.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 23 | $-300 | -100.0% | 19 | $-275 | -100.0% | 9 | $-125 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 55
- first starter, light-history or no-Proj runner: 46
- bush meeting: 3
