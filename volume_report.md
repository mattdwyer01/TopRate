# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 213; bets still open 4.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 86 | 178 | 17 | $2150 | $2167 | $17 | 0.8% | 1.1% |
| Volume v2 | 69 | 125 | 12 | $1725 | $1937 | $212 | 12.3% | 14.4% |
| Volume v3 (P cut) | 49 | 73 | 8 | $1225 | $1209 | $-16 | -1.3% | -10.0% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 178 | $17 | 0.8% | 125 | $212 | 12.3% | 73 | $-16 | -1.3% |
| Meeting minimum prize $30k+ | 111 | $350 | 25.5% | 79 | $527 | 49.0% | 55 | $204 | 22.0% |
| Meeting minimum prize $40k+ | 97 | $550 | 46.9% | 71 | $677 | 73.2% | 45 | $379 | 50.5% |
| Meeting minimum prize $50k+ | 65 | $857 | 114.2% | 49 | $739 | 128.6% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 145 | $113 | 6.5% | 97 | $389 | 28.8% | 66 | $54 | 5.0% |
| $30k+ and good/firm | 96 | $525 | 43.8% | 65 | $702 | 78.0% | 51 | $279 | 32.8% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 154 | $315 | 17.3% | 114 | $412 | 27.0% | 65 | $104 | 10.1% |
| Field of 5 to 7 | 24 | $-298 | -91.8% | 11 | $-200 | -100.0% | 8 | $-120 | -60.0% |
| $40k+ and field of 8+ | 90 | $625 | 56.9% | 68 | $702 | 78.0% | 43 | $429 | 61.3% |
| P(first third) 0.7+ | 45 | $-82 | -15.4% | 30 | $-92 | -22.0% | 45 | $-57 | -7.2% |
| P(first third) 0.5 to 0.7 | 51 | $480 | 69.3% | 33 | $510 | 94.6% | 28 | $40 | 9.2% |
| P(first third) under 0.5 | 36 | $-78 | -20.9% | 24 | $20 | 6.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 115
- first starter, light-history or no-Proj runner: 65
- bush meeting: 33
