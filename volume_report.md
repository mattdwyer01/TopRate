# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-08; races checked 221; bets still open 7.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 88 | 182 | 17 | $2200 | $2167 | $-33 | -1.5% | -1.2% |
| Volume v2 | 70 | 126 | 12 | $1750 | $1937 | $187 | 10.7% | 12.8% |
| Volume v3 (P cut) | 51 | 75 | 8 | $1275 | $1209 | $-66 | -5.2% | -13.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 93 | $770 | 67 | $764 | 47 | $384 |
| 2026-11-08 | 4 | $-50 | 1 | $-25 | 2 | $-50 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 182 | $-33 | -1.5% | 126 | $187 | 10.7% | 75 | $-66 | -5.2% |
| Meeting minimum prize $30k+ | 114 | $325 | 23.3% | 79 | $527 | 49.0% | 56 | $179 | 18.8% |
| Meeting minimum prize $40k+ | 97 | $550 | 46.9% | 71 | $677 | 73.2% | 45 | $379 | 50.5% |
| Meeting minimum prize $50k+ | 65 | $857 | 114.2% | 49 | $739 | 128.6% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 146 | $88 | 5.0% | 98 | $364 | 26.5% | 67 | $29 | 2.6% |
| $30k+ and good/firm | 96 | $525 | 43.8% | 65 | $702 | 78.0% | 51 | $279 | 32.8% |
| $40k+ and good/firm | 88 | $625 | 56.9% | 62 | $752 | 88.4% | 45 | $379 | 50.5% |
| Field of 8 or more | 157 | $290 | 15.7% | 114 | $412 | 27.0% | 66 | $79 | 7.5% |
| Field of 5 to 7 | 25 | $-323 | -92.4% | 12 | $-225 | -100.0% | 9 | $-145 | -64.4% |
| $40k+ and field of 8+ | 90 | $625 | 56.9% | 68 | $702 | 78.0% | 43 | $429 | 61.3% |
| P(first third) 0.7+ | 47 | $-116 | -20.3% | 31 | $-117 | -26.4% | 47 | $-107 | -12.8% |
| P(first third) 0.5 to 0.7 | 52 | $471 | 67.3% | 33 | $510 | 94.6% | 28 | $40 | 9.2% |
| P(first third) under 0.5 | 37 | $-86 | -22.6% | 24 | $20 | 6.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 67 | $-252 | -30.6% | 53 | $17 | 2.3% | 32 | $-25 | -4.3% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 119
- first starter, light-history or no-Proj runner: 69
- bush meeting: 33
