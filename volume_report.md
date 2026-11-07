# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 172; bets still open 9.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 61 | 125 | 7 | $1525 | $730 | $-795 | -52.1% | -47.7% |
| Volume v2 | 49 | 89 | 6 | $1225 | $695 | $-530 | -43.3% | -37.8% |
| Volume v3 (P cut) | 28 | 44 | 2 | $700 | $179 | $-521 | -74.5% | -74.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 40 | $-42 | 31 | $22 | 18 | $-121 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 125 | $-795 | -52.1% | 89 | $-530 | -43.3% | 44 | $-521 | -74.5% |
| Meeting minimum prize $30k+ | 73 | $-530 | -57.3% | 52 | $-365 | -50.3% | 33 | $-346 | -66.0% |
| Meeting minimum prize $40k+ | 59 | $-330 | -45.5% | 44 | $-215 | -37.4% | 23 | $-171 | -48.9% |
| Meeting minimum prize $50k+ | 47 | $-155 | -28.2% | 35 | $-65 | -15.3% | 17 | $-96 | -35.0% |
| Good or firm going (1 to 4) | 99 | $-692 | -56.5% | 65 | $-428 | -46.2% | 39 | $-421 | -70.2% |
| $30k+ and good/firm | 58 | $-355 | -47.3% | 38 | $-190 | -34.6% | 29 | $-271 | -60.3% |
| $40k+ and good/firm | 50 | $-255 | -39.2% | 35 | $-140 | -28.0% | 23 | $-171 | -48.9% |
| Field of 8 or more | 109 | $-570 | -43.8% | 80 | $-380 | -35.3% | 40 | $-421 | -70.2% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 56 | $-305 | -43.6% | 41 | $-190 | -34.6% | 23 | $-171 | -48.9% |
| P(first third) 0.7+ | 29 | $-182 | -53.2% | 19 | $-138 | -52.4% | 29 | $-319 | -64.1% |
| P(first third) 0.5 to 0.7 | 31 | $-175 | -42.4% | 21 | $-77 | -24.5% | 15 | $-202 | -100.0% |
| P(first third) under 0.5 | 19 | $-136 | -61.6% | 11 | $-88 | -50.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 36 | $-300 | -66.7% | 32 | $-275 | -64.7% | 15 | $-250 | -100.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 88
- first starter, light-history or no-Proj runner: 59
- bush meeting: 25
