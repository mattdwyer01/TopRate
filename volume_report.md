# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 170; bets still open 10.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 60 | 124 | 7 | $1500 | $730 | $-770 | -51.3% | -46.8% |
| Volume v2 | 48 | 88 | 6 | $1200 | $695 | $-505 | -42.1% | -36.5% |
| Volume v3 (P cut) | 28 | 44 | 2 | $700 | $179 | $-521 | -74.5% | -74.5% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 39 | $-17 | 30 | $47 | 18 | $-121 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 124 | $-770 | -51.3% | 88 | $-505 | -42.1% | 44 | $-521 | -74.5% |
| Meeting minimum prize $30k+ | 72 | $-505 | -56.1% | 51 | $-340 | -48.6% | 33 | $-346 | -66.0% |
| Meeting minimum prize $40k+ | 58 | $-305 | -43.6% | 43 | $-190 | -34.5% | 23 | $-171 | -48.9% |
| Meeting minimum prize $50k+ | 46 | $-130 | -24.8% | 34 | $-40 | -10.0% | 17 | $-96 | -35.0% |
| Good or firm going (1 to 4) | 98 | $-667 | -55.6% | 64 | $-402 | -44.7% | 39 | $-421 | -70.2% |
| $30k+ and good/firm | 57 | $-330 | -45.5% | 37 | $-165 | -31.4% | 29 | $-271 | -60.3% |
| $40k+ and good/firm | 49 | $-230 | -36.8% | 34 | $-115 | -24.2% | 23 | $-171 | -48.9% |
| Field of 8 or more | 108 | $-545 | -42.7% | 79 | $-355 | -33.8% | 40 | $-421 | -70.2% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 55 | $-280 | -41.5% | 40 | $-165 | -31.4% | 23 | $-171 | -48.9% |
| P(first third) 0.7+ | 29 | $-182 | -53.2% | 19 | $-138 | -52.4% | 29 | $-319 | -64.1% |
| P(first third) 0.5 to 0.7 | 30 | $-150 | -38.6% | 20 | $-52 | -18.0% | 15 | $-202 | -100.0% |
| P(first third) under 0.5 | 19 | $-136 | -61.6% | 11 | $-88 | -50.8% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 36 | $-300 | -66.7% | 32 | $-275 | -64.7% | 15 | $-250 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 88
- first starter, light-history or no-Proj runner: 58
- bush meeting: 24
