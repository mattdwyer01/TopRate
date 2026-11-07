# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 154; bets still open 14.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 54 | 112 | 7 | $1350 | $730 | $-620 | -45.9% | -40.9% |
| Volume v2 | 43 | 77 | 6 | $1075 | $695 | $-380 | -35.3% | -29.1% |
| Volume v3 (P cut) | 25 | 39 | 2 | $625 | $179 | $-446 | -71.4% | -71.4% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 27 | $133 | 19 | $172 | 13 | $-46 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 112 | $-620 | -45.9% | 77 | $-380 | -35.3% | 39 | $-446 | -71.4% |
| Meeting minimum prize $30k+ | 65 | $-405 | -50.6% | 44 | $-240 | -40.0% | 28 | $-271 | -60.3% |
| Meeting minimum prize $40k+ | 51 | $-205 | -34.2% | 36 | $-90 | -20.0% | 18 | $-96 | -35.0% |
| Meeting minimum prize $50k+ | 40 | $-55 | -12.2% | 28 | $35 | 10.8% | 12 | $-21 | -10.6% |
| Good or firm going (1 to 4) | 90 | $-542 | -50.5% | 57 | $-302 | -37.8% | 34 | $-346 | -66.0% |
| $30k+ and good/firm | 50 | $-230 | -36.8% | 30 | $-65 | -15.3% | 24 | $-196 | -52.3% |
| $40k+ and good/firm | 42 | $-130 | -24.8% | 27 | $-15 | -4.0% | 18 | $-96 | -35.0% |
| Field of 8 or more | 97 | $-420 | -36.5% | 68 | $-230 | -24.9% | 35 | $-346 | -66.0% |
| Field of 5 to 7 | 15 | $-200 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 48 | $-180 | -31.3% | 33 | $-65 | -15.3% | 18 | $-96 | -35.0% |
| P(first third) 0.7+ | 26 | $-144 | -47.4% | 16 | $-100 | -44.5% | 26 | $-278 | -60.8% |
| P(first third) 0.5 to 0.7 | 25 | $-81 | -25.4% | 16 | $-8 | -3.4% | 13 | $-169 | -100.0% |
| P(first third) under 0.5 | 15 | $-92 | -52.1% | 7 | $-44 | -34.2% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 30 | $-225 | -60.0% | 26 | $-200 | -57.1% | 13 | $-200 | -100.0% |
| 3+ earlier races, under 25% won from first third | 29 | $-275 | -100.0% | 13 | $-175 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 80
- first starter, light-history or no-Proj runner: 55
- bush meeting: 19
