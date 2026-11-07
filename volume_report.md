# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 195; bets still open 19.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 67 | 141 | 10 | $1675 | $1005 | $-670 | -40.0% | -36.0% |
| Volume v2 | 54 | 101 | 8 | $1350 | $907 | $-442 | -32.8% | -27.8% |
| Volume v3 (P cut) | 33 | 53 | 4 | $825 | $591 | $-234 | -28.3% | -28.3% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 56 | $83 | 43 | $110 | 27 | $166 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 141 | $-670 | -40.0% | 101 | $-442 | -32.8% | 53 | $-234 | -28.3% |
| Meeting minimum prize $30k+ | 87 | $-380 | -36.2% | 62 | $-252 | -30.6% | 42 | $-59 | -9.0% |
| Meeting minimum prize $40k+ | 73 | $-180 | -21.2% | 54 | $-102 | -15.2% | 32 | $116 | 24.5% |
| Meeting minimum prize $50k+ | 53 | $20 | 3.3% | 39 | $-28 | -6.1% | 20 | $266 | 81.9% |
| Good or firm going (1 to 4) | 113 | $-542 | -40.2% | 75 | $-315 | -30.7% | 48 | $-134 | -18.4% |
| $30k+ and good/firm | 72 | $-205 | -23.4% | 48 | $-78 | -11.9% | 38 | $16 | 2.8% |
| $40k+ and good/firm | 64 | $-105 | -13.5% | 45 | $-28 | -4.6% | 32 | $116 | 24.5% |
| Field of 8 or more | 125 | $-445 | -30.7% | 92 | $-292 | -24.4% | 49 | $-134 | -18.4% |
| Field of 5 to 7 | 16 | $-225 | -100.0% | 9 | $-150 | -100.0% | 4 | $-100 | -100.0% |
| $40k+ and field of 8+ | 70 | $-155 | -18.8% | 51 | $-78 | -11.9% | 32 | $116 | 24.5% |
| P(first third) 0.7+ | 35 | $-13 | -3.2% | 22 | $-102 | -35.3% | 35 | $6 | 1.0% |
| P(first third) 0.5 to 0.7 | 35 | $-220 | -48.1% | 24 | $-110 | -31.7% | 18 | $-240 | -100.0% |
| P(first third) under 0.5 | 25 | $-134 | -49.8% | 17 | $-2 | -1.0% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 47 | $-287 | -52.3% | 41 | $-162 | -30.9% | 20 | $-75 | -23.1% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 102
- first starter, light-history or no-Proj runner: 61
- bush meeting: 32
