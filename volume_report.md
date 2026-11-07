# Volume rules tracker

Bets are frozen up to 40 minutes before the jump at the fixed price then; results are filled in after the race. $25 a race per rule, split equally. See `volume_rules.py` for the rule definitions.

Logged 2026-11-04 to 2026-11-07; races checked 206; bets still open 7.

| Rule | Races | Bets | Wins | Staked | Returned | Profit | ROI at logged price | ROI at starting price |
|---|---|---|---|---|---|---|---|---|
| Volume v1 | 79 | 167 | 15 | $1975 | $2060 | $86 | 4.3% | 7.7% |
| Volume v2 | 65 | 121 | 12 | $1625 | $1937 | $312 | 19.2% | 23.3% |
| Volume v3 (P cut) | 44 | 68 | 7 | $1100 | $1129 | $29 | 2.6% | 2.6% |

## By day (at logged price)

| Date | v1 bets | v1 profit | v2 bets | v2 profit | v3 bets | v3 profit |
|---|---|---|---|---|---|---|
| 2026-11-04 | 5 | $35 | 5 | $35 | 0 | $0 |
| 2026-11-05 | 41 | $-337 | 33 | $-262 | 0 | $0 |
| 2026-11-06 | 39 | $-450 | 20 | $-325 | 26 | $-400 |
| 2026-11-07 | 82 | $838 | 63 | $864 | 42 | $429 |

## Segments (at logged price; stake is the full $25 a race rule stake, so segments are cuts of the same bets)

| Segment | v1 bets | v1 profit | v1 ROI | v2 bets | v2 profit | v2 ROI | v3 bets | v3 profit | v3 ROI |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 167 | $86 | 4.3% | 121 | $312 | 19.2% | 68 | $29 | 2.6% |
| Meeting minimum prize $30k+ | 105 | $450 | 35.3% | 77 | $577 | 56.3% | 52 | $279 | 32.8% |
| Meeting minimum prize $40k+ | 91 | $650 | 60.5% | 69 | $727 | 83.1% | 42 | $454 | 67.2% |
| Meeting minimum prize $50k+ | 65 | $857 | 114.2% | 49 | $739 | 128.6% | 27 | $541 | 120.3% |
| Good or firm going (1 to 4) | 139 | $213 | 12.9% | 95 | $439 | 33.8% | 63 | $129 | 12.9% |
| $30k+ and good/firm | 90 | $625 | 56.9% | 63 | $752 | 88.4% | 48 | $354 | 45.6% |
| $40k+ and good/firm | 82 | $725 | 72.6% | 60 | $802 | 100.2% | 42 | $454 | 67.2% |
| Field of 8 or more | 150 | $335 | 19.5% | 112 | $462 | 31.3% | 63 | $154 | 15.8% |
| Field of 5 to 7 | 17 | $-250 | -100.0% | 9 | $-150 | -100.0% | 5 | $-125 | -100.0% |
| $40k+ and field of 8+ | 87 | $700 | 68.3% | 66 | $752 | 88.4% | 41 | $479 | 73.7% |
| P(first third) 0.7+ | 43 | $-32 | -6.7% | 28 | $-42 | -11.4% | 43 | $-7 | -0.9% |
| P(first third) 0.5 to 0.7 | 45 | $536 | 88.1% | 31 | $560 | 114.5% | 25 | $35 | 9.7% |
| P(first third) under 0.5 | 33 | $-116 | -35.1% | 24 | $20 | 6.9% | 0 | $0 | None% |
| 3+ earlier races, 40%+ won from first third | 61 | $-152 | -21.0% | 51 | $67 | 9.9% | 29 | $50 | 10.0% |
| 3+ earlier races, under 25% won from first third | 30 | $-300 | -100.0% | 14 | $-200 | -100.0% | 11 | $-150 | -100.0% |
| 3+ earlier races, winners forecast at the back (mean 0.55+) | 20 | $-175 | -100.0% | 7 | $-100 | -100.0% | 11 | $-150 | -100.0% |

## Races checked without a bet, by reason

- ok: 111
- first starter, light-history or no-Proj runner: 62
- bush meeting: 33
