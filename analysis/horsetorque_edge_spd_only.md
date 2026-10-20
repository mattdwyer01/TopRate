# Spd-only Horsetorque tests

18,137 races, 168,807 runners, 2025-07 to 8 Oct 2026. Only the Spd rating ranks or selects; every other idea is a filter on Spd picks. ROI is shown at the Top price and at SP (Top is never below SP, so Top is an upper bound).

## Base: Spd rank and price floor

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| Spd #1, any price | 18,137 | 3,718 | 20.5 | 8.61 | -13.2 | 1.8 | -19.1 | -14.2 | -10.1 | -16.2 |
| Spd #2, any price | 18,137 | 2,904 | 16.0 | 10.96 | -13.9 | 2.0 | -20.9 | -15.1 | -12.4 | -15.4 |
| Spd #1, Top >= $3 | 14,438 | 2,152 | 14.9 | 10.24 | -14.1 | 2.2 | -20.5 | -15.4 | -10.0 | -18.2 |
| Spd #1 or #2, Top >= $3 (base for the filters) | 30,469 | 4,208 | 13.8 | 11.22 | -14.3 | 1.6 | -21.2 | -15.0 | -11.5 | -17.1 |
| all runners, Top >= $3 (baseline) | 159,013 | 14,066 | 8.8 | 25.82 | -20.7 | 1.0 | -28.3 | -21.1 | -20.3 | -21.2 |

## Test 5a: price bands and the floor, Spd #1-2

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| Spd #1-2, Top $1.5-2 | 1,265 | 678 | 53.6 | 1.75 | -6.9 | 2.5 | -11.7 | -7.1 | -6.9 | -6.9 |
| Spd #1-2, Top $2-3 | 4,315 | 1,574 | 36.5 | 2.47 | -10.7 | 1.8 | -14.7 | -10.8 | -11.0 | -10.4 |
| Spd #1-2, Top $3-5 | 9,221 | 2,191 | 23.8 | 3.86 | -10.0 | 1.7 | -15.9 | -10.2 | -7.7 | -12.3 |
| Spd #1-2, Top $5-7 | 5,682 | 907 | 16.0 | 5.70 | -9.9 | 2.8 | -16.9 | -10.2 | -10.4 | -9.4 |
| Spd #1-2, Top $7-+ | 15,566 | 1,110 | 7.1 | 17.59 | -18.4 | 2.7 | -25.9 | -19.8 | -14.1 | -22.7 |
| Spd #1-2, floor $2 | 34,784 | 5,782 | 16.6 | 10.13 | -13.8 | 1.4 | -20.4 | -14.5 | -11.4 | -16.3 |
| Spd #1-2, floor $2.5 | 32,750 | 4,984 | 15.2 | 10.63 | -13.9 | 1.5 | -20.6 | -14.6 | -11.3 | -16.5 |
| Spd #1-2, floor $3 | 30,469 | 4,208 | 13.8 | 11.22 | -14.3 | 1.6 | -21.2 | -15.0 | -11.5 | -17.1 |
| Spd #1-2, floor $4 | 25,328 | 2,840 | 11.2 | 12.80 | -15.4 | 1.9 | -22.6 | -16.3 | -12.4 | -18.4 |
| Spd #1-2, floor $5 | 21,248 | 2,017 | 9.5 | 14.41 | -16.1 | 2.1 | -23.5 | -17.2 | -13.1 | -19.2 |

## Test 1: class par as a filter on Spd #1-2 (Top >= $3)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| class drop (> 1.5 par below recent) | 5,437 | 707 | 13.0 | 12.87 | -13.5 | 3.8 | -19.3 | -15.1 | -9.2 | -17.6 |
| same class (+-1.5) | 16,746 | 2,291 | 13.7 | 10.70 | -17.3 | 2.0 | -24.3 | -18.5 | -15.3 | -19.3 |
| class rise (> 1.5 above recent) | 8,286 | 1,210 | 14.6 | 11.18 | -8.7 | 3.3 | -16.2 | -11.0 | -5.3 | -12.2 |
| class_par Maiden | 4,110 | 559 | 13.6 | 11.66 | -18.9 | 4.4 | -26.2 | -23.1 | -15.4 | -22.4 |
| class_par BM/CLS up to 92 | 16,102 | 2,295 | 14.3 | 10.37 | -11.1 | 2.2 | -18.2 | -12.3 | -9.6 | -12.7 |
| class_par BM/CLS 92-96.5 | 6,532 | 868 | 13.3 | 12.13 | -16.4 | 3.4 | -23.7 | -18.6 | -10.5 | -22.3 |
| class_par Open / Black type | 3,725 | 486 | 13.0 | 12.80 | -19.1 | 4.1 | -24.1 | -21.4 | -20.6 | -17.6 |

## Test 2: TOF avoid flag on Spd #1-2 (Top >= $3)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| avoid flag set (TOF<0, rear third, weight or distance up) | 247 | 37 | 15.0 | 11.11 | -7.5 | 16.1 | -12.1 | -24.4 | +18.2 | -33.1 |
| flag not set | 27,838 | 3,834 | 13.8 | 11.35 | -13.9 | 1.7 | -21.0 | -14.7 | -10.7 | -17.0 |
| last-start TOF < 0 (any settle) | 5,234 | 737 | 14.1 | 9.64 | -17.8 | 3.4 | -23.8 | -19.7 | -12.8 | -22.7 |
| last-start TOF >= 0 | 22,851 | 3,134 | 13.7 | 11.74 | -12.9 | 1.9 | -20.3 | -13.9 | -10.2 | -15.6 |

## Test 3: compression gate on Spd #1-2 (points on the displayed Spd scale, 2.15 per length)

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| no gate | 30,469 | 4,208 | 13.8 | 11.22 | -14.3 | 1.6 | -21.2 | -15.0 | -11.5 | -17.1 |
| skip compressed: >= 4 within 3 pts (kept 89%) | 27,154 | 3,842 | 14.1 | 10.94 | -12.7 | 1.7 | -19.7 | -13.5 | -9.5 | -15.8 |
| skip compressed: >= 5 within 3 pts (kept 96%) | 29,389 | 4,096 | 13.9 | 11.09 | -13.6 | 1.6 | -20.6 | -14.3 | -11.0 | -16.2 |
| skip compressed: >= 6 within 3 pts (kept 99%) | 30,122 | 4,170 | 13.8 | 11.17 | -14.0 | 1.6 | -21.0 | -14.8 | -11.1 | -17.0 |
| skip compressed: >= 4 within 4 pts (kept 79%) | 24,202 | 3,485 | 14.4 | 10.74 | -12.3 | 1.7 | -19.4 | -13.2 | -9.4 | -15.2 |
| skip compressed: >= 5 within 4 pts (kept 91%) | 27,774 | 3,929 | 14.1 | 10.94 | -13.1 | 1.6 | -20.1 | -13.9 | -10.2 | -16.0 |
| skip compressed: >= 6 within 4 pts (kept 97%) | 29,431 | 4,099 | 13.9 | 11.07 | -14.0 | 1.6 | -20.9 | -14.7 | -11.0 | -17.0 |
| skip compressed: >= 4 within 5 pts (kept 68%) | 20,696 | 3,051 | 14.7 | 10.59 | -11.4 | 1.9 | -18.7 | -12.5 | -6.6 | -16.2 |
| skip compressed: >= 5 within 5 pts (kept 83%) | 25,315 | 3,615 | 14.3 | 10.75 | -13.1 | 1.7 | -20.2 | -13.9 | -9.8 | -16.3 |
| skip compressed: >= 6 within 5 pts (kept 92%) | 28,101 | 3,976 | 14.1 | 10.93 | -13.0 | 1.6 | -20.0 | -13.8 | -10.0 | -16.1 |
| skip compressed: >= 4 within 6 pts (kept 57%) | 17,297 | 2,577 | 14.9 | 10.46 | -11.6 | 2.1 | -18.7 | -12.8 | -6.5 | -16.7 |
| skip compressed: >= 5 within 6 pts (kept 74%) | 22,526 | 3,284 | 14.6 | 10.56 | -12.1 | 1.8 | -19.3 | -13.1 | -8.0 | -16.3 |
| skip compressed: >= 6 within 6 pts (kept 86%) | 26,151 | 3,750 | 14.3 | 10.73 | -12.5 | 1.7 | -19.5 | -13.3 | -8.5 | -16.6 |

gap_1_5 quartiles (larger = less compressed):

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| gap_1_5 0.4 to 5.9 | 7,618 | 882 | 11.6 | 13.17 | -21.5 | 3.3 | -27.7 | -23.9 | -24.4 | -18.7 |
| gap_1_5 5.9 to 8.4 | 7,620 | 1,058 | 13.9 | 11.29 | -9.4 | 3.3 | -16.3 | -11.1 | -5.4 | -13.5 |
| gap_1_5 8.4 to 11.6 | 7,619 | 1,088 | 14.3 | 10.58 | -14.0 | 3.1 | -21.2 | -15.9 | -10.3 | -17.6 |
| gap_1_5 11.6 to 180.3 | 7,618 | 1,180 | 15.5 | 9.84 | -12.3 | 3.0 | -19.6 | -14.3 | -7.6 | -17.0 |

## Test 4: projected map position (last-3 average 800m call) on Spd #1-2, fields of 9+

| Variant | Bets | Wins | Strike % | Avg price | ROI at Top % | ROI s.e. | ROI at SP % | ROI ex top-3 winners % | ROI 1st half % | ROI 2nd half % |
|---|---|---|---|---|---|---|---|---|---|---|
| projected map position in first 8 | 16,744 | 2,214 | 13.2 | 12.04 | -14.1 | 2.2 | -20.9 | -15.3 | -13.4 | -14.8 |
| projected map position 9th or worse | 3,719 | 409 | 11.0 | 14.88 | -20.4 | 4.8 | -27.4 | -24.2 | -16.7 | -24.1 |
| projected in first 4 | 9,399 | 1,239 | 13.2 | 11.16 | -19.9 | 2.5 | -25.9 | -20.8 | -21.6 | -18.2 |

## Test 5b: Dutch the Spd top 4 to equal return

| variant | races | strike % | ROI on outlay % |
|---|---|---|---|
| Dutch Spd top 4 at Top, outlay < 0.8 | 12209 | 52.3 | -9.5 |
| Dutch Spd top 4 at Top, outlay < 1.0 | 16478 | 59.4 | -9.8 |
| Dutch Spd top 4 at SP, outlay < 0.8 | 10542 | 49.1 | -17.0 |
| Dutch Spd top 4 at SP, outlay < 1.0 | 15510 | 57.5 | -16.5 |
