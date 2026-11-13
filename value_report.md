# Value model forward test

The model was locked on races to 2026-10-08. Every race below is later than that. Bets are the fixed rule (model chance x net return above 1.00, Betfair starting price under $30), 1 unit each, paid at the Betfair starting price after commission (10% NSW, 8% elsewhere). Research only: no bets are placed, and the Betfair starting price is not known before the jump.

Pass rule, fixed before the first day was scored: first read at 2000 bets, final read at 6000. Pass = return above zero without the 10 best winners, and the bets win more often than the Betfair price implied.

**no read yet: 1477 of 2000 bets**

2026-10-09 to 2026-11-11: 34 days, 1545 races scored, 14792 runners.

| | Bets | Wins | Won | Model said | Betfair said | Avg price | Profit (units) | Return | Return without 10 best |
|---|---|---|---|---|---|---|---|---|---|
| All bets | 1477 | 227 | 15.4% | 15.8% | 14.2% | $12.15 | +6.9 | +0.5% | -13.4% |
| Under $6 | 390 | 134 | 34.4% | 34.8% | 31.8% | $3.62 | +17.0 | +4.4% | -6.3% |
| $6 to $12 | 416 | 47 | 11.3% | 13.2% | 11.7% | $8.95 | -51.8 | -12.4% | -33.7% |
| $12 to $30 | 671 | 46 | 6.9% | 6.4% | 5.6% | $19.08 | +41.6 | +6.2% | -24.4% |
| NSW | 303 | 49 | 16.2% | 17.0% | 15.0% | $11.40 | +6.1 | +2.0% | -38.6% |
| Other states | 1174 | 178 | 15.2% | 15.5% | 14.0% | $12.34 | +0.8 | +0.1% | -17.4% |

Return range from resampling days (90%): -9.3% to +11.0%; chance the return is above zero: 54%.
Winner log-likelihood gain over the Betfair price: +0.0002 a race (standard error 0.0020).

## By week

| Week starting | Bets | Wins | Profit (units) | Return |
|---|---|---|---|---|
| 2026-10-05 | 187 | 23 | -26.0 | -13.9% |
| 2026-10-12 | 292 | 52 | +91.1 | +31.2% |
| 2026-10-19 | 300 | 45 | -9.2 | -3.1% |
| 2026-10-26 | 314 | 42 | -39.0 | -12.4% |
| 2026-11-02 | 314 | 49 | -15.6 | -5.0% |
| 2026-11-09 | 70 | 16 | +5.6 | +8.0% |
