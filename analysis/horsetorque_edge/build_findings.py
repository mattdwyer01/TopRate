"""Assemble ../horsetorque_edge_findings.md from results/t*.md plus the written summary."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
import pandas as pd
from common import *
from model import md

here = os.path.dirname(os.path.abspath(__file__))
D = pd.read_pickle(os.path.join(CACHE, 'features.pkl'))
cov = D.groupby('dt_year').agg(runs=('win', 'size'), races=('race_id', 'nunique'), last400=('sect_i_l400', lambda s: s.notna().mean() * 100),
                               pos800=('position800m', lambda s: s.notna().mean() * 100), top_price=('price_top', lambda s: (s > 1).mean() * 100)).reset_index().rename(columns={'dt_year': 'year'})
for c in ('year', 'runs', 'races'):
    cov[c] = cov[c].astype(int).map(lambda v: str(v) if c == 'year' else f'{v:,}')
cov_md = md(cov, {'last400': '{:.0f}%', 'pos800': '{:.0f}%', 'top_price': '{:.0f}%'})
R = lambda n: open(os.path.join(here, 'results', n)).read()

head = f"""# Horsetorque "Edge" ideas: backtest findings (19 Oct 2026)

Branch `claude/horsetorque-edge-backtest-tjul7l`. Code: `analysis/horsetorque_edge/` (analysis only; nothing in production, `runners.csv`, the payload or the locked rule was changed).
Reproduce: `python analysis/horsetorque_edge/run_all.py` (about 12 minutes), then `python analysis/horsetorque_edge/build_findings.py`.

## Read this first: what could and could not be tested

1. **The locked rule can only be tested on 26 Apr to 8 Oct 2026.** TR rating and the Mid/Late/Total speed scores exist only in the retired TopRate runner files
   (`archive/toprate/`), for 7,158 resulted races. The rule as given (TR rank <= 3, Mid, Late and Total ranks each <= 2, Top price >= $3, fixed-odds win) made
   **885 bets in that window**. The results files carry no TR rating, and the private racing-model repo was not available in this session, so there is no 2016+ version of the locked rule.
   The v3 header in `toprate_html_v3.py` is the only definition in this repo (the picks log shows the `main` model changed definition several times in May 2026); "Mid+Late+Total top 2" is read as each of the three ranks <= 2.
2. **"2016+" is really 2019+.** The results files have almost nothing before 2019 (2016: 83 rows, 2017: about 4k rows, 2018: about 19k rows, with no last-400m and almost no prices):

{cov_md}

3. **Reference rule P (2019 to 2026) is a stand-in, not the locked rule.** To get an 8-year population I built rule P from as-of results data: last-3 WPR rank <= 3, as-of Mid/Late/Total sectional proxies each rank <= 2, Top >= $3, at least 3 prior runs.
   The proxies match the real columns poorly (within-race rank correlation with the real score: Mid 0.29, Late 0.44, Total 0.77, TR vs last-3 WPR 0.71; `calibrate_proxy.py`). In the 2026 window only 219 of rule P's 3,912 picks are real locked-rule picks (6%), and rule P finds 25% of the real ones.
   Rule P bets 4x as often at longer prices (avg $11.8 vs $5.4). Read results on P as "does this idea move a sectional-form rule", never as "this is what the locked rule would have done". Where the two disagree, trust neither; the real-rule sample is small.
4. **The Top price is a hindsight maximum.** `price_top` is at or above the starting price on 100% of 2019 to 2026 runs (average +10.8%), so it is the best price the horse reached, not a price you can reliably take. Every ROI table therefore shows **ROI at Top and ROI at SP**; the achievable result sits between them.
   The real locked rule returns +4.2% at Top and -5.1% at SP over 885 bets (s.e. about 7 points either way), i.e. it is not distinguishable from zero.
5. **Sectional units.** The results files hold last-400m as `sect_i_l400` in lengths against a per-race standard, not seconds (a per-runner time is not stored; `time_last600m` is a race constant filled on 1 to 30% of races). XR uses 0.147 s per length (the repo-measured figure), so 0.1 s = 1 point = 0.68 lengths.
   Values beyond 15 lengths from the winner are clipped (the columns hold +-100 data errors). These are TopRate-authored columns, read raw on purpose (the production `own_overlay` blanks them).
6. **Model.** A walk-forward logistic regression (train before year Y, test 2023 to 2026, 636k runners, 67.6k races; features demeaned within race; price never a feature) stands in for the racing-model rating model. AUC and log-loss are out of sample. "Gain" is the paired drop in race-level winner log-loss against the base set (positive = better), with its standard error.
7. **Settled position** is `position800m` (`positionSettled` is blank in every file). **F&M and 3YOF rungs** can only be detected from `race_name` (filled on about 15% of rows), so they apply to 0.02% of runs. **Race shape** was projected in the analysis module only; nothing was written to `runners.csv`.
8. **Many looks.** Test 3 is a 12-cell sweep on 885 bets. A cell that looks good there needs to hold in halves and on the second data set before it counts.

## Verdicts

| # | Idea | Verdict |
|---|---|---|
| 1 | Class par ladder | **Worth keeping as a feature, small gain, not a betting edge.** class_par class_move/peak_at_class beat the trackGrading version (+0.0019 vs +0.0007 nats a race, t 9.6) and the retired rung ladder (+0.0014). sr_vs_par adds nothing on top. ROI is unchanged within noise. The Open (non black type) rung of 100 is about 6 points too high against what winners rate. |
| 2 | XR / TOF | **Small model gain (+0.0020 nats, t 5.5), no ROI change, avoid flag not supported.** The flag is rare (0.7% of runs) and flagged runners do not lose more than unflagged ones. |
| 3 | Compression gate | **Not supported.** No gate improves rule P at any of the 12 settings (best -10.0% vs -10.2% ungated; tight gates are worse). The real-rule best cell (+10.6%, n=502) does not hold up when the same gate uses `wpr_nett` (-4.6%). |
| 4 | Golden 8 | **The ~75% claim does not hold as stated.** 91% of all winners settle in the first 8 only because most fields are 8 or fewer. In fields of 9+ it is 86.8% against 73.0% of runners (lift 1.19); 75% is reached only at 13 to 14 runners. A real but modest map effect. Projected map position adds +0.0016 nats. Race shape cannot be projected from settle positions (R2 0.05, 0.00, 0.06). |
| 5a | Price bands / $3 floor | **No case to move the floor.** Below $3 the real rule loses (-5.3% at $1.5-2, -10.8% at $2-3), but $3 vs $2.5 vs $4 vs $5 are all inside one standard error (7 to 12 points), and rule P points the other way. |
| 5b | Dutch top 4, outlay < 80% | **Loses.** -6.9% at Top and -15.6% at SP over 38.7k model races (59% strike); market top 4 (-4.8% at Top) and TopRate-rank top 4 (-6.3% at Top, -14.5% at SP) are similar. Not a useful benchmark to beat. |

---
"""

tail = """
---

## Notes on the numbers

* **Test 1.** Winner WPR minus par is not flat down the ladder: -4 to -7 for Group, Listed and most BM/CLS rungs, but -12.2 for Open (no black type) and -11.0 / -11.3 at the BM 94+ and below-62 ends. If the ladder is meant to be in WPR points, Open (no black type) at 100 is the clear outlier (generic Open races are mostly open handicaps).
  The "known bug" (class_move off `trackGrading`, which is the going number) had already been fixed in the retired `wpr_projection.py` with a rung ladder; the trackGrading row is that old behaviour for comparison. CLS2 to CLS6, RSTnn and R0MW/R1MW are not on the supplied ladder and were mapped by assumption (see `class_par.py`).
* **Test 2.** At 1.47 points per length XR is compressed against WPR (TOF averages +5.8 for beaten runners), so raw "TOF < 0" is a narrow cut. The 2.15 points per length and race-relative versions are in table 2c. Rear-third settlers almost always have a positive TOF, which is why the specified flag is so rare.
  On the real rule only 16 picks carry the specified flag (99 with the race-relative version, +26.2% at Top, s.e. 23.8): too few to read either way. TOF rank 1 as a stand-alone pick picks $50 longshots and loses 28%.
* **Test 3.** In rule P the widest-gap quartile (least compressed) has the worst ROI (-16.0%) because it holds the longest prices; compression is mostly a proxy for price. Gate rows on the real rule swing between -15.7% and +10.6% with s.e. 8 to 12 points, which is noise-sized.
* **Test 4.** Position 1 at the 800m call wins 21.1% of the time, 2nd 14.1%, down to 2.7% for 13th or worse; the cumulative share passes 75% at the 6th position over all fields. Projected map position (average 800m position of the last 3 starts) correlates 0.43 with the actual call.
  `results/race_shape_projected.csv.gz` (not committed, regenerate with `t4_golden8.py`) holds the projected shape values for inspection.
* **Test 5.** The Dutch outlay test uses the Top price both to choose races (outlay < 0.8) and to settle them, so it is biased in the bettor's favour; the SP rows are the fair check.

## What would make these tests sharper

* The locked rule's real inputs for 2016 to 2025 (the racing-model repo) would turn the 885-bet sample into one with thousands of bets.
* A pre-race fixed price history (opening or mid prices exist for only about 21% of 2026 runs here) would replace the Top / SP bracket.
* Per-runner last-400m times, if the racing-model repo holds them, would replace the length-to-seconds conversion.
"""
open(os.path.join(here, '..', 'horsetorque_edge_findings.md'), 'w').write(head + '\n'.join(R(f't{i}.md') + '\n' for i in range(1, 6)) + tail)
print('written')
