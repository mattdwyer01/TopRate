# New WPR projection pipeline

Projects a WPR for every runner in upcoming races and writes `wpr_projection_new.json` at the repo root. It does not change
anything on the dashboard yet: nothing reads this file until the cutover.

- `features.py` builds every feature as of the race date, for past runs and for races that have not run, with the same code.
  Ported from the research scripts and checked against them (`validate.py`): features match exactly for past runs and for runs
  whose outcome is hidden, and end-to-end predictions agree to under 0.01 WPR.
- `run.py` routes each runner: three or more prior rated runs use the main model (139 features, 5 seeds), 0-2 prior runs use the
  light-history model. Main-model projections get a small suitability adjustment (about +-1 WPR). The file records the model, the
  number of prior runs, an error estimate (sd) and the going the race was projected on.
- `train_light.py` retrains the light-history model. `setup_artifacts.py` writes the frozen class/track levels, the comment-text
  vectoriser and the shipped main-model seeds (`models/`).

Run order for a refresh: `python projection/run.py` (about 10 minutes, full history rebuild).

Going: each race is projected on the going held in `toprate_runners.csv` when `run.py` runs. The model reads the going, the change
from the horse's last run and the horse's record on that going. A mid-meeting track change takes effect when `run.py` is re-run
after `tab_results_poller.py` has updated the going.

Known gaps in live use
- Weight carried, jockey and sometimes going are blank until the field is declared; the model handles blanks but projections for
  races declared early are less certain.
- Weight allowance, and age/sex for horses with no previous run, are not in the upcoming-runner data (age and sex are carried
  from the horse's last run).
- Day-of track-bias features need 800m positions, which arrive only with the authoritative results pass; intraday only the
  finishing-order part is available.
- Light-history projections run slightly low on average (about +0.5 to +1.1 WPR actual above projected); the stage-wise bias is
  written to `models/light_info.json` and is not applied.
