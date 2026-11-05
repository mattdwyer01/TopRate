"""Back-fill the bad-run risk (projection/train_risk.py) for logged runs that have none (5 Nov 2026): runners of races before today get the risk the model gives from the
horse's page runs strictly before the race date (ctx.predict builds the same as-of features as for an upcoming runner). Only the log's `risk` column is written, never a projection.
CAVEAT: risk_model.txt was fitted on every page run to its date, which includes these finished races, so back-filled risks are in sample (a little too good); live risks are not.
Run: PYTHONPATH=. python projection/backfill_risk.py [--since 2026-10-01]"""
import argparse, os, sys
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ctx as C          # noqa: E402
import projlog           # noqa: E402
import runners_io        # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--since', default='2026-09-01')
    ap.add_argument('--until', default=None, help='last date to fill (default: yesterday UTC)')
    a = ap.parse_args()
    until = a.until or (pd.Timestamp.now('UTC').normalize() - pd.Timedelta(days=1)).strftime('%Y-%m-%d')
    lg = projlog.load()
    todo = lg[(lg.risk.isna()) & (lg.date >= a.since) & (lg.date <= until)]
    print('log rows without risk in range:', len(todo))
    rr = runners_io.read_runners()
    rr['run_id'] = pd.to_numeric(rr.run_id, errors='coerce')
    rr = rr[rr.run_id.isin(todo.run_id)].copy()
    rr = rr[rr.scratched.fillna(0).astype(float) != 1]
    rr['field_size'] = rr.groupby('race_id').horse.transform('size')
    T = pd.DataFrame(dict(horse_id=rr.horse_id.values, date=rr.date.values, jockey=rr.jockey.values, trainer=rr.trainer.values, distance=rr.distance.values, going=rr.going.values,
                          weightCarried=rr.weight_carried.values, barrier=rr.barrier.values, field_size=rr.field_size.values, race_class=rr.race_class.values,
                          trackGrading=rr.track_grading.values, venue=rr.venue.values, prize=rr.prize_money.values)).reset_index(drop=True)
    _, _, risk = C.predict(T, want_risk=True)
    got = pd.Series(np.round(risk * 100, 1), index=rr.run_id.astype('int64').values)
    got = got[~got.index.duplicated()].dropna()
    print('risks computed:', len(got), 'mean %.1f' % got.mean())
    m = lg.run_id.isin(got.index) & lg.risk.isna()
    lg.loc[m, 'risk'] = lg.loc[m, 'run_id'].map(got)
    lg = lg.sort_values(['date', 'race_id', 'run_id'])
    lg.to_csv(projlog.PATH, index=False, compression='gzip', float_format='%.2f')
    print('written', int(m.sum()), 'rows')


if __name__ == '__main__':
    main()
