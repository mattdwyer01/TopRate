"""Build the race table for the Spd exotic-box study (speed_exotics_nuggets.py): the pre-race Spd rating for every runner of every results-file race
2025-07 to 8 Oct 2026, exactly as speed_rating.compute() does it (EWM of par v2 figures, shrink for few figures, days and weight terms), plus finishing order,
starting price, field size, distance, going, class. Writes a gzip CSV (path = argv[1]).
usage: PYTHONPATH=. python research/speed_exotics_build.py OUT.csv.gz
"""
import sys

import numpy as np
import pandas as pd

import speed_rating as S


def main(out):
    d = S.load_results(2022)
    d = d[d["date"] <= "2026-10-08"]
    h = S.history(d)
    mu = float(h.loc[h["nfig"] >= 6, "rating"].mean())
    t = d[d["date"] >= "2025-07-01"].copy()
    t["key"] = t["horse"].astype(str).str.lower().str.strip()
    q = t[["race_id", "date", "key", "weightCarried"]].sort_values("date").reset_index(drop=True)
    m = pd.merge_asof(q, h, on="date", by="key", allow_exact_matches=False, tolerance=pd.Timedelta(days=400))
    k = np.select([m["nfig"] == 1, m["nfig"] == 2, m["nfig"].between(3, 5)], [S.SHRINK[1], S.SHRINK[2], S.SHRINK[3]], default=1.0)
    rating = mu + k * (m["rating"].values - mu)
    adj = S._adjustment(m, pd.Series(m["date"].values, index=m.index), m["weightCarried"])
    m["spd_len"] = rating + adj
    m = m[["race_id", "key", "spd_len", "nfig"]].drop_duplicates(["race_id", "key"])
    t = t.merge(m, on=["race_id", "key"], how="left")
    import glob
    ex = pd.concat([pd.read_csv(f, usecols=["race_id", "horse", "priceStarting", "raceNumber", "barrier", "price_opening"], low_memory=False)
                    for f in sorted(glob.glob("race_results_202[56].csv.gz"))], ignore_index=True).drop_duplicates(["race_id", "horse"])
    t = t.merge(ex, on=["race_id", "horse"], how="left")
    cols = ["race_id", "date", "track", "raceNumber", "horse", "distance", "going", "race_class", "field_size", "positionFinish", "priceStarting",
            "weightCarried", "barrier", "spd_len", "nfig", "price_opening"]
    t[[c for c in cols if c in t.columns]].to_csv(out, index=False)
    print(len(t), "runs", t.race_id.nunique(), "races", t.spd_len.notna().mean())


if __name__ == "__main__":
    main(sys.argv[1])
