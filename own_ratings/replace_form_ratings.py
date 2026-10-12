"""Replace every rating in wpr_form_history.csv.gz with our own (13 Oct 2026).

Input is the file written by `python -m own_ratings.rebuild_history` (our chain run over all past races from an empty history, no TopRate
rating in its inputs). Each form row takes the own rating of the same run (matched on horse id and date, then horse name and date); a row
with no own rating (a barrier trial, a jumps race, a run with no margin) is left blank rather than keeping TopRate's number.

The rating is the plain WPR at the weight carried in that run, so the form feed's "rating at the next start's weight" shift (the ATW
offset) no longer exists: atw_offsets.compute_atw_offsets() now returns {}.

  python -m own_ratings.replace_form_ratings --ratings own_history.csv.gz [--dry-run]
"""
import argparse
import sys

import pandas as pd

FORM_FILE = "wpr_form_history.csv.gz"


def norm(s):
    return s.astype(str).str.strip().str.lower()


def replace(form: pd.DataFrame, own: pd.DataFrame):
    """Return (form with `wpr` replaced, matched count). `own` needs date, horse_id, horse, wpr."""
    own = own.dropna(subset=["wpr"]).copy()
    own["d"] = own.date.astype(str).str[:10]
    own["hid"] = pd.to_numeric(own.horse_id, errors="coerce")
    own["hl"] = norm(own.horse)
    by_id = own.dropna(subset=["hid"]).drop_duplicates(["hid", "d"], keep="last").set_index(["hid", "d"]).wpr
    by_nm = own.drop_duplicates(["hl", "d"], keep="last").set_index(["hl", "d"]).wpr
    f = form.copy()
    d = f.date.astype(str).str[:10]
    hid = pd.to_numeric(f.horse_id, errors="coerce")
    a = pd.Series(list(zip(hid, d)), index=f.index).map(by_id)
    b = pd.Series(list(zip(norm(f.horse), d)), index=f.index).map(by_nm)
    new = a.fillna(b)
    f["wpr"] = new.round(1)
    return f, int(new.notna().sum())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ratings", required=True)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    own = pd.read_csv(a.ratings, usecols=["date", "horse_id", "horse", "wpr"], low_memory=False)
    form = pd.read_csv(FORM_FILE, low_memory=False)
    new, n = replace(form, own)
    print(f"form rows {len(form):,}: {n:,} now carry an own rating ({n / len(form):.1%}); {len(form) - n:,} left blank")
    old = pd.to_numeric(form.wpr, errors="coerce")
    both = old.notna() & new.wpr.notna()
    print(f"vs the TopRate numbers they replace (report only): mean difference {(new.wpr[both] - old[both]).mean():+.2f}, "
          f"mean absolute {(new.wpr[both] - old[both]).abs().mean():.2f} over {both.sum():,} rows")
    if not a.dry_run:
        new.to_csv(FORM_FILE, index=False, compression="gzip")
        print("written", FORM_FILE)
    return 0


if __name__ == "__main__":
    sys.exit(main())
