"""
wpr_adjudicate.py - post-race adjudication of projection misses.

For a resulted meeting, sorts every material projection miss into:
  MODEL MISS (low)   model rated the horse too LOW (ran at/above projection,
                     including horses that did so DESPITE a trouble comment -
                     the trouble did not stop them, so the model was simply low)
  MODEL MISS (over)  model rated too HIGH on a clean run with no excuse
  VOID (excuse)      strong excuse (vet/lame/bled/checked/eased/fell) on an
                     UNDER-performance - run is compromised, exclude from error
  VOID (weak)        minor excuse (slow away, held up) on a LARGE underperformance
  PACE-CONTEXT       underperformance explained by race shape (strong late bias
                     against a backmarker), not the model
  MODEL OK           within +/- 5 WPR of projection + offset

The direction rule is the crux: an excuse only voids an UNDERperformance. A
horse that ran ABOVE projection despite trouble is a model-too-low case, not a
void. This stops incident runs from being scored as model error and stops
over-performances from being thrown away.

INPUT
  A meeting __data.json (SvelteKit result page export) for actuals + comments,
  and toprate_runners.csv for the model projection (wprp_proj) and the actual
  it was scored against (wpr_actual = atw). Joined on horse name + date.
  Once toprate_daily.py captures comments into the CSV, the __data.json step
  becomes optional and this can read everything from the CSV.

USAGE
  python wpr_adjudicate.py --data meeting_111137.json --runners toprate_runners.csv
  python wpr_adjudicate.py --data meeting.json --offset 2.57

NO EM DASHES policy: hyphens only.
"""

import sys
import json
import pandas as pd
import numpy as np

STRONG = ['shin', 'vet', 'lame', 'bled', 'blood', 'broke down', 'fell',
          'checked', 'badly hampered', 'eased', 'tailed off', 'severely']
WEAK = ['slowly away', 'slow out', 'bit slow out', 'hampered', 'held up',
        'crowded', 'began awkwardly', 'jumped awkwardly', 'keen', 'raced flat',
        'wide throughout', 'interfere', 'lost', 'tightened']
PACE_WORDS = ['back', 'mid field', 'midfield', 'fades', 'out of picture',
              "couldn't get close", 'no run', 'laboured']


def decode_data_json(path):
    """Decode a SvelteKit __data.json (flat index-pointer array) into objects.
    Returns the meetingResult dict."""
    raw = json.load(open(path))
    node = next((n for n in raw["nodes"]
                 if isinstance(n, dict) and isinstance(n.get("data"), list)), None)
    if node is None:
        raise ValueError("no data node found in __data.json")
    data = node["data"]

    def deref(i, seen=None):
        if seen is None:
            seen = set()
        if isinstance(i, bool) or i is None or not isinstance(i, int):
            return i
        if i in seen or i < 0 or i >= len(data):
            return None
        v = data[i]
        if isinstance(v, dict):
            return {k: deref(idx, seen | {i}) for k, idx in v.items()}
        if isinstance(v, list):
            return [deref(x, seen | {i}) for x in v]
        return v

    root = deref(0)
    return root.get("meetingResult", root)


def excuses(text):
    t = (text or "").lower()
    return [m for m in STRONG if m in t], [m for m in WEAK if m in t]


def classify(proj, act, cv, cs, pace_late, offset):
    if proj is None or act is None:
        return ("NO PROJECTION", "")
    miss = act - (proj + offset)
    text = ((cv or "") + " " + (cs or "")).lower()
    s, w = excuses(text)
    if abs(miss) < 5:
        return ("MODEL OK", f"miss {miss:+.1f}")
    if miss < 0:
        if s:
            return ("VOID (excuse)", f"miss {miss:+.1f} | {', '.join(s[:2])}")
        if w and miss < -8:
            return ("VOID (weak)", f"miss {miss:+.1f} | {', '.join(w[:2])}")
        if pace_late is not None and pace_late < -1.5 and any(k in text for k in PACE_WORDS):
            return ("PACE-CONTEXT", f"miss {miss:+.1f} | late {pace_late}")
        return ("MODEL MISS (over)", f"miss {miss:+.1f} | clean, rated too high")
    tag = " | despite " + ", ".join((s + w)[:2]) if (s or w) else " | clean"
    return ("MODEL MISS (low)", f"miss {miss:+.1f}{tag}")


def main():
    args = sys.argv
    def opt(flag, d):
        return args[args.index(flag) + 1] if flag in args else d
    data_path = opt("--data", "meeting_111137.json")
    runners_csv = opt("--runners", "toprate_runners.csv")
    offset = float(opt("--offset", "2.57"))

    mr = decode_data_json(data_path)
    mdate = str(mr.get("date", ""))[:10]
    venue = mr.get("venue", "")
    csv = pd.read_csv(runners_csv, low_memory=False)
    csv = csv[csv["date"].astype(str).str.startswith(mdate) &
              csv["venue"].astype(str).str.contains(str(venue).split("-")[0], case=False, na=False)]

    def lookup(horse):
        r = csv[csv["horse"].astype(str).str.lower() == str(horse).lower()]
        if not len(r):
            return (None, None, None)
        row = r.iloc[0]
        g = lambda c: (float(row[c]) if c in row and pd.notna(row[c]) else None)
        return (g("wprp_proj"), g("wpr_actual"), g("wprp_conf"))

    rows = []
    for race in mr["races"]:
        pl = race.get("raceShapeLate")
        for u in race["runners"]:
            proj, act, conf = lookup(u.get("horse"))
            verdict, note = classify(proj, act, u.get("commentsVideo"),
                                     u.get("commentsSteward"), pl, offset)
            rows.append({"race": race["number"], "fin": u.get("positionFinish"),
                         "horse": u.get("horse"), "proj": proj, "act": act,
                         "conf": conf, "verdict": verdict, "note": note})
    R = pd.DataFrame(rows)
    P = R[R["verdict"] != "NO PROJECTION"]

    print("=" * 78)
    print(f"{venue} {mdate}  ADJUDICATION  (offset {offset:+.2f})")
    print("=" * 78)
    print("\nVERDICT COUNTS:")
    for k, v in P["verdict"].value_counts().items():
        print(f"   {k:20s} {v}")

    for grp in ["MODEL MISS (low)", "MODEL MISS (over)"]:
        sub = P[P["verdict"] == grp]
        if len(sub):
            print(f"\n{grp}:")
            for _, r in sub.iterrows():
                print(f"   R{r['race']} {str(r['horse'])[:18]:18s} "
                      f"proj{r['proj']:5.1f} act{r['act']:5.1f} "
                      f"fin{int(r['fin']) if pd.notna(r['fin']) else 0:>2}  {r['note']}")

    allmiss = P["act"] - (P["proj"] + offset)
    keep = P[~P["verdict"].isin(["VOID (excuse)", "VOID (weak)"])]
    km = keep["act"] - (keep["proj"] + offset)
    print(f"\nDECONTAMINATION EFFECT:")
    print(f"   all projected:   n={len(P):4d}  mean miss {allmiss.mean():+.2f}  MAE {allmiss.abs().mean():.2f}")
    print(f"   excluding voids: n={len(keep):4d}  mean miss {km.mean():+.2f}  MAE {km.abs().mean():.2f}")
    print("\n   (verdicts are a first pass - overrule any the racing read gets wrong)")


if __name__ == "__main__":
    main()
