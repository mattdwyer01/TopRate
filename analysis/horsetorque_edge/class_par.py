"""Test 1: class par ladder (Horsetorque Edge idea 1).

Maps (race_class, blackType, age_restriction, race_name) to a numeric class_par.
Analysis only: nothing here is imported by production code.

Ladder as supplied by the owner (Open unless stated):
  G1 110, F&M G1 108, 3YO G1 106, 3YOF G1 105, 2YO G1 102
  G2 107, F&M G2 105, 3YO G2 103, 3YOF G2 102, 2YO G2 99
  G3 103, 3YO G3 99, 3YOF G3 98, 2YO G3 95
  LR 101, F&M LR 99, 3YO LR 97, 2YO LR 93
  Open 100, Open F&M 98, 3YO Open 96, 2YO Open 92
  BM94 98, BM84 96, BM74 93, C1/BM62 91, Maiden 86
Other BM levels are interpolated linearly between those anchors.

Assumptions the data forces (see RESULTS.md):
  * F&M / 3YOF can only be detected from race_name (Fillies, Mares, Oaks...), which is
    filled on ~15% of rows, so most F&M races fall back to the Open/3YO rung.
  * 3YO / 2YO come from age_restriction ('3yo', '2yo', '2,3yo' counts as 2YO).
  * CLS2..CLS6 are not on the owner's ladder; mapped to BM70, 78, 86, 94, 100 equivalents.
  * RSTnn (restricted) is treated as BMnn; R0MW/R1MW (win-count series) as Maiden+2.
"""
import re
import numpy as np
import pandas as pd

BM_ANCHORS = [(62, 91.0), (74, 93.0), (84, 96.0), (94, 98.0)]
MAIDEN = 86.0

# (open, f&m, 3yo, 3yof, 2yo)
BLACK = {
    'G1': (110, 108, 106, 105, 102),
    'G2': (107, 105, 103, 102, 99),
    'G3': (103, None, 99, 98, 95),
    'LR': (101, 99, 97, None, 93),
    'OPEN': (100, 98, 96, None, 92),
}
CLS_AS_BM = {'CLS1': 62, 'CLS2': 70, 'CLS3': 78, 'CLS4': 86, 'CLS5': 94, 'CLS6': 100,
             'CLSA': 50, 'CLSB': 55, 'REST': 58}
JUMPS = {'STEEPLE', 'HURDLE', 'NOVH', 'RESTH', 'R1HW', 'MAIH', 'JUMPOUT'}
FM_RE = re.compile(r'\b(?:fillies|filly|mares|mare|oaks|f&m|f & m)\b', re.I)


def bm_par(n):
    """Linear interpolation between the BM anchors; extrapolate with the nearest segment."""
    xs = [a for a, _ in BM_ANCHORS]; ys = [b for _, b in BM_ANCHORS]
    if n <= xs[0]:
        slope = (ys[1] - ys[0]) / (xs[1] - xs[0])
        return ys[0] + slope * (n - xs[0])
    if n >= xs[-1]:
        slope = (ys[-1] - ys[-2]) / (xs[-1] - xs[-2])
        return min(ys[-1] + slope * (n - xs[-1]), 99.5)
    return float(np.interp(n, xs, ys))


def class_par_one(race_class, black, age, name):
    c = '' if race_class is None or (isinstance(race_class, float) and np.isnan(race_class)) else str(race_class).strip().upper()
    if c in JUMPS or c in ('', 'NAN'):
        return np.nan
    age = '' if age is None or (isinstance(age, float) and np.isnan(age)) else str(age).lower()
    fm = bool(FM_RE.search(name)) if isinstance(name, str) else False
    is2 = age == '2yo'
    is3 = age == '3yo'
    key = black if isinstance(black, str) and black in BLACK else ('OPEN' if c == 'OPEN' else None)
    if key:
        o, f, t3, t3f, t2 = BLACK[key]
        if is2 and t2 is not None: return float(t2)
        if is3 and fm and t3f is not None: return float(t3f)
        if is3 and t3 is not None: return float(t3)
        if fm and f is not None: return float(f)
        return float(o)
    if c.startswith('MAI'):
        return MAIDEN
    if c in CLS_AS_BM:
        return bm_par(CLS_AS_BM[c])
    m = re.match(r'^(BM|RST)(\d+)', c)
    if m:
        return bm_par(int(m.group(2)))
    if c.startswith('R0MW') or c.startswith('R1MW'):
        return MAIDEN + 2
    return np.nan


def add_class_par(df):
    """Vectorised via a lookup over the distinct (race_class, blackType, age, F&M flag) tuples."""
    fm = df['race_name'].astype('string').str.contains(FM_RE, na=False) if 'race_name' in df else pd.Series(False, index=df.index)
    key = pd.DataFrame({'c': df['race_class'], 'b': df['blackType'], 'a': df['age_restriction'], 'fm': fm})
    uniq = key.drop_duplicates()
    uniq['par'] = [class_par_one(c, b, a, 'Fillies' if f else None) for c, b, a, f in zip(uniq.c, uniq.b, uniq.a, uniq.fm)]
    out = key.merge(uniq, on=['c', 'b', 'a', 'fm'], how='left')['par'].values
    df['class_par'] = out
    return df
