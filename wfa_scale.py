"""Standard weight-for-age scale, Australian Rules of Racing AR 168 (flat races), and the ATW offset it implies (26 Oct 2026).

TopRate's runner-page rating of a past run = the plain results rating + 0.8 x (W_std - W) where W is the weight the horse carries in the race the page is
struck for (after any apprentice claim) and W_std is this scale's weight for that race (research/atw_offset_exact.py: 5yo and older match exactly, mares and
fillies 2 kg lower per AR 169). So a plain rating can be put on the ATW scale of any race from its date, distance, the horse's racing age and sex, and the weight.

TRANSCRIBED BY HAND from a screenshot of AR 168 supplied by the owner (not from a machine-readable source): cells marked in UNSURE were hard to read, and the
3yo and 4yo values measured in October 2026 sit 0.1 to 1.25 kg above the October column (see research/wfa_check.py), so use the 5yo+ rows with confidence
and re-check the 3yo and 4yo rows against the rules before relying on them. The 2yo rows (January to July only) and the 4yo and 3yo rows are as read.
Not included: AR 170 (allowances for northern hemisphere horses foaled 1 January to 31 July) and races other than flat.

Racing age: a horse's age counts from 1 August (foaled in the 12 months from 1 August 2022 it is a 3yo from 1 August 2025 to 31 July 2026), see racing_age().
"""
import datetime as dt

MONTHS = ['AUG', 'SEP', 'OCT', 'NOV', 'DEC', 'JAN', 'FEB', 'MAR', 'APR', 'MAY', 'JUN', 'JUL']
_NONE = None

# distance blocks: (upper bound in metres inclusive, label)
BLOCKS = [(1200, 'to 1200'), (1400, 'over 1200 to 1400'), (1600, 'over 1400 to 1600'), (2000, 'over 1600 to 2000'), (2400, 'over 2000 to 2400'), (3200, 'over 2400 to 3200')]

# weights in kg by block index, then age ('2', '3', '4', '5' meaning 5yo and older), 12 months from AUG
SCALE = {
    0: {'2': [_NONE] * 5 + [45, 46, 47, 48, 49, 50, 51],
        '3': [51.5, 52, 53, 53.5, 54.5, 55, 55.5, 56, 56.5, 57, 57.5, 58],
        '4': [58.5] * 12, '5': [58.5] * 12},
    1: {'2': [_NONE] * 5 + [44, 45, 46, 47, 48, 49, 50],
        '3': [50.5, 51, 52, 53, 54, 54.5, 55.5, 56, 56.5, 57, 57.5, 58],
        '4': [58.5, 58.5, 58.5, 58.5] + [59] * 8, '5': [59] * 12},
    2: {'2': [_NONE] * 5 + [43.5, 44.5, 45.5, 46.5, 47.5, 48.5, 49.5],
        '3': [50, 50.5, 51, 52, 53, 54, 55, 56, 56.5, 57, 57.5, 58],
        '4': [58.5, 58.5, 58.5, 58.5] + [59] * 8, '5': [59] * 12},
    3: {'2': [_NONE] * 5 + [42.5, 43.5, 44.5, 45.5, 46.5, 47.5, 48.5],
        '3': [49, 49.5, 50, 51, 52, 53, 54, 55, 55.5, 56.5, 57, 57.5],
        '4': [58, 58, 58, 58.5, 58.5, 58.5] + [59] * 6, '5': [59] * 12},
    4: {'2': [_NONE] * 12,
        '3': [48.5, 49, 49.5, 50.5, 51, 52, 53, 54, 54.5, 55.5, 56, 57],
        '4': [57.5, 57.5, 57.5, 57.5, 58, 58, 58.5, 58.5, 58.5, 59, 59, 59], '5': [59] * 12},
    5: {'2': [_NONE] * 12,
        '3': [48, 48.5, 49, 50, 50.5, 51.5, 52.5, 53.5, 54, 55, 55.5, 56],
        '4': [57.5, 57.5, 57.5, 57.5, 58, 58, 58, 58.5, 58.5, 59, 59, 59], '5': [59.5] * 12},
}
UNSURE = ['3yo rows in every block (read from a small screenshot)', '4yo rows over 1200m (where 58.5 turns to 59 and the 58 / 57.5 steps)']
FILLY_MARE_ALLOWANCE_KG = 2.0     # AR 169: fillies and mares in set-weight and set-weight-and-penalties races
ATW_PER_KG = 0.8


def racing_age(foaled, on):
    """Racing age on date `on` for a horse foaled on `foaled` (both date or ISO string): ages tick over on 1 August."""
    f = foaled if isinstance(foaled, dt.date) else dt.date.fromisoformat(str(foaled)[:10])
    d = on if isinstance(on, dt.date) else dt.date.fromisoformat(str(on)[:10])
    season = lambda x: x.year + (1 if x.month >= 8 else 0)
    return season(d) - season(f)


def block_index(distance):
    for i, (hi, _) in enumerate(BLOCKS):
        if distance <= hi:
            return i
    return len(BLOCKS) - 1


def std_weight(age, sex, date, distance):
    """Standard weight (kg) for the race, or None (a 2yo in a month the scale does not cover, an age under 2). age = racing age; sex 'M' or 'F' (mare or filly) get 2 kg off."""
    if age is None or age < 2:
        return None
    d = date if isinstance(date, dt.date) else dt.date.fromisoformat(str(date)[:10])
    row = SCALE[block_index(distance)]['5' if age >= 5 else str(int(age))]
    w = row[(d.month - 8) % 12]
    if w is None:
        return None
    return w - (FILLY_MARE_ALLOWANCE_KG if str(sex).upper()[:1] in ('M', 'F') else 0.0)


def atw_offset(age, sex, date, distance, weight):
    """Rating points to add to a plain rating to put it on the ATW scale of a race with this weight (post-claim). None when the scale has no entry."""
    w = std_weight(age, sex, date, distance)
    if w is None or weight is None:
        return None
    return ATW_PER_KG * (w - float(weight))
