"""
resolve_daily_target.py - figures out what today's scheduled daily.yml run
should actually do, from the REAL current Melbourne local time (DST-aware,
via zoneinfo) rather than the raw UTC cron string that triggered it.

WHY: GitHub Actions cron is UTC-only with no DST awareness. daily.yml's
`on.schedule` fires two candidate UTC times per intended local-time slot -
one correct for AEST (UTC+10), one correct for AEDT (UTC+11) - every day,
regardless of season. This script is the thing that actually decides,
looking at the real Melbourne clock, whether THIS particular firing lands
close enough to one of the real target slots to do work, or whether it's
the other season's now-wrong candidate and should just no-op.

Prints exactly one line to stdout:
  date:YYYY-MM-DD  - run toprate_daily.py --date YYYY-MM-DD
  bare              - run toprate_daily.py with no --date (results collection)
  skip              - no target slot matches right now; do nothing

TOL (15 min) is generous enough to absorb normal GitHub Actions scheduling
jitter, while staying under half the 30-minute gap between the closest
adjacent slots (09:00/09:30, 12:00/12:30) so it can never ambiguously match
the wrong one.
"""
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

TOL = 15

# (target local time in minutes-since-midnight, day offset from today).
# 09:00 and 11:30 are both offset 0 - 11:30 is a same-day re-fetch (catches
# late scratches/price moves), not a new target date.
_TARGETS = [
    (9 * 60 + 0, 0),
    (9 * 60 + 30, 1),
    (11 * 60 + 30, 0),
    (12 * 60 + 0, 2),
    (12 * 60 + 30, 3),
]
_RESULTS_TIME = 23 * 60


def resolve(now=None):
    now = now or datetime.now(ZoneInfo("Australia/Melbourne"))
    mins = now.hour * 60 + now.minute
    for target_mins, offset in _TARGETS:
        if abs(mins - target_mins) <= TOL:
            return f"date:{(now.date() + timedelta(days=offset)).isoformat()}"
    if abs(mins - _RESULTS_TIME) <= TOL:
        return "bare"
    return "skip"


if __name__ == "__main__":
    print(resolve())
