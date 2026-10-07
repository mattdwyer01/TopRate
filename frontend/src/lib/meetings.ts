import type { Race } from '../types/domain'

export interface Meeting {
  date: string
  venue: string
  state: string
  races: Race[]
  totalPrizeMoney: number
  topRacePrizeMoney: number
}

// Bush/picnic-meeting threshold: matches the current dashboard's "hide small
// meetings" default (toprate_html_v3.py renderMeetingsGrid) - a meeting
// whose BIGGEST single race tops out at $20k or less is treated as bush/
// picnic-grade and hidden unless the user opts in.
export const BUSH_TRACK_THRESHOLD = 20_000

export function groupIntoMeetings(races: Race[], date: string): Meeting[] {
  const byVenue = new Map<string, Race[]>()
  for (const race of races) {
    if (race.date !== date) continue
    const existing = byVenue.get(race.venue)
    if (existing) existing.push(race)
    else byVenue.set(race.venue, [race])
  }
  const meetings: Meeting[] = []
  for (const [venue, venueRaces] of byVenue) {
    venueRaces.sort((a, b) => a.raceNumber - b.raceNumber)
    const prizes = venueRaces.map((r) => r.prizeMoney ?? 0)
    meetings.push({
      date,
      venue,
      state: venueRaces[0].state,
      races: venueRaces,
      totalPrizeMoney: prizes.reduce((a, b) => a + b, 0),
      topRacePrizeMoney: Math.max(0, ...prizes),
    })
  }
  meetings.sort((a, b) => b.totalPrizeMoney - a.totalPrizeMoney)
  return meetings
}

export function isBushMeeting(meeting: Meeting): boolean {
  // No prize data at all means unknown, not bush: never hide a meeting on missing data.
  if (!meeting.races.some((r) => r.prizeMoney != null)) return false
  return meeting.topRacePrizeMoney <= BUSH_TRACK_THRESHOLD
}

// Meeting identity for a single race, independent of any one day's grouping
// (the ticker looks ahead up to 24h, so it can span two dates at once).
export function meetingKey(race: Race): string {
  return `${race.date}::${race.venue}`
}

// Same bush/picnic rule as isBushMeeting, computed directly across a race
// list spanning any number of dates/venues - lets a consumer like the
// next-to-jump ticker filter individual races without grouping into Meeting
// objects first.
export function bushMeetingKeys(races: Race[]): Set<string> {
  const topPrizeByMeeting = new Map<string, number>()
  for (const race of races) {
    if (race.prizeMoney == null) continue // unknown prize: never counts a meeting as bush
    const key = meetingKey(race)
    const prize = race.prizeMoney
    topPrizeByMeeting.set(key, Math.max(topPrizeByMeeting.get(key) ?? 0, prize))
  }
  const bush = new Set<string>()
  for (const [key, topPrize] of topPrizeByMeeting) {
    if (topPrize <= BUSH_TRACK_THRESHOLD) bush.add(key)
  }
  return bush
}

// Every distinct venue string seen across the loaded races (any date in the
// window, not just one day) - the source list for a "choose venues to hide"
// UI (see lib/hiddenVenues.ts). No normalization: venue is a raw passthrough
// string from the pipeline (api/adapter.ts), matching how groupIntoMeetings/
// bushMeetingKeys above already treat it - a genuine spelling drift between
// data sources would need fixing at the source, not papered over here.
export function distinctVenues(races: Race[]): string[] {
  return Array.from(new Set(races.map((r) => r.venue))).sort((a, b) => a.localeCompare(b))
}

// "Today" for this dashboard always means the current date in Melbourne
// (the backend's own race-day boundary - the daily fetch workflow resolves
// its target date from the real Australia/Melbourne local time too, see
// .github/workflows/daily.yml). Deliberately NOT `new Date().toISOString()`:
// that converts the VIEWER's local clock to UTC, which disagrees with
// Melbourne for the ~10-11 hours/day UTC lags behind AEST/AEDT (race
// morning) - the "Today" button would show yesterday's meetings for a
// chunk of every morning, and worse for a viewer outside Australia.
export function todayIso(offsetDays = 0): string {
  const melbourneToday = new Intl.DateTimeFormat('en-CA', {
    timeZone: 'Australia/Melbourne',
    year: 'numeric',
    month: '2-digit',
    day: '2-digit',
  }).format(new Date())
  if (offsetDays === 0) return melbourneToday
  // Anchor the offset arithmetic in UTC on the already-correct Melbourne
  // date string, rather than re-interpreting it in local time (which would
  // reintroduce the same timezone mismatch this function exists to avoid).
  const d = new Date(`${melbourneToday}T00:00:00Z`)
  d.setUTCDate(d.getUTCDate() + offsetDays)
  return d.toISOString().slice(0, 10)
}

export interface MeetingConditions {
  going: string | null
  rail: string | null
  // The going the meeting started on, set only when it has since changed.
  goingFrom: string | null
}

/** Track condition for a meeting: the going of the next race still to run (the last race if all have run), the rail position, and what
 * the going was at the first race when it has changed. `done` says whether a race has run. */
export function meetingConditions(meeting: Meeting, done: (race: Race) => boolean): MeetingConditions {
  const races = meeting.races
  const current = races.find((r) => !done(r)) ?? races[races.length - 1]
  const first = races[0]
  const going = current?.going || null
  const firstGoing = first?.going || null
  return {
    going,
    rail: current?.rail || null,
    goingFrom: going && firstGoing && firstGoing !== going ? firstGoing : null,
  }
}
