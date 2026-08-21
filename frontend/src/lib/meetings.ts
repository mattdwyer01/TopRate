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
  return meeting.topRacePrizeMoney <= BUSH_TRACK_THRESHOLD
}

export function todayIso(offsetDays = 0): string {
  const d = new Date()
  d.setDate(d.getDate() + offsetDays)
  return d.toISOString().slice(0, 10)
}
