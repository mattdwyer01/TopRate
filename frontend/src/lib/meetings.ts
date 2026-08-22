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
    const key = meetingKey(race)
    const prize = race.prizeMoney ?? 0
    topPrizeByMeeting.set(key, Math.max(topPrizeByMeeting.get(key) ?? 0, prize))
  }
  const bush = new Set<string>()
  for (const [key, topPrize] of topPrizeByMeeting) {
    if (topPrize <= BUSH_TRACK_THRESHOLD) bush.add(key)
  }
  return bush
}

export function todayIso(offsetDays = 0): string {
  const d = new Date()
  d.setDate(d.getDate() + offsetDays)
  return d.toISOString().slice(0, 10)
}
