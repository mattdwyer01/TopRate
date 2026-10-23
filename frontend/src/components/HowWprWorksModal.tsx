import { useRef } from 'react'
import { useBodyScrollLock, useFocusTrap } from '../lib/modalA11y'

interface HowWprWorksModalProps {
  onClose: () => void
}

function Section({ title, children }: { title: string; children: React.ReactNode }) {
  return (
    <section className="border-b border-line-soft px-4 py-4 last:border-0 sm:px-6">
      <h2 className="mb-2 text-sm font-semibold text-ink">{title}</h2>
      <div className="space-y-2 text-sm leading-relaxed text-ink-soft">{children}</div>
    </section>
  )
}

// A dedicated page (styled as a full modal, matching RunnerDetailModal's pattern) describing how the projection is built. It describes
// the new model (projection/ in the repo): what goes in, how accurate it was on races it had not seen, and what it does not do.
export function HowWprWorksModal({ onClose }: HowWprWorksModalProps) {
  const panelRef = useRef<HTMLDivElement>(null)
  useBodyScrollLock()
  useFocusTrap(panelRef)

  return (
    <div
      className="fixed inset-0 z-50 flex items-start justify-center overflow-y-auto bg-ink/60 p-3 sm:items-center sm:p-6"
      onClick={onClose}
    >
      <div
        ref={panelRef}
        role="dialog"
        aria-modal="true"
        aria-label="How WPR is calculated"
        tabIndex={-1}
        className="flex max-h-full w-full max-w-3xl flex-col overflow-y-auto rounded-lg bg-panel shadow-[var(--shadow-2)] outline-none"
        onClick={(e) => e.stopPropagation()}
      >
        <div className="sticky top-0 z-10 flex items-center justify-between border-b border-line bg-panel px-4 py-3 sm:px-6">
          <span className="text-base font-semibold text-ink">How WPR is calculated</span>
          <button
            type="button"
            onClick={onClose}
            className="flex h-8 w-8 items-center justify-center rounded-md text-ink-mute transition-colors hover:bg-bg hover:text-ink"
            aria-label="Close"
          >
            ✕
          </button>
        </div>

        <Section title="The short version">
          <p>
            <span className="font-mono text-ink">WR</span> is the WPR projection: a machine-learned estimate of the WPR a horse will run from its
            past runs and the conditions, trained on ten years of Australian results. It is shown at the weight carried today (ATW), the same scale as the
            Recent runs table, and it is the figure each race is ranked on. Base and Adj below describe it. <span className="font-mono text-ink">Rated $</span> is
            the price that projection implies for each runner, from a simulation of the race in which every runner's true figure is its projection plus noise (larger for horses with little history); hover a Proj value for the rated price and place price. It is the model's view, not a betting price.
          </p>
          <p>
            Horses with three or more prior rated runs use the main model. Horses with none, one or two prior runs
            (debut, second and third starters) use a separate light-history model that leans on the trainer, jockey,
            trials and race class instead of form. The runner panel says which one was used.
          </p>
        </Section>

        <Section title="Column and label guide">
          <ul className="list-disc space-y-1 pl-5">
            <li><span className="font-mono text-ink">Peak</span>: the highest rating the horse has run in the 12 months before the race (runner-page ratings, the same scale as WR). A blank means no rated run in that time.</li>
            <li><span className="font-mono text-ink">WR</span>: the WPR projection at the weight carried today, and the race's ranking figure. <span className="font-mono text-ink">Base</span> + <span className="font-mono text-ink">Adj</span> = the projection, which the runner page explains.</li>
            <li><span className="font-mono text-ink">First starters</span>: a horse with no form has no form rating. Its WR (shown with a ~ and an est tag) is an estimate: the level of the race from its experienced runners plus an adjustment for the runner&apos;s price against the field, so it mostly reflects the market. It is kept out of the Rating, the gap lines and the quaddie pools.</li>
            <li><span className="font-mono text-ink">Rating</span>: since 23 Oct 2026 this is the WR itself (WR 100%). Base (TopRate's Nett) and Spd are shown for reference but are not counted; the small squares under the Rating show the runner's rank on Peak, Base and Spd, in that order. The table is sorted by it. It is a reading aid, not a bet.</li>
            <li><span className="font-mono text-ink">Spd</span>: the pre-race speed rating. Each earlier run gets a time-based figure (finish time against a par time for the track, distance, class and going, plus a same-day track allowance), in lengths, and the rating is a recency-weighted average of those figures, shown on the same scale as the other ratings: 79 is a par performance and each length is about 1.3 points, so its spread matches Nett and Proj. Higher is faster; a typical horse is around 73. In testing it picked the winner about 20% of the time against 29% for Proj, so it is the weakest of the three and best read alongside them.</li>
            <li><span className="font-mono text-ink">SM</span> (speed map, shown on the Trip map): the suitability part of the projection, relative to this field. A green dot on a runner is +0.5 or better, red is -0.5 or worse; hover a runner for the figure. Runners at +0.5 or better won more often in testing, but the market already prices it.</li>
            <li><span className="font-mono text-ink">Rated price</span> (in the WR tooltip and on the runner page): the price the projection implies, from a softmax over the field's projections. It is the model's own view of the race, not a value claim: the earlier rated-price-against-market signal lost 30 to 39% at every threshold in testing.</li>
            <li><span className="font-mono text-ink">Fixed $</span>: the current fixed-odds win price. <span className="font-mono text-ink">FP</span>: finishing position.</li>
            <li><span className="font-mono text-ink">RTS</span>: run number this preparation. FU first-up, 2U second-up, and so on; FS and similar mark a first start in a new stage.</li>
            <li><span className="font-mono text-ink">light</span>: the runner has fewer than three rated runs, so the lighter model was used and the range is wider.</li>
            <li>The bar and the plus-or-minus figure show the likely range (about the middle half of outcomes), not a guarantee.</li>
          </ul>
        </Section>


        <Section title="What goes in">
          <ul className="list-disc space-y-1 pl-5">
            <li>The horse's recent WPRs (last run, last three, last five, career average, peak, how much it varies) and how long since it last ran.</li>
            <li>Its record on this going, at this distance and at this track, and how far today's going and distance are from its last run.</li>
            <li>Weight carried, barrier and field size, race class and the track's usual level.</li>
            <li>Jockey and trainer effects (how their runners have rated against expectation, including this pairing and first-up runners), as at race day.</li>
            <li>Position in the preparation (first up, second up) and its record from there; barrier trials and jump-outs, scaled for the track, distance and going.</li>
            <li>What the stewards and race callers said about its last runs, and how strong the fields it recently beat were.</li>
          </ul>
        </Section>

        <Section title="Base and Adj">
          <p>
            <span className="font-mono text-ink">Base</span> is the main model's projection. <span className="font-mono text-ink">Adj</span> is
            a small suitability adjustment, usually within one WPR point, added to runners on the main model. It looks at how
            often the horse has been held up, raced wide or started slowly, how the track has played earlier on the card,
            the horse's late versus early sectional profile, and whether its jockey and trainer ride it further forward or back
            than its usual style (light-history runners have no suitability adjustment in their projection; the Trip map SM figure still shows an estimate for them from their barrier, the day's track bias and their jockey and trainer, faded because it is lower confidence). <span className="font-mono text-ink">Adj</span> also
            includes weight carried: the model's ratings are weight-free, so each kilo above the field average takes about 0.4
            WPR off, and each kilo below adds the same. That figure was measured on the model's own out-of-sample projections
            (measured on 4,551 out-of-sample races, 90% range 0.35 to 0.47).
            Once three or more races at the meeting have run, Proj also carries a <span className="font-semibold text-ink">draw lean</span>: if the placegetters have come mostly from wide (or inside) barriers, wide runners are lifted and inside runners lowered (or the reverse), about 15 x lean x barrier position, usually under one WPR point and about 2 points between the widest and the inside barriers on a strongly leaning day. It shows as a small draw chip on the runner and in the Draw lean note above the table.
          </p>
        </Section>

        <Section title="How accurate it is">
          <p>
            On races the model had not seen (2024-07 onward) the main model's typical miss was about 9 WPR points
            (RMSE 9.1, average miss 6.1), or about 8 for runners projected at 70 or more, and it was well balanced: the average
            error was close to zero, including on heavy tracks. The light-history model missed by about 11.8 for debutants and
            10 to 10.5 for second and third starters. The plus-or-minus figure on each runner is that typical miss for the model and
            rating level used. Ranking runners within a race works better than the size of any single number.
          </p>
        </Section>

        <Section title="Going and track changes">
          <p>
            Each race is projected on the going recorded for that race, the change in going from the horse's last run and
            the horse's record on that going. When the track condition changes during a meeting, the remaining races are
            re-projected once the change is published, so the figures follow the track.
          </p>
        </Section>

        <Section title="What this doesn't cover">
          <p>
            It does not model the race's pace, the tempo other runners will set or where horses will settle, and in testing
            those added almost nothing to the rating. It is also not a betting edge on its own: added to the market price
            it did not improve winner selection. Use it to rank and compare runners and to see how much to trust each number.
          </p>
        </Section>
      </div>
    </div>
  )
}
