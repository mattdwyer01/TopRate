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
            <span className="font-mono text-ink">Proj</span> is the WPR projection: a machine-learned estimate of the WPR a horse will run from its
            past runs and the conditions, trained on ten years of Australian results. It is shown at the weight carried today (ATW), the same scale as the
            Recent runs table, and it is the figure each race is ranked on. Base and Adj below describe it. <span className="font-mono text-ink">Rated $</span> is
            the price that projection implies for each runner, from a simulation of the race in which every runner's true figure is its projection plus noise (larger for horses with little history); hover it for the place price. It is the model's view, not a betting price.
          </p>
          <p>
            Horses with three or more prior rated runs use the main model. Horses with none, one or two prior runs
            (debut, second and third starters) use a separate light-history model that leans on the trainer, jockey,
            trials and race class instead of form. The runner panel says which one was used.
          </p>
        </Section>

        <Section title="Column and label guide">
          <ul className="list-disc space-y-1 pl-5">
            <li><span className="font-mono text-ink">Proj</span>: the WPR projection at the weight carried today, and the race's ranking figure. <span className="font-mono text-ink">Base</span> + <span className="font-mono text-ink">Adj</span> = the projection, which the runner page explains.</li>
            <li><span className="font-mono text-ink">SM</span>: the suitability part of the WPR projection's Adj, relative to this field (green +0.5 or better, red -0.5 or worse). Runners at +0.5 or better do win more often (10.5% for the middle band, 13.9% at +0.5 to +1.0, 20% above +1.0), but the market already prices that: win rates matched the market-implied chances at every band, so SM is a reading aid for the map, not a source of value.</li>
            <li><span className="font-mono text-ink">Rated $</span>: the price the projection implies, from a softmax over the field's projections. It is the model's own view of the race, not a value claim: the earlier rated-price-against-market signal lost 30 to 39% at every threshold in testing.</li>
            <li><span className="font-mono text-ink">Fixed $</span>: the current fixed-odds win price. <span className="font-mono text-ink">FP</span>: finishing position.</li>
            <li><span className="font-mono text-ink">RTS</span>: run number this preparation. FU first-up, 2U second-up, and so on; FS and similar mark a first start in a new stage.</li>
            <li><span className="font-mono text-ink">light</span>: the runner has fewer than three rated runs, so the lighter model was used and the range is wider.</li>
            <li><span className="font-mono text-ink">2 / 4 from top</span>: the dotted line marks runners within 2 rating points of the top rated, the solid line within 4. Inside 4 holds about 3.4 runners a race and 68% of winners; inside 2 holds about 2.0 and 49%. They show where the winners are, not where the value is.</li>
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
            than its usual style (light-history runners have no suitability adjustment in their projection; the SM column still shows an estimate for them from their barrier, the day's track bias and their jockey and trainer, faded because it is lower confidence). <span className="font-mono text-ink">Adj</span> also
            includes weight carried: the model's ratings are weight-free, so each kilo above the field average takes about 0.4
            WPR off, and each kilo below adds the same. That figure was measured on the model's own out-of-sample projections
            (measured on 4,551 out-of-sample races, 90% range 0.35 to 0.47).
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
