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
            <span className="font-mono text-ink">Rating</span> is the figure each race is ranked on, at the weight carried today (ATW),
            the same scale as the Recent runs table. Where a race has bet signals (see Bets, below) it is a 40 / 60 blend of two things:
            the bet-signal model's win chances turned into ratings (3.66 rating points per unit of log win chance, level taken from the field's average
            WPR projection) and the <span className="font-mono text-ink">WPR projection</span> itself, a machine-learned estimate of the WPR a horse will
            run from its past runs and the conditions, trained on ten years of Australian results (about 845,000 runs). The bet-signal part is informed
            by the market price, so the rating moves a little when the price moves; blending in the projection keeps it from being just the market's
            order. Where a race has no signals yet, Rating is the WPR projection alone, and the line above the table says which is in use.
            Base and Adj below describe the WPR projection.
          </p>
          <p>
            Horses with three or more prior rated runs use the main model. Horses with none, one or two prior runs
            (debut, second and third starters) use a separate light-history model that leans on the trainer, jockey,
            trials and race class instead of form. The runner panel says which one was used.
          </p>
        </Section>

        <Section title="Column and label guide">
          <ul className="list-disc space-y-1 pl-5">
            <li><span className="font-mono text-ink">Rating</span>: the race's ranking figure at today's weight (bet-signal rating where the race has signals, otherwise the WPR projection; the line under the Race heading says which). <span className="font-mono text-ink">Base</span> + <span className="font-mono text-ink">Adj</span> = the WPR projection, which the runner page explains.</li>
            <li><span className="font-mono text-ink">SM</span>: the suitability part of the WPR projection's Adj, relative to this field (green +0.5 or better, red -0.5 or worse). Runners at +0.5 or better do win more often (10.5% for the middle band, 13.9% at +0.5 to +1.0, 20% above +1.0), but the market already prices that: win rates matched the market-implied chances at every band, so SM is a reading aid for the map, not a source of value. It is not part of the bet-signal rating.</li>
            <li><span className="font-mono text-ink">Edge</span> and <span className="font-mono text-ink">Model $</span> (Model $ on wider screens): from the experimental bet-signal model (see Bets, below). Edge is its win chance times the current price, minus 1; Model $ is 1 / its win chance. Blank when the race is not fully drawn and priced.</li>
            <li><span className="font-mono text-ink">Fixed $</span>: the current fixed-odds win price. <span className="font-mono text-ink">FP</span>: finishing position.</li>
            <li><span className="font-mono text-ink">RTS</span>: run number this preparation. FU first-up, 2U second-up, and so on; FS and similar mark a first start in a new stage.</li>
            <li><span className="font-mono text-ink">light</span>: the runner has fewer than three rated runs, so the lighter model was used and the range is wider.</li>
            <li><span className="font-mono text-ink">SELECT / VOL</span>: the runner is a Select or Volume bet from the bet-signal model. The Bets tab lists them with stakes and a scoreboard.</li>
            <li><span className="font-mono text-ink">2 / 4 / 8 from top</span>: the lines show runners within 2, 4 and 8 rating points of the top rated (at today's weight). On the blended rating (1,692 races, July to October 2026) inside 2 holds 2.0 runners a race and about 52% of winners, inside 4 holds 3.4 and 70%, inside 8 holds 6.3 and 93%. On the WPR projection alone (15-month out-of-sample test) the same lines held 2.2 runners and 50%, 3.9 and 70%, 6.9 and 93%. They show where the winners are, not where the value is.</li>
            <li>The bar and the plus-or-minus figure show the likely range (about the middle half of outcomes), not a guarantee.</li>
          </ul>
        </Section>

        <Section title="Bets (experimental)">
          <p>
            The Bets tab and the Model $ / Edge columns come from a separate model that is not the WPR projection. It starts from each runner's
            current market price, corrects it using form, ratings, weight, barrier, jockey and trainer records (measured against the market),
            and returns a win chance. Model $ is 1 / that chance and Edge is the chance times the price, minus 1.
          </p>
          <ul className="list-disc space-y-1 pl-5">
            <li><span className="font-mono text-ink">Consistent blend</span>: the Rating is 40% bet-signal model and 60% WPR projection. Win chance (a softmax of that rating), Model $, Edge and the tiers all use the same blend, so they agree with the Rating column.</li>
            <li><span className="font-mono text-ink">Select</span>: edge above 100%, any price. Staked at 2 units. <span className="font-mono text-ink">Volume</span>: edge above 60%, any price. Staked at 0.25 units. 1 unit is $50.</li>
            <li>These blended thresholds are NOT validated. The pure model (no WPR blend) backtested at about +53% for its Select tier at closing SP, but on 1,693 July to October 2026 races every threshold on the blend lost about 28% to 37% at SP, and its high-edge runners won about half as often as predicted. They are set high only to keep the list short. The Bets tab scoreboard is the real check; judge it over months.</li>
            <li>The earlier WPR-based value signal (rated price against market) lost 30 to 39% at every threshold in testing and has been removed.</li>
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
