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

function Term({
  name,
  fires,
  children,
}: {
  name: string
  fires: string
  children: React.ReactNode
}) {
  return (
    <div className="rounded-md border border-line-soft p-2.5">
      <div className="mb-0.5 flex items-baseline justify-between gap-2">
        <span className="font-mono text-xs font-semibold text-emerald-deep">{name}</span>
        <span className="text-[11px] text-ink-faint">{fires}</span>
      </div>
      <p className="text-xs text-ink-soft">{children}</p>
    </div>
  )
}

function Step({ label, value }: { label: string; value: string }) {
  return (
    <div className="flex items-baseline justify-between gap-3 border-b border-line-soft/60 py-1 text-xs last:border-0">
      <span className="text-ink-mute">{label}</span>
      <span className="font-mono text-ink">{value}</span>
    </div>
  )
}

// A dedicated page (styled as a full modal, matching RunnerDetailModal's
// pattern) explaining the WPR projection's actual math - not a marketing
// summary, the real formulas from wpr_projection.py, illustrated with a
// real runner's real numbers rather than a made-up example. Linked from
// Settings (user request, Aug 2026: "a page that explains in full detail
// the methodology... include a walkthrough example... using actual data").
//
// The worked example (Chiaro Di Luna, Mackay 2026-07-25) was picked
// because five of the seven adjustment terms fire for it at once - a
// richer single example than most runners give. Every number below was
// pulled directly from that runner's actual stored projection (wpjcb/wpjd
// in the payload) and cross-checked against wpr_projection.py's own
// build_features() output for the same horse/date, not reconstructed by
// hand - base + adjustments sums to exactly its real projected WPR (71.5).
// The two supplementary examples (own_second_up, own_trend) are real
// runners too, picked because Chiaro Di Luna doesn't trigger those two
// terms itself (not second-up, not lightly-raced).
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
            <span className="font-mono text-ink">Projected WPR = Base + Adjustment</span>. Base is the horse's own
            anchor rating for today. Adjustment is a sum of up to seven small, explainable nudges, each answering
            one plain-English question about this specific horse and this specific race - no fitted regression,
            no hidden coefficients. What the runner detail panel shows in its breakdown table <em>is</em> the whole
            calculation, not a summary of one.
          </p>
        </Section>

        <Section title="The base rating">
          <p>A 50/50 blend of two numbers that already exist elsewhere in the pipeline:</p>
          <ul className="list-disc space-y-1 pl-5">
            <li>
              <strong className="text-ink">TopRate's own rating</strong> for the horse going into today's race
              (its <code className="font-mono text-xs">wpr_nett</code> figure).
            </li>
            <li>
              <strong className="text-ink">This horse's own recent form</strong> - an exponentially-weighted
              average of its last few runs, so its latest run counts for more than one from further back.
            </li>
          </ul>
          <p>
            If only one of the two is available (TopRate hasn't rated it yet, or it doesn't have enough of its own
            history), the base falls back to whichever half exists, then to a plain average of its last three runs,
            then to its career average - in that order.
          </p>
        </Section>

        <Section title="The adjustment: your horse's own history">
          <p>
            Six of the seven terms below ask the same shape of question: <em>does this horse personally run above
            or below its own level under this specific condition</em> (this trip, this going, first-up, etc.),
            using only that horse's own prior runs - never another horse's. Each is computed the same way:
          </p>
          <ol className="list-decimal space-y-1 pl-5">
            <li>Find this horse's average WPR in its prior runs that match today's condition.</li>
            <li>Subtract its overall career average - this is the raw, unshrunk delta.</li>
            <li>
              Shrink it by how many matching runs actually back it up:{' '}
              <code className="font-mono text-xs">shrunk = delta &times; n / (n + 3)</code>. One matching run gets
              only a quarter of its raw delta (1/4 = 0.25); ten matching runs get about three-quarters
              (10/13 &asymp; 0.77); the more evidence, the closer to the full, unshrunk number.
            </li>
            <li>
              Cap the result to &plusmn;3.0 - a single term is never allowed to swing the projection by more than
              that on its own.
            </li>
          </ol>
          <p>
            If several terms fire strongly at once (say, a lightly-raced horse that's both improving fast and
            first-up), their capped values are summed and, only if that sum exceeds &plusmn;6.0 in total, every
            nonzero term for that runner is scaled down by the same factor so they still sum to exactly that limit
            - proportions between terms are preserved, so the breakdown table always adds up to the total shown
            next to it.
          </p>
        </Section>

        <Section title="The seven terms">
          <div className="grid gap-2 sm:grid-cols-2">
            <Term name="own_distance" fires="always, if it's raced at this exact distance before">
              This horse's average WPR at exactly today's distance (not a band - the exact metres), vs its career
              average.
            </Term>
            <Term name="own_going" fires="always, if it's raced in this going band before">
              Same idea for going, banded into Firm / Good / Soft / Heavy.
            </Term>
            <Term name="own_first_up" fires="only when today is its first run back from a spell">
              How this horse has historically performed specifically first-up, vs its career average. Zero on
              every other run.
            </Term>
            <Term name="own_second_up" fires="only when today is its second run of the campaign">
              Same idea, for second-up.
            </Term>
            <Term name="own_trend" fires="only for lightly-raced horses (4-6 career starts)">
              Is it trending up or down across its short career so far - second half of its runs vs the first
              half. An established horse's trend is already captured by its recent-form average in Base, so this
              only applies while there's too little history for that to mean much yet.
            </Term>
            <Term name="own_long_spell" fires="only after a break of 180+ days">
              Does this horse specifically run below (or above) its own level after a genuinely long layoff -
              well beyond an ordinary first-up gap.
            </Term>
          </div>
          <div className="mt-2 rounded-md border border-line-soft p-2.5">
            <div className="mb-0.5 flex items-baseline justify-between gap-2">
              <span className="font-mono text-xs font-semibold text-emerald-deep">track_barrier</span>
              <span className="text-[11px] text-ink-faint">always, using today's barrier and field size</span>
            </div>
            <p className="text-xs text-ink-soft">
              The one term that is <em>not</em> about this horse's own history. Fitted once, across every horse
              that has ever raced at a given track and trip, checking whether an inside/mid/wide barrier draw
              (barrier &divide; field size) has historically gone better or worse there than the field-wide
              average - after removing each horse's own quality first, so it can't just be re-learning "this is a
              good horse" through barrier. Shrunk toward the pooled average with a much larger shrinkage constant
              (300 rather than 3, since a track+trip+barrier combination needs to show up across many different
              horses before the model trusts the pattern), and re-centered per track+trip so it can never become
              a flat "this track is good" bias - a wide-draw-friendly track shifts inside draws down and wide
              draws up, not everything up together.
            </p>
          </div>
        </Section>

        <Section title="Worked example: Chiaro Di Luna, Mackay, 25 Jul 2026">
          <p>
            A real runner, picked because five of the seven terms fire for it at once. Barrier 3 of 10, 1100m,
            Good 4, first-up off a 263-day spell. Every number below is exactly what the model produced for this
            runner - the total really does add up to its real projected WPR.
          </p>

          <div className="rounded-md border border-line-soft p-2.5">
            <div className="mb-1 text-xs font-semibold text-ink">Base</div>
            <Step label="TopRate's rating" value="68.9" />
            <Step label="Recent-form average (last ~3 runs)" value="63.3" />
            <Step label="Base = (68.9 + 63.3) / 2" value="66.1" />
          </div>

          <div className="mt-2 rounded-md border border-line-soft p-2.5">
            <div className="mb-1 text-xs font-semibold text-ink">
              Career reference: 38 prior runs, 2 discounted for interference/vet issues &rarr; career average 67.0
            </div>

            <div className="mt-2">
              <div className="text-[11px] font-semibold text-ink-mute">own_distance</div>
              <Step label="9 of those runs were at exactly 1100m, averaging" value="64.4" />
              <Step label="Raw delta: 64.4 &minus; 67.0" value="&minus;2.6" />
              <Step label="Shrink factor: 9 / (9 + 3)" value="0.75" />
              <Step label="Shrunk: &minus;2.6 &times; 0.75" value="&minus;1.9 (stored: &minus;1.93)" />
            </div>

            <div className="mt-2">
              <div className="text-[11px] font-semibold text-ink-mute">own_going</div>
              <Step label="26 of those runs were in the same Good band, averaging" value="69.7" />
              <Step label="Raw delta: 69.7 &minus; 67.0" value="+2.7" />
              <Step label="Shrink factor: 26 / (26 + 3)" value="0.90" />
              <Step label="Shrunk: 2.7 &times; 0.90" value="+2.4 (stored: +2.44)" />
            </div>

            <div className="mt-2">
              <div className="text-[11px] font-semibold text-ink-mute">own_first_up</div>
              <Step label="4 prior first-up runs, averaging" value="69.7" />
              <Step label="Raw delta: 69.7 &minus; 67.0" value="+2.7" />
              <Step label="Shrink factor: 4 / (4 + 3)" value="0.57" />
              <Step label="Shrunk: 2.7 &times; 0.57" value="+1.5 (stored: +1.53)" />
            </div>

            <div className="mt-2">
              <div className="text-[11px] font-semibold text-ink-mute">own_second_up, own_trend</div>
              <p className="text-xs text-ink-soft">
                Zero - today isn't this horse's second-up run, and with 38 career starts it isn't lightly-raced
                either. See the two examples below for real runners where these fire.
              </p>
            </div>

            <div className="mt-2">
              <div className="text-[11px] font-semibold text-ink-mute">own_long_spell</div>
              <p className="text-xs text-ink-soft">
                Today's 263-day gap clears the 180-day threshold, and this horse has a real history of running
                above its level after long layoffs before. Lands at exactly the per-term cap, +3.0 - its raw
                shrunk value would have been even larger before that ceiling applied.
              </p>
            </div>

            <div className="mt-2">
              <div className="text-[11px] font-semibold text-ink-mute">track_barrier</div>
              <Step label="Barrier 3 of 10 runners &rarr; relative draw 3/10" value="0.30 (Inside third)" />
              <Step label="Mackay, 1000-1199m band, Inside barriers &rarr; looked up" value="+0.40" />
            </div>
          </div>

          <div className="mt-2 rounded-md border border-emerald-line bg-emerald-bg p-2.5">
            <Step label="Total adjustment: &minus;1.93 + 2.44 + 1.53 + 0 + 0 + 3.00 + 0.40" value="+5.4" />
            <Step label="Projected WPR: 66.1 + 5.4" value="71.5" />
            <p className="mt-1 text-[11px] text-ink-mute">
              Matches this runner's real, live projected WPR exactly.
            </p>
          </div>
        </Section>

        <Section title="Two more real examples">
          <div className="rounded-md border border-line-soft p-2.5">
            <div className="mb-1 text-xs font-semibold text-ink">
              own_second_up &mdash; Larado, 25 Jul 2026: why one data point barely moves the needle
            </div>
            <Step label="Only 1 prior second-up run on record, at" value="89.8" />
            <Step label="Its career average is around" value="82.1" />
            <Step label="Raw delta: 89.8 &minus; 82.1" value="+7.7" />
            <Step label="Shrink factor with n=1: 1 / (1 + 3)" value="0.25" />
            <Step label="Shrunk: 7.7 &times; 0.25" value="+1.9 (stored: +1.92)" />
            <p className="mt-1 text-xs text-ink-soft">
              A single matching run is mostly noise dressed up as a personal pattern, so it only ever gets a
              quarter of its raw weight - three-quarters of that dramatic +7.7 gap gets discounted away.
            </p>
          </div>

          <div className="mt-2 rounded-md border border-line-soft p-2.5">
            <div className="mb-1 text-xs font-semibold text-ink">
              own_trend &mdash; Final Spirit, 25 Jul 2026: a lightly-raced horse's trajectory
            </div>
            <Step label="Its 5 recorded WPRs in order" value="62.9, 63.6, 62.9, 65.8, 65.1" />
            <Step label="Earlier half average (first 2)" value="63.3" />
            <Step label="Recent half average (last 2)" value="65.5" />
            <Step label="Raw delta: 65.5 &minus; 63.3" value="+2.2" />
            <Step label="Shrink factor with n=5: 5 / (5 + 3)" value="0.625" />
            <Step label="Shrunk: 2.2 &times; 0.625" value="+1.4 (stored: +1.37)" />
            <p className="mt-1 text-xs text-ink-soft">
              Only applies for 4-6 career starts. A horse with a longer record has this same "is it trending"
              question already answered by the recency-weighted average that feeds Base, so own_trend stays at
              zero for it.
            </p>
          </div>
        </Section>

        <Section title="What this doesn't cover">
          <p>
            This is a form-quality projection built from each horse's own history plus one population-level
            barrier effect - it doesn't model race pace, other runners' likely tempo, or anything about the
            field beyond field size. It ranks horses and rates how much to trust each number; it isn't a proven
            betting edge. Held-out testing puts the typical projection within about 5.9 WPR points of the actual
            result - useful for ranking and comparison, not a promise of precision on any single runner.
          </p>
        </Section>
      </div>
    </div>
  )
}
