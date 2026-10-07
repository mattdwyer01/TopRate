import { useState } from 'react'
import { LIVE_CHANNELS, isStreamUrl, useLiveStreams } from '../lib/liveVision'
import type { LiveChannel } from '../lib/liveVision'

// Settings block for the live-vision stream addresses. Saved on blur, only in this browser (never synced, never in the repo).
export function LiveVisionSettings() {
  const [streams, setStream] = useLiveStreams()
  const [drafts, setDrafts] = useState<Partial<Record<LiveChannel, string>>>({})
  return (
    <div className="flex flex-col gap-2 p-4">
      <span className="text-sm font-semibold text-ink">Live vision</span>
      <p className="text-xs text-ink-mute">
        Paste a stream address (an https link ending in .m3u8) for each channel you want. They are kept only in this browser and are not synced
        or sent anywhere. Once one is saved, a "Watch live" button appears on today's races. You are responsible for having the right to watch
        what you add.
      </p>
      {LIVE_CHANNELS.map(({ key, label }) => {
        const value = drafts[key] ?? streams[key] ?? ''
        const bad = value.trim() !== '' && !isStreamUrl(value)
        return (
          <label key={key} className="flex flex-col gap-1 text-xs text-ink-soft">
            <span className="flex items-center gap-2">
              {label}
              {streams[key] && !bad && <span className="font-semibold text-emerald-deep">Saved</span>}
            </span>
            <input
              type="url"
              inputMode="url"
              autoCapitalize="off"
              autoCorrect="off"
              spellCheck={false}
              placeholder="https://.../index.m3u8"
              value={value}
              onChange={(e) => {
                const v = e.target.value
                setDrafts((d) => ({ ...d, [key]: v }))
                // save as soon as the address is valid (a phone paste + closing Settings never blurs the box)
                if (isStreamUrl(v)) setStream(key, v)
              }}
              onBlur={() => {
                const v = (drafts[key] ?? streams[key] ?? '').trim()
                // an invalid address stays in the box with its error so it can be fixed; a valid or empty one is saved
                if (v !== '' && !isStreamUrl(v)) return
                setStream(key, v)
                setDrafts((d) => {
                  const { [key]: _drop, ...rest } = d
                  return rest
                })
              }}
              className={`rounded-md border bg-panel px-2 py-1.5 text-sm text-ink ${bad ? 'border-rose' : 'border-line'}`}
            />
            {bad && <span className="text-rose">Needs to be an https address ending in .m3u8</span>}
          </label>
        )
      })}
    </div>
  )
}
