// TopRate service worker: makes the dashboard installable and lets it open with the last data when the network is down.
// Network first for everything, so a normal load always gets the newest page and data. The cache is only the fallback.
// The big history file is never cached here (tens of MB); the page already treats it as optional.
const CACHE = 'toprate-v1'
const SHELL = ['toprate_live.html', 'manifest.webmanifest', 'icon-192.png']

self.addEventListener('install', (event) => {
  event.waitUntil(caches.open(CACHE).then((c) => c.addAll(SHELL)).catch(() => {}))
  self.skipWaiting()
})

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches
      .keys()
      .then((keys) => Promise.all(keys.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
      .then(() => self.clients.claim()),
  )
})

function cacheable(url) {
  const path = new URL(url).pathname
  if (path.endsWith('toprate_history.json') || path.endsWith('toprate_history.json.gz')) return false
  return /\.(html|webmanifest|png|svg)$/.test(path) || path.endsWith('toprate_data.json') || path.endsWith('toprate_data.json.gz') || path.endsWith('trip_map.json')
}

self.addEventListener('fetch', (event) => {
  const req = event.request
  if (req.method !== 'GET') return
  const url = new URL(req.url)
  if (url.origin !== self.location.origin || !cacheable(req.url)) return
  event.respondWith(
    fetch(req)
      .then((res) => {
        if (res.ok && res.status === 200) {
          const copy = res.clone()
          caches.open(CACHE).then((c) => c.put(req, copy)).catch(() => {})
        }
        return res
      })
      .catch(() => caches.match(req, { ignoreSearch: true }).then((hit) => hit || Response.error())),
  )
})
