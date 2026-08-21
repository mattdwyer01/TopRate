import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import tailwindcss from '@tailwindcss/vite'
import { viteSingleFile } from 'vite-plugin-singlefile'

// GitHub Pages serves this repo from https://mattdwyer01.github.io/TopRate/,
// so the built page needs to know it lives under the /TopRate/ subpath.
// vite-plugin-singlefile inlines JS/CSS into one file (matching the current
// single toprate_live.html artifact - see the rebuild plan for why), so
// `base` mostly only matters if something ever isn't inlined (e.g. a future
// external asset). Runtime data loading (toprate_data.json) is fetched with
// a path relative to the page, so it is unaffected by `base` either way.
export default defineConfig({
  base: '/TopRate/',
  plugins: [react(), tailwindcss(), viteSingleFile()],
  build: {
    // vite-plugin-singlefile needs a single entry, single chunk build.
    cssCodeSplit: false,
  },
})
