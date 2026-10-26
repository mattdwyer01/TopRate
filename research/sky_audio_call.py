"""Sky replay audio: transcribe the race call with word timestamps, primed with the race's declared runner names.
usage: PYTHONPATH=. python research/sky_audio_call.py OUT_DIR MODEL  (races listed in RACES below)
Writes OUT_DIR/{race}.json = {"field": [[tab, name], ...], "segments": [[start, end, text], ...]}.
Each video is downloaded, its audio extracted and the video deleted, so disk use stays small.
"""
import json, os, subprocess, sys, time, wave, urllib.request
import numpy as np
from faster_whisper import WhisperModel

RACES = [('20261024', 'FLER', 'Flemington', '2026-10-24', n) for n in range(1, 10)] + \
        [('20261024', 'MOPR', 'Morphettville', '2026-10-24', n) for n in range(1, 10)] + \
        [('20261017', 'CAUR', 'Caulfield', '2026-10-17', n) for n in (1, 2)]


def field(venue, date, race):
    j = json.load(open('toprate_history.json'))
    for r in j['RACES']:
        if r['venue'] == venue and r['date'] == date and r['race'] == race:
            return [[x['tab'], x['h']] for x in r['runners'] if not x.get('scr')]
    return []


def main():
    out, model = sys.argv[1], (sys.argv[2] if len(sys.argv) > 2 else 'base.en')
    os.makedirs(out, exist_ok=True)
    m = WhisperModel(model, compute_type='int8')
    for d, code, venue, iso, n in RACES:
        name = f'{d}{code}{n:02d}'
        fn = f'{out}/{name}.json'
        if os.path.exists(fn):
            continue
        t0 = time.time()
        mp4, wav = f'/tmp/{name}.mp4', f'/tmp/{name}.wav'
        urllib.request.urlretrieve(f'https://mediatabs.skyracing.com.au/Race_Replay/{d[:4]}/{d[4:6]}/{name}_V.mp4', mp4)
        subprocess.run(['ffmpeg', '-v', 'error', '-y', '-i', mp4, '-vn', '-ac', '1', '-ar', '16000', wav], check=True)
        os.remove(mp4)
        w = wave.open(wav)
        a = np.frombuffer(w.readframes(w.getnframes()), np.int16).astype(np.float32) / 32768
        os.remove(wav)
        fld = field(venue, iso, n)
        prompt = 'Horse racing call. Runners: ' + ', '.join(x[1] for x in fld) + '.'
        seg, _ = m.transcribe(a, language='en', initial_prompt=prompt, word_timestamps=True)
        segs = []
        for s in seg:
            segs.append([round(s.start, 2), round(s.end, 2), s.text.strip(),
                         [[round(x.start, 2), round(x.end, 2), x.word.strip()] for x in (s.words or [])]])
        json.dump({'field': fld, 'segments': segs}, open(fn, 'w'))
        print(name, len(fld), 'runners', len(segs), 'segments', round(time.time() - t0), 's', flush=True)


if __name__ == '__main__':
    main()
