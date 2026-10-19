"""Run all tests in order (features are cached in .cache/; delete it to rebuild)."""
import subprocess, sys, os
here = os.path.dirname(os.path.abspath(__file__))
for t in ('t1_class_par.py', 't2_xr_tof.py', 't3_compression.py', 't4_golden8.py', 't5_sanity.py'):
    print('running', t, flush=True)
    subprocess.run([sys.executable, os.path.join(here, t)], check=True, stdout=subprocess.DEVNULL)
