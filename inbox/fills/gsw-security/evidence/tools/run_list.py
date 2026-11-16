"""Check each module of a list serially through check_module.py; stop at the first failure.
Usage: run_list.py [--maxerrors0] <list> <logdir> <summary-log>  (from the checkout root)"""
import subprocess, sys
from pathlib import Path
args = sys.argv[1:]
flag = []
if args[0] == '--maxerrors0':
    flag, args = ['--maxerrors0'], args[1:]
lst, logdir, summary = args
tool = Path(__file__).resolve().parent / 'check_module.py'
mods = [l.strip() for l in open(lst) if l.strip()]
with open(summary, 'a') as s:
    for i, m in enumerate(mods, 1):
        log = f'{logdir}/{m.replace("/", "_")}.log'
        p = subprocess.run(['python3', '-I', str(tool), *flag, m, log],
                           capture_output=True, text=True)
        s.write(f'[{i}/{len(mods)}] {p.stdout.strip()}\n'); s.flush()
        if p.returncode != 0:
            s.write(f'STOP at {m}\n'); sys.exit(1)
    s.write(f'ALL {len(mods)} OK\n')
