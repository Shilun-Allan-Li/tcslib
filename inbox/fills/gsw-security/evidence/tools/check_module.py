"""One Lean module check, logged with start/end time and peak child memory.

Usage (from the fill checkout's root, run with python3 -I):
    check_module.py [--maxerrors0] <module-path-without-.lean> <log>
Without --maxerrors0 it runs scripts/lean_check_tree.sh unchanged. With --maxerrors0 it
runs evidence/tools/lean_check_tree_maxerrors0.sh, which differs from the script only in
passing -DmaxErrors=0 to lean and failing on both `error:` and `error(` (seals, controls,
probes). /usr/bin/time is absent on this host, so the peak resident set size is
resource.getrusage(RUSAGE_CHILDREN).ru_maxrss of the finished check (KiB). Called serially:
one Lean process at a time.
"""
import datetime, os, re, resource, subprocess, sys
from pathlib import Path

args = sys.argv[1:]
d0 = args and args[0] == '--maxerrors0'
if d0:
    args = args[1:]
mod, log = args
here = Path(__file__).resolve().parent
script = str(here / 'lean_check_tree_maxerrors0.sh') if d0 else 'scripts/lean_check_tree.sh'
Path(log).parent.mkdir(parents=True, exist_ok=True)
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='milliseconds')
with open(log, 'w') as f:
    f.write(f'START {now()} {mod}\nCOMMAND bash {script} {mod}\n'); f.flush()
    p = subprocess.run(['bash', script, mod], stdout=f, stderr=subprocess.STDOUT)
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    f.write(f'END {now()} {mod} EXIT {p.returncode} MAXRSS_KIB {rss}\n')
text = Path(log).read_text()
errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', text, re.M))
sorr = len(re.findall(r"declaration uses 'sorry'", text))
print(f'{mod} exit={p.returncode} errors={errs} sorry_warnings={sorr} maxrss_kib={rss}', flush=True)
sys.exit(p.returncode)
