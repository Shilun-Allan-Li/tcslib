import datetime
import os
from pathlib import Path
import re
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
dest = root / "evidence/logs/preflight.log"
scratch = [root, Path('/private/tmp'), Path(os.environ.get('TMPDIR', '/private/tmp'))]
scratch.extend(Path(p).resolve() for p in sys.argv[2:])
with dest.open('a') as log:
    def record(s):
        print(s, flush=True)
        print(s, file=log, flush=True)

    def run(args):
        record('$ ' + ' '.join(map(str, args)))
        p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        record(p.stdout.rstrip())
        record('exit=' + str(p.returncode))
        return p

    record('UTC ' + datetime.datetime.now(datetime.timezone.utc).isoformat())
    cpu = run(['sysctl', '-n', 'hw.ncpu', 'hw.memsize'])
    vm = run(['vm_stat'])
    pressure = run(['memory_pressure', '-Q'])
    disk = run(['df', '-k'] + list(map(str, scratch)))
    run(['mount'])
    page_size = int(re.search(r'page size of (\d+) bytes', vm.stdout)[1])
    counts = {}
    for label in ['free', 'inactive', 'speculative', 'purgeable']:
        counts[label] = int(re.search(r'Pages ' + label + r':\s+(\d+)', vm.stdout)[1])
    headroom = sum(counts.values()) * page_size
    record(f'HEADROOM: {counts}; sum={sum(counts.values())} pages * {page_size} '
           f'bytes/page = {headroom} bytes = {headroom / 2**30:.6f} GiB')
    available = int(disk.stdout.splitlines()[1].split()[3]) * 1024
    record(f'DISK: {available} bytes = {available / 2**30:.6f} GiB')
    passed = cpu.returncode == 0 and headroom >= 4 * 2**30 and available >= 12 * 2**30
    record('PREFLIGHT ' + ('PASS' if passed else 'FAIL'))
    sys.exit(0 if passed else 1)
