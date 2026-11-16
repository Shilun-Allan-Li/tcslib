#!/usr/bin/env python3
"""Record the issued macOS resource checks and compute the binding headroom floor."""
import argparse
import datetime
import json
import os
from pathlib import Path
import re
import subprocess

p = argparse.ArgumentParser()
p.add_argument('--phase', required=True)
a = p.parse_args()
out = Path('evidence/logs') / (a.phase + '-preflight.log')
assert not out.exists(), out
paths = [str(Path.cwd()), '/private/tmp', os.environ.get('TMPDIR', '/private/tmp')]
paths += ['/Users/seyoonr/.codex/worktrees/' + name + '/tcslib-exchange'
          for name in ['sc-yao-a', 'sc-yao-b', 'sc-yao-c', 'sc-yao-delivery']]
commands = [['sysctl', '-n', 'hw.ncpu', 'hw.memsize'], ['vm_stat'],
            ['memory_pressure', '-Q'], ['df', '-k', *paths], ['mount']]
vm = None
with out.open('w') as log:
    log.write('UTC ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '\n')
    for cmd in commands:
        log.write('COMMAND ' + repr(cmd) + '\n')
        log.flush()
        r = subprocess.run(cmd, capture_output=True, text=True)
        log.write(r.stdout + r.stderr + '\nEXIT ' + str(r.returncode) + '\n')
        log.flush()
        if cmd == ['vm_stat']:
            assert r.returncode == 0
            vm = r.stdout
page = int(re.search(r'page size of (\d+) bytes', vm).group(1))
fields = {k: int(re.search('^' + re.escape(k) + r':\s+(\d+)', vm, re.M).group(1))
          for k in ['Pages free', 'Pages inactive', 'Pages speculative', 'Pages purgeable']}
headroom = sum(fields.values()) * page
disk = os.statvfs(Path.cwd())
free_disk = disk.f_bavail * disk.f_frsize
record = dict(page_size=page, pages=fields, headroom_bytes=headroom,
    headroom_GiB=headroom / 2**30, memory_floor_GiB=4, disk_available_bytes=free_disk,
    disk_available_GiB=free_disk / 2**30, disk_floor_GiB=12,
    slot_directory_override=os.environ.get('LEAN_SLOT_DIR'),
    slot_count_override=os.environ.get('LEAN_SLOTS'))
with out.open('a') as log:
    log.write(json.dumps(record) + '\n')
out.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
assert headroom >= 4 * 2**30, 'E-RES: headroom below 4 GiB'
assert free_disk >= 12 * 2**30, 'E-RES: available disk below 12 GiB'
