"""Courtesy pause of this unit's dispatchers; never signal a native Lean process."""
import datetime
from pathlib import Path
import os
import signal
import subprocess
import time

tokens = [
    ' -I evidence/tools/check_modules.py base-bootstrap '
    'evidence/inputs/issued/outbox/fills/derand-r2/order.txt',
    ' -I evidence/tools/check_modules.py checkpoint1-bootstrap '
    'evidence/logs/checkpoint1-bootstrap-order.txt',
]
out = Path('evidence/logs/coordination-yield-01.log')
with out.open('w') as log:
    def record(msg):
        print(datetime.datetime.now(datetime.timezone.utc).isoformat(), msg, file=log, flush=True)
    rows = subprocess.check_output(['ps', '-axo', 'pid=,comm=,args='], text=True).splitlines()
    pids = []
    for row in rows:
        parts = row.split(None, 2)
        if len(parts) == 3 and parts[1].endswith('/Python'):
            if any(token in parts[2] for token in tokens):
                pids.append(int(parts[0]))
                record('Owned dispatcher: ' + row.strip())
    assert 1 <= len(pids) <= 2, pids
    stopped = []
    try:
        for pid in pids:
            os.kill(pid, signal.SIGSTOP)
            stopped.append(pid)
            record(f'Paused dispatcher {pid}; child native checks finish normally')
        time.sleep(40)
    finally:
        for pid in stopped:
            try:
                os.kill(pid, signal.SIGCONT)
                record(f'Resumed dispatcher {pid}')
            except ProcessLookupError:
                record(f'Dispatcher {pid} exited before resume')
print(out.read_text())
