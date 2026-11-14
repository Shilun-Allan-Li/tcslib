"""Honor the user's shared-Mac cap; never terminate another worker's process."""
import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

audit = Path(__file__).parent.parent / 'logs' / 'host-slots.jsonl'


def active():
    # macOS truncates comm to 15 characters when args is another output column.
    # Request only pid and comm so executable basenames remain reliable.
    raw = subprocess.check_output(['ps', '-axo', 'pid=,comm='], text=True)
    rows = []
    for line in raw.splitlines():
        fields = line.strip().split(None, 1)
        if len(fields) == 2 and Path(fields[1]).name == 'lean':
            rows.append({'pid': int(fields[0]), 'executable': fields[1]})
    return rows


def record(event, processes, **extra):
    row = dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               event=event, cap=3, reserved_for_dl_crh=0, processes=processes, **extra)
    with audit.open('a') as log:
        log.write(json.dumps(row) + '\n')


command = sys.argv[1:]
if command and command[0] == '--':
    command = command[1:]
if not command:
    rows = active()
    record('observe', rows)
    print(json.dumps(rows))
    sys.exit(0)
while True:
    rows = active()
    record('before-check', rows, command=command)
    if len(rows) < 3:
        break
    print(f'WAIT: {len(rows)} active Lean processes; waiting for shared cap3 capacity', flush=True)
    time.sleep(10)
child = subprocess.Popen(command, start_new_session=True)
record('started', active(), wrapper_pid=child.pid, command=command)
interrupted = False
while child.poll() is None:
    rows = active()
    if len(rows) > 3:
        ours=[]
        for row in rows:
            try:
                if os.getpgid(row['pid']) == child.pid:
                    ours.append(row)
            except ProcessLookupError:
                pass
        if ours:
            record('interrupted-for-cap', rows, wrapper_pid=child.pid,
                   stopped_lean_pids=[r['pid'] for r in ours], command=command)
            print('INTERRUPTED: stopping only our Lean child; preserving the log wrapper',
                  flush=True)
            for row in ours:
                try:
                    os.kill(row['pid'], signal.SIGINT)
                except ProcessLookupError:
                    pass
            interrupted = True
            break
    time.sleep(1)
status = child.wait()
record('finished', active(), wrapper_pid=child.pid, status=status, interrupted=interrupted)
sys.exit(130 if interrupted else status)
