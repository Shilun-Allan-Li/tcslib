"""Yield only derand's own dispatchers; never stop a native Lean child."""
import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import time

pids = [15550, 23834]
roots = ['/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange',
         '/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange']
log = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange/evidence/logs/courtesy-gap.jsonl')

def record(event, **fields):
    row = dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(), event=event, **fields)
    with log.open('a') as dest:
        print(json.dumps(row), file=dest)
    print(json.dumps(row), flush=True)

def processes():
    lines = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,command='], text=True).splitlines()
    return {int(parts[0]): parts[2] for line in lines if len(parts := line.strip().split(None, 2)) == 3}

stopped = []
try:
    table = processes()
    for pid in pids:
        command = table.get(pid, '')
        assert 'Python -I evidence/tools/check_modules.py ' in command, (pid, command)
        assert (' checkpoint1-full ' in command or ' host-word-bootstrap ' in command), command
        cwd = subprocess.check_output(['lsof', '-a', '-p', str(pid), '-d', 'cwd', '-Fn'], text=True)
        assert any('\nn' + root + '\n' in cwd for root in roots), cwd
        os.kill(pid, signal.SIGSTOP)
        stopped.append(pid)
        record('dispatcher-paused', pid=pid, command=command)
    deadline = time.monotonic() + 300
    while time.monotonic() < deadline:
        active = [(pid, command) for pid, command in processes().items()
                  if command.startswith('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/bin/lean ')
                  and any(' -o ' + root + '/.lake/' in command for root in roots)]
        if not active:
            record('own-native-checks-finished')
            time.sleep(12)
            record('twelve-second-acquisition-gap-complete')
            break
        time.sleep(0.5)
    else:
        record('long-check-still-active-gap-deferred')
finally:
    for pid in stopped:
        try:
            os.kill(pid, signal.SIGCONT)
            record('dispatcher-resumed', pid=pid)
        except ProcessLookupError:
            record('dispatcher-already-finished', pid=pid)
