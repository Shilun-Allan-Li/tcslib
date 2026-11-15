import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import time

pid = 15550
root = '/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange'
log = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange/evidence/logs/cache-window.jsonl')
command = subprocess.check_output(['ps', '-p', str(pid), '-o', 'command='], text=True).strip()
assert 'Python -I evidence/tools/check_modules.py checkpoint1-full ' in command
cwd = subprocess.check_output(['lsof', '-a', '-p', str(pid), '-d', 'cwd', '-Fn'], text=True)
assert '\nn' + root + '\n' in cwd

def record(event):
    row = dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(), event=event, pid=pid)
    with log.open('a') as dest:
        print(json.dumps(row), file=dest)
    print(json.dumps(row), flush=True)

os.kill(pid, signal.SIGSTOP)
try:
    record('own-verification-dispatcher-paused-for-cache-window')
    time.sleep(40)
finally:
    os.kill(pid, signal.SIGCONT)
    record('own-verification-dispatcher-resumed')
