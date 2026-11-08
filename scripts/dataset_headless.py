#!/usr/bin/env python3
"""Run the resumable FABL/TCSlib dataset pipeline without a supervising chat.

Start: python3 scripts/dataset_headless.py --detach
Status: python3 scripts/dataset_headless.py --status
Logs: dataset/.pipeline/headless.log
Stops after the first failed stage; running the start command again resumes caches.
"""
from __future__ import annotations
import argparse
import datetime as dt
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / 'dataset' / '.pipeline'
STATUS = WORK / 'headless-status.json'
LOG = WORK / 'headless.log'


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def save(data):
    temp = STATUS.with_suffix('.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(STATUS)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--detach', action='store_true')
    mode.add_argument('--run', action='store_true', help=argparse.SUPPRESS)
    mode.add_argument('--status', action='store_true')
    ap.add_argument('--from', dest='from_stage', default='references',
                    choices=['references', 'blueprint', 'citations', 'statements', 'difficulty',
                             'informalize', 'dataset', 'verify'], help='first stage to resume')
    ap.add_argument('--without-sources', action='store_true',
                    help='allow proof notes when cited reference texts are unavailable')
    args = ap.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    if args.status:
        if not STATUS.exists():
            print('No headless run started')
            return 0
        state = json.loads(STATUS.read_text())
        state['process_alive'] = alive(state['pid'])
        if state.get('status') == 'running' and not state['process_alive']:
            state['recorded_status'] = 'running'
            state['status'] = 'not-running'
        print(json.dumps(state, indent=2))
        return 0
    if args.detach:
        if STATUS.exists():
            previous = json.loads(STATUS.read_text())
            if previous.get('status') == 'running' and alive(previous['pid']):
                print(f"Already running: PID {previous['pid']}; log: {LOG}")
                return 0
        with LOG.open('a') as log:
            child = [sys.executable, str(Path(__file__).resolve()), '--run', '--from', args.from_stage]
            if args.without_sources:
                child.append('--without-sources')
            process = subprocess.Popen(child,
                                       cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        print(f'Headless runner PID {process.pid}; log: {LOG}')
        return 0
    import fcntl
    lock = (WORK / 'headless.lock').open('w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print('Another headless runner holds the lock', flush=True)
        return 1
    command = [sys.executable, '-u', str(ROOT / 'scripts/dataset_pipeline.py'),
               '--from', args.from_stage, '--source',
               'OD14=' + str(ROOT / 'blueprint/src/references/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf'),
               '--backend', 'codex', '--model', 'gpt-6-luna', '--jobs', '4',
               '--batch-size', '8', '--yes']
    if args.without_sources:
        command.append('--without-sources')
    state = dict(status='running', pid=os.getpid(), started_at=now(),
                 model='gpt-6-luna', command=command, log=str(LOG))
    save(state)
    print(f'\nHeadless dataset run started {state["started_at"]}', flush=True)
    env = dict(os.environ, PROOFMATCH_EXTRACT_JOBS='4',
               PROOFMATCH_CLEANUP_CACHE_MODELS='gpt-6.1-sol')
    try:
        result = subprocess.run(command, cwd=ROOT, env=env)
        state.update(status='complete' if result.returncode == 0 else 'stopped',
                     exit_code=result.returncode, finished_at=now())
        save(state)
        return result.returncode
    except BaseException as error:
        state.update(status='stopped', error=str(error), finished_at=now())
        save(state)
        raise


if __name__ == '__main__':
    sys.exit(main())
