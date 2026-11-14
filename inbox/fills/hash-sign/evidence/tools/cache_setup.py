import datetime
import os
import pathlib
import subprocess

evidence = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
store = pathlib.Path(os.environ.get('XDG_CACHE_HOME', str(pathlib.Path.home() / '.cache'))) / 'mathlib'
files = list(store.rglob('*')) if store.exists() else []
files = [p for p in files if p.is_file()]
with (evidence / 'logs/cache-store.log').open('w') as f:
    print('time:', datetime.datetime.now(datetime.timezone.utc).isoformat(), file=f)
    print('path:', store, 'exists:', store.exists(), file=f)
    print('files:', len(files), 'bytes:', sum(p.stat().st_size for p in files), file=f)
    print('Any existing archives predate this session; origin unknown.', file=f)
roots = (evidence / 'inputs/roots.txt').read_text().splitlines()
env = dict(os.environ, TAR_OPTIONS='--no-same-owner')
with (evidence / 'logs/cache-get.log').open('w') as f:
    print('roots:', len(roots), 'start:', datetime.datetime.now(datetime.timezone.utc).isoformat(), file=f, flush=True)
    p = subprocess.run(['lake', 'exe', 'cache', 'get'] + roots, cwd=repo, env=env, stdout=f, stderr=subprocess.STDOUT)
    print('exit:', p.returncode, 'end:', datetime.datetime.now(datetime.timezone.utc).isoformat(), file=f)
raise SystemExit(p.returncode)
