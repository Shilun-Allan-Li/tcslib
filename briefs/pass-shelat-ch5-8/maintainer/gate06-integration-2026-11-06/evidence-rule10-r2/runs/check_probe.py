"""Run one probe through the campaign script, retaining its exact source and diagnostics.

Usage: python3 -I check_probe.py <evidence-dir> <probe-module-without-suffix> <new-label>
The root coordinator is responsible for serializing all Lean commands.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

r = Path.cwd()
out, module, label = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
out.mkdir(parents=True, exist_ok=True)
log = out / (label + '.log')
assert not log.exists(), 'Do not overwrite a probe attempt'
source = r / (module + '.lean')
raw = source.read_bytes()
(out / (label + '.source.txt')).write_bytes(raw)
env = os.environ.copy()
env['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + env['PATH']
run = r / 'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-run'
env['TCSLIB_OLEANS'] = json.loads((run / 'setup-summary.json').read_text())['olean_tree']
clock = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
start, tick = clock(), time.monotonic()
with log.open('w') as handle:
    handle.write('START ' + start + '\nSOURCE_SHA256 ' + hashlib.sha256(raw).hexdigest() + '\n')
    handle.flush()
    proc = subprocess.Popen(['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', module], env=env, stdout=handle, stderr=subprocess.STDOUT)
    (out / (label + '.pid')).write_text(str(proc.pid) + '\n')
    rc = proc.wait()
    end = clock()
    handle.write('\nEND ' + end + ' RC ' + str(rc) + '\n')
obj = Path(env['TCSLIB_OLEANS']) / (module + '.olean')
text = log.read_text()
rss = re.search(r'(\d+)\s+maximum resident set size', text)
result = {'module': module, 'label': label, 'start': start, 'end': end, 'elapsed_seconds': round(time.monotonic()-tick, 3), 'rc': rc, 'source_sha256': hashlib.sha256(raw).hexdigest(), 'source_unchanged': source.read_bytes() == raw, 'fresh_nonempty_object': rc == 0 and obj.is_file() and obj.stat().st_size > 0, 'object_sha256': hashlib.sha256(obj.read_bytes()).hexdigest() if rc == 0 and obj.is_file() else None, 'peak_rss_bytes': int(rss.group(1)) if rss else None, 'error_diagnostics': len(re.findall(r'\.lean:\d+:\d+: error:', text))}
(out / (label + '.json')).write_text(json.dumps(result, indent=2) + '\n')
(out / 'check_probe.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(result), flush=True)
assert result['source_unchanged']
sys.exit(rc)
