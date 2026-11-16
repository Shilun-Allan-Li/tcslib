"""Run every prepared seal or control probe serially; keep every raw log (gsw-security).

Adapted from the derand fill's `run_seals.py`. Each probe goes through
`check_module.py --maxerrors0` (that is `lean -DmaxErrors=0` via
`lean_check_tree_maxerrors0.sh`), one Lean process at a time. Errors are counted in both
forms (`error:` and `error(`) with `^\\S+\\.lean:\\d+:\\d+: error[:(]`, and each is mapped back to
its source line through the probe's line map. A sealed probe is harness-valid when it logs
exactly one `GSWSEC-INSTALL` and one `GSWSEC-EOF` for its label and every error maps to a
source line. Unsealed probes (no label in the manifest row) only record their errors.

Usage (python3 -I, from the fill checkout root): run_seals.py <dir-with-manifest.json>
Appends one JSON row per probe to <dir>/results.jsonl and prints a one-line summary each.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

folder = Path(sys.argv[1])
manifest = json.loads((folder / 'manifest.json').read_text())
tool = Path(__file__).resolve().parent / 'check_module.py'
results = folder / 'results.jsonl'
ERR = re.compile(r'^\S+\.lean:(\d+):(\d+): error[:(].*$', re.M)
bad = 0
for item in manifest:
    path = Path(item['probe'])
    log = path.with_suffix('.log')
    proc = subprocess.run(['python3', '-I', str(tool), '--maxerrors0', str(path.with_suffix('')),
                           str(log)], capture_output=True, text=True)
    raw = log.read_text()
    mapfile = path.with_suffix('.linemap.json')
    mapping = json.loads(mapfile.read_text()) if mapfile.exists() else None
    errors = []
    for m in ERR.finditer(raw):
        line = int(m[1])
        src = (mapping[line - 1] if line <= len(mapping) else None) if mapping else line
        errors.append(dict(probe_line=line, source_line=src, diagnostic=m[0]))
    colon = len(re.findall(r'^\S+\.lean:\d+:\d+: error:', raw, re.M))
    paren = len(re.findall(r'^\S+\.lean:\d+:\d+: error\(', raw, re.M))
    label = item.get('label')
    row = dict(item, exit=proc.returncode, errors=errors, error_count=len(errors),
               error_colon=colon, error_paren=paren, log=str(log))
    if label:
        install = re.findall(r'GSWSEC-INSTALL ' + re.escape(label) + r' requested=(\d+)', raw)
        eof = raw.count('GSWSEC-EOF ' + label)
        harness = len(install) == 1 and eof == 1 and all(e['source_line'] for e in errors)
        row.update(install=len(install), eof=eof,
                   requests=int(install[0]) if len(install) == 1 else None,
                   harness_valid=harness)
        bad += not harness
    m = re.search(r'MAXRSS_KIB (\d+)', raw)
    row['max_rss_kib'] = int(m[1]) if m else None
    with results.open('a') as dest:
        print(json.dumps(row), file=dest)
    print(f'{path}: exit={proc.returncode} errors={len(errors)} (error:={colon}, error(={paren}) '
          f'harness={row.get("harness_valid", "n/a")} requests={row.get("requests")}', flush=True)
print(f'{folder}: {len(manifest)} probes, harness-invalid {bad}', flush=True)
sys.exit(1 if bad else 0)
