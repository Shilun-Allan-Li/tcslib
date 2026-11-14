import hashlib
import json
import pathlib
import re
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
old = [json.loads(s) for s in (ev/'logs/sweep-results.jsonl').read_text().splitlines()]
tail = [json.loads(s) for s in (ev/'logs/sweep-final-tail-results.jsonl').read_text().splitlines()]
assert len(old) == 169 and [r['index'] for r in tail] == list(range(164,169))
selected = old[:164] + tail
order = (ev/'logs/extended-order.txt').read_text().splitlines()
assert [r['module'] for r in selected] == order and all(r['exit'] == 0 for r in selected)
for r in selected:
    log = (ev/r['log']).read_text()
    sha = re.search(r'^source_sha256: ([0-9a-f]{64})$', log, re.M)[1]
    assert sha == hashlib.sha256((repo/(r['module']+'.lean')).read_bytes()).hexdigest(), r['module']
    r['source_sha256'] = sha
(ev/'logs/final-sweep-results.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in selected))
commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
summary = dict(source_commit=commit,module_count=169,errors=0,all_exit_zero=True,
    initial_full_sweep_passed=True,initial_source_commit='8e4234934690fe4e3e00e46965112998e1d09a31',
    unchanged_prefix_modules=164,rechecked_tail_indices=list(range(164,169)),
    all_selected_source_hashes_match=True,start=selected[0]['start'],end=selected[-1]['end'],
    max_rss_bytes=max(r['max_rss_bytes'] for r in selected),passed=True)
(ev/'logs/sweep-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
