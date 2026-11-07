"""Capture the exact 25-file API1160/current-draft source populations, read-only."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess

out = Path(__file__).resolve().parent
root = out.parents[4]
scratch = Path(os.environ['TCSLIB_SCRATCH'])
wt = scratch / 'wt-epad'
base = '1160c18f03fd318f0dec25738790935fa61379d4'
population = root / 'campaign/fills/mig1/landing/review-final-source/screen-population-final-review.txt'
paths = population.read_text().splitlines()
assert len(paths) == len(set(paths)) == 25
assert all(p.startswith('TCSlib/') and p.endswith('.lean') and '..' not in Path(p).parts for p in paths)
def git(*args):
    return subprocess.check_output(['git', '-C', str(wt), *args])
assert git('rev-parse', base + '^{commit}').decode().strip() == base
git('cat-file', '-e', base + '^{commit}')
before = {p: (wt / p).read_bytes() for p in paths}
entries = []
for p in paths:
    oid = git('rev-parse', base + ':' + p).decode().strip()
    assert len(oid) == 40
    git('cat-file', '-e', oid + '^{blob}')
    baseline = git('show', base + ':' + p)
    assert hashlib.sha1(b'blob ' + str(len(baseline)).encode() + b'\0' + baseline).hexdigest() == oid
    row = dict(path=p, baseline_blob=oid)
    for label, data in [('base', baseline), ('head', before[p])]:
        target = out / 'inputs' / label / (p + '.txt')
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        row[label + '_sha256'] = hashlib.sha256(data).hexdigest()
        row[label + '_bytes'] = len(data)
    row['changed'] = baseline != before[p]
    entries.append(row)
assert all((wt / p).read_bytes() == before[p] for p in paths), 'actual source changed during capture'
(out / 'population.txt').write_bytes(population.read_bytes())
receipt = dict(label='CURRENT DRAFT, captured before comment fixes; not final gate',
               captured_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               base_commit=base, base_commit_and_all_blob_objects_verified=True,
               actual_worktree=str(wt), source_population=str(population),
               count=len(paths), current_sources_stable_during_capture=True, files=entries)
(out / 'capture.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'count': len(paths), 'base_commit': base,
                  'changed_files': [r['path'] for r in entries if r['changed']],
                  'capture_sha256': hashlib.sha256((out/'capture.json').read_bytes()).hexdigest(),
                  'current_sources_stable_during_capture': True}, indent=2))
