"""Prepare a gate's working folder from $GATE/gate.json: CHANGED.txt (the Lean owners that differ
between base and head), POPULATION.txt and POPULATION-BASE.txt (the copy screen's populations),
base-src/ (the base's text of each owner) and driver-request.json (the replay driver's request).
Run once per head; it refuses to overwrite a replay that already exists."""
import json, os, subprocess
from pathlib import Path
G = Path(os.environ['GATE']); c = json.loads((G/'gate.json').read_text())
R, S = c['repo'], Path(c['scratch'])
git = lambda *a: subprocess.check_output(['git', '-C', R, *a]).decode()
head, base = git('rev-parse', c['head']).strip(), git('rev-parse', c['base']).strip()
changed = [p for p in git('diff', '--name-only', base, head, '--', 'TCSlib').split() if p.endswith('.lean')]
assert changed, 'no Lean owner differs between base and head'
added = [p for p in changed if subprocess.run(['git', '-C', R, 'cat-file', '-e', f'{base}:{p}'], capture_output=True).returncode]
deleted = [p for p in changed if subprocess.run(['git', '-C', R, 'cat-file', '-e', f'{head}:{p}'], capture_output=True).returncode]
present = [p for p in changed if p not in deleted]
(G/'CHANGED.txt').write_text('\n'.join(present) + '\n')
(G/'POPULATION.txt').write_text('\n'.join(present) + '\n')
(G/'POPULATION-BASE.txt').write_text('\n'.join(p for p in changed if p not in added) + '\n')
for p in changed:
    if p in added: continue
    t = G/'base-src'/p; t.parent.mkdir(parents=True, exist_ok=True)
    t.write_bytes(subprocess.check_output(['git', '-C', R, 'show', f'{base}:{p}']))
assert not (G/'replay').exists(), 'replay/ exists: move it to a runN/ folder first'
lean_files = sum(1 for p in git('ls-tree', '-r', '--name-only', head).split() if p.endswith('.lean'))
req = {'pr': c.get('pr', G.name), 'repository': R, 'head_ref': head, 'head': head,
       'baseline': git('rev-parse', c.get('baseline', c['base'])).strip(),
       'input_snapshot': c['input_snapshot'], 'input_hash_map': str(S/'manifests'/(c['input_snapshot'] + '.output.json')),
       'output_snapshot': c['output_snapshot'], 'evidence': str(G/'replay'), 'expected_owners': present,
       'merge_target': c.get('merge_target', ''), 'historical_timing': c.get('historical_timing', ''), 'workers': int(os.environ.get('TCSLIB_LEAN_SLOTS', '3')),
       'deleted_owners': deleted, 'lean_files': lean_files, 'added_owners': added}
(G/'driver-request.json').write_text(json.dumps(req, indent=2) + '\n')
print('head', head[:12], 'base', base[:12], 'owners', len(present), 'added', len(added), 'deleted', len(deleted))
