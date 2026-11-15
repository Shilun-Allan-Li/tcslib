from pathlib import Path
import json
import runpy
import subprocess

old = '904123d3780cc1f5daf4f37ad49d90395595c1a9'
new = '5e12a169e671dc16b6766e21067b79c16835af67'
path = 'TCSlib/Complexity/Randomized/SeedMajority/State.lean'
changed = subprocess.check_output(['git', 'diff', '--name-only', old, new], text=True).splitlines()
assert changed == [path], changed
mask = runpy.run_path('evidence/tools/frozen_headers.py')['mask']
before = subprocess.check_output(['git', 'show', old + ':' + path], text=True)
after = subprocess.check_output(['git', 'show', new + ':' + path], text=True)
assert mask(before).split() == mask(after).split(), 'Non-comment tokens differ'
rows = [json.loads(line) for line in Path('evidence/logs/final-full/results.jsonl').read_text().splitlines()]
assert path[:-5] not in {row['module'] for row in rows}, 'Affected module already checked'
record = dict(start_tip=old, final_tip=new, changed=changed, comment_only=True,
              completed_before_advance=len(rows), affected_module_already_checked=False)
Path('evidence/logs/final-source-advance.json').write_text(json.dumps(record, indent=2) + '\n')
subprocess.run(['git', 'checkout', '--detach', new], check=True)
print('SOURCE ADVANCE PASS: comment-only change before affected module; '
      'all completed modules unchanged. Final audit will compare every source hash.')
