"""Apply one exact proof-body warning cleanup, retaining both source snapshots.

Root-only, no Lean. Never copies old complete modules over current source.
"""
import argparse
import hashlib
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('replacements')
ap.add_argument('edit_id')
a = ap.parse_args()
rows = json.loads(Path(a.replacements).read_text())
matches = [r for r in rows if r['id'] == a.edit_id]
assert len(matches) == 1
r = matches[0]
p = Path('TCSlib/Cryptography/Obfuscation/StructuredSeed') / r['file']
before = p.read_text()
assert before.count(r['before']) == 1
after = before.replace(r['before'], r['after'])
out = Path('evidence/warning-cleanup') / a.edit_id
assert not out.exists()
out.mkdir(parents=True)
(out / 'before.lean.txt').write_text(before)
(out / 'after.lean.txt').write_text(after)
r.update(file=str(p), before_sha256=hashlib.sha256(before.encode()).hexdigest(),
         after_sha256=hashlib.sha256(after.encode()).hexdigest(),
         status='APPLIED_NOT_YET_CHECKED')
(out / 'edit.json').write_text(json.dumps(r, indent=1) + '\n')
p.write_text(after)
print('ONE_PROOF_BODY_WARNING_EDIT', a.edit_id, r['theorem'])
