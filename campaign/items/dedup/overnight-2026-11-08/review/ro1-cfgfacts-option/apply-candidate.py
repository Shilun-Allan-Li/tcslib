from pathlib import Path
import json,hashlib
O=Path('/private/tmp/ab34-ro1-integration')
W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
rows=json.loads((O/'candidate-source-map.json').read_text())
for r in rows:
    p=W/r['path'];h=hashlib.sha256(p.read_bytes()).hexdigest()
    assert h in (r['baseline_sha256'],r['candidate_sha256']),(r['path'],h)
for r in rows:
    p=W/r['path'];b=(O/'source-candidate'/(r['path']+'.txt')).read_bytes()
    assert hashlib.sha256(b).hexdigest()==r['candidate_sha256']
    p.write_bytes(b)
receipt={'source_root':str(W),'files':rows,'held_imports_not_authorized_to_publish':json.loads((O/'held-imports.json').read_text()),'no_commit_push_PR_or_records_changes':True}
(O/'applied-held-candidate.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Applied held candidate to '+str(len(rows))+' source files.')
