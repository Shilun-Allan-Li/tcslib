# io-sprg import-environment binding, Mac host 2026-11-18; no Lean.
# Bind checks to the complete job-owned olean tree, not merely probe text.
import hashlib,json
from pathlib import Path
def snapshot(tree,home):
 tree=Path(tree).resolve();rows=[]
 for p in sorted(tree.rglob('*.olean')):
  rows.append(dict(path=p.relative_to(tree).as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 assert rows,'empty import environment'
 payload=json.dumps(rows,sort_keys=True,separators=(',',':')).encode();digest=hashlib.sha256(payload).hexdigest()
 folder=Path(home)/'environment-snapshots';folder.mkdir(exist_ok=True)
 (folder/(digest+'.json')).write_text(json.dumps(dict(tree=str(tree),sha256=digest,objects=rows),indent=1)+'\n')
 return digest
def previous(binding,mod):
 p=Path(binding)
 if not p.exists():return None
 return next((r for r in reversed([json.loads(l) for l in p.read_text().splitlines()]) if r['module']==mod),None)
def record(binding,row,digest):
 with Path(binding).open('a') as f:f.write(json.dumps(dict(module=row['module'],source_sha256=row['source_sha256'],log_sha256=row['log_sha256'],environment_sha256=digest))+'\n')
