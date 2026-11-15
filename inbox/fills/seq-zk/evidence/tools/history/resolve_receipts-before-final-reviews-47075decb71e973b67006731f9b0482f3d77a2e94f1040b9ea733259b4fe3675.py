"""Resolve immutable historical receipts without dropping any version of updated metadata."""
from pathlib import Path
import csv,hashlib,subprocess,json
root=Path.cwd();ev=root/'evidence'
def sha(b):return hashlib.sha256(b).hexdigest()
index={}
for p in ev.rglob('*'):
 if p.is_file():index.setdefault(sha(p.read_bytes()),[]).append(p)
records=[];unresolved=[];archives=[]
receipts=set(ev.glob('subagents/*/*closed-files.tsv')) | set(ev.glob('subagents/**/CLOSED.tsv'))
for receipt in sorted(receipts):
 for row in csv.DictReader(receipt.open(),delimiter='\t'):
  rel=row.get('relative_path',row.get('path'));h=row.get('sha256')
  if not rel or not h:continue
  p=root/rel if rel.startswith('evidence/') else receipt.parent/rel
  method='current exact bytes';found=p if p.is_file() and sha(p.read_bytes())==h else None
  if found is None and h in index:
   found=index[h][0];method='preserved alternate exact bytes'
  if found is None and p.is_file():
   raw=p.read_bytes();digest=hashlib.sha256();pos=0
   for line in raw.splitlines(keepends=True):
    digest.update(line);pos+=len(line)
    if digest.hexdigest()==h:
     raw=raw[:pos];method='exact SHA-verified append-only prefix';break
   else:raw=None
   if raw is not None:
    found=ev/'receipt-versions'/h/p.relative_to(ev);found.parent.mkdir(parents=True,exist_ok=True);found.write_bytes(raw);index[h]=[found];archives.append(str(found.relative_to(root)))
  if found is None:
   for rev in ['36f1896da3fe7c31d4d8f63b4610fe081c75cfb1','d316d29a7c1f507f2c3a37f13a38db28d65dca20']:
    q=subprocess.run(['git','show',rev+':inbox/fills/seq-zk/'+p.relative_to(root).as_posix()],capture_output=True)
    if q.returncode==0 and sha(q.stdout)==h:
     found=ev/'receipt-versions'/h/p.relative_to(ev);found.parent.mkdir(parents=True,exist_ok=True);found.write_bytes(q.stdout);index[h]=[found];method='exact bytes from own published checkpoint '+rev;archives.append(str(found.relative_to(root)));break
  item=dict(receipt=str(receipt.relative_to(root)),original_path=rel,sha256=h,resolved_path=str(found.relative_to(root)) if found else None,method=method if found else 'UNRESOLVED')
  records.append(item)
  if found is None:unresolved.append(item)
with (ev/'receipt-resolution.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=['receipt','original_path','sha256','resolved_path','method'],delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(records)
summary=dict(rows=len(records),resolved=len(records)-len(unresolved),unresolved=unresolved,new_archives=archives)
(ev/'logs/receipt-resolution-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2));raise SystemExit(1 if unresolved else 0)
