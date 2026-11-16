#!/usr/bin/env python3
"""Copy immutable evidence, retain large raw samples losslessly, and seal exact path sets."""
from pathlib import Path
import argparse,hashlib,json,shutil
parser=argparse.ArgumentParser();parser.add_argument('payload');args=parser.parse_args()
root=Path.cwd();dest=Path(args.payload);assert (dest/'REPORT.md').is_file()
skip={'logs/bobio-sample.txt','subagents/a/logs/all-tables-02-sample.txt'}
exclude_prefix=['probe-runs/yao-efficiency-repair-1/','seals/yao-efficiency-repair/']
for src in sorted((root/'evidence').rglob('*')):
 if not src.is_file():continue
 rel=src.relative_to(root/'evidence').as_posix()
 if rel=='SHA256SUMS' or rel in skip or any(rel.startswith(p) for p in exclude_prefix):continue
 target=dest/'evidence'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
for scope in [dest/'evidence',dest]:
 manifest=scope/'SHA256SUMS'
 rows=[]
 for p in sorted(scope.rglob('*')):
  if p.is_file() and p!=manifest:rows.append((hashlib.sha256(p.read_bytes()).hexdigest(),p.relative_to(scope).as_posix()))
 manifest.write_text(''.join(h+'  '+name+'\n' for h,name in rows))
 actual={p.relative_to(scope).as_posix() for p in scope.rglob('*') if p.is_file() and p!=manifest}
 listed={name for _,name in rows};assert actual==listed
 for h,name in rows:
  assert not name.startswith('./') and hashlib.sha256((scope/name).read_bytes()).hexdigest()==h
 print(scope,'EXACT FILES',len(rows),'BYTES',sum((scope/name).stat().st_size for _,name in rows))
