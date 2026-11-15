#!/usr/bin/env python3
"""Save/restore only this worker's sources for the baseline seal environment."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
p=argparse.ArgumentParser();p.add_argument('mode',choices=['base','final']);args=p.parse_args()
base='fbd37f447596d4207c8d08b7ef7602f57fe95198'
saved=Path('/private/tmp/sc-garble-runtime/seal-source-snapshot')
manifest=saved/'manifest.json'
files=Path('evidence/source-files.txt').read_text().splitlines()
if args.mode=='base':
 assert not manifest.exists(),'snapshot already exists; inspect rather than overwrite it'
 rows=[]
 for f in files:
  data=Path(f).read_bytes();dest=saved/f;dest.parent.mkdir(parents=True,exist_ok=True)
  dest.write_bytes(data)
  r=subprocess.run(['git','show',base+':'+f],capture_output=True)
  rows.append(dict(path=f,final_sha256=hashlib.sha256(data).hexdigest(),
                   base_sha256=hashlib.sha256(r.stdout).hexdigest()if not r.returncode else None))
  if not r.returncode:Path(f).write_bytes(r.stdout)
 manifest.write_text(json.dumps(rows,indent=2)+'\n')
 Path('evidence/seals/source-snapshot.json').write_text(manifest.read_text())
 print('BASE SOURCES INSTALLED:',sum(r['base_sha256']is not None for r in rows))
else:
 rows=json.loads(manifest.read_text())
 for r in rows:
  data=(saved/r['path']).read_bytes()
  assert hashlib.sha256(data).hexdigest()==r['final_sha256']
  Path(r['path']).write_bytes(data)
 assert all(hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['final_sha256']for r in rows)
 print('FINAL SOURCES RESTORED BYTE-FOR-BYTE:',len(rows))
