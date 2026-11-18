#!/usr/bin/env python3
"""ROOT-ONLY future read-only Git binding; no Lean/lake and no Git mutation."""
import argparse, hashlib, json, subprocess
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('snapshot',type=Path); a=ap.parse_args()
s=json.loads((a.snapshot/'snapshot.json').read_text()); root=Path(s['root'])
fe=root/'TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption'
pa=root/'TCSlib/Cryptography/Pairing'
paths=[fe.with_suffix('.lean'), *fe.rglob('*.lean'), pa/'Exponents.lean',
       pa/'Linear.lean', pa/'MatrixDH.lean', *(pa/'MatrixDH').rglob('*.lean')]
current={p.relative_to(root).as_posix() for p in paths if p.is_file()}
assert current==set(s['files']), 'Owned module set changed; regenerate snapshot'
head=subprocess.run(['git','-C',str(root),'rev-parse','HEAD'],check=True,capture_output=True,text=True).stdout.strip()
if head!=s['head_at_snapshot']: raise SystemExit('HEAD changed; regenerate snapshot before binding')
for path,rec in s['files'].items():
 raw=(root/path).read_bytes(); committed=subprocess.run(['git','-C',str(root),'show',head+':'+path],
                                                       check=True,capture_output=True).stdout
 if raw!=committed or hashlib.sha256(raw).hexdigest()!=rec['sha256']:
  raise SystemExit('Working bytes do not equal snapshot AND committed HEAD: '+path)
record={'status':'HEAD_BOUND_NOT_LEAN_VERIFIED','head':head,'source_bytes_equal_head':True,
        'snapshot_sha256':hashlib.sha256((a.snapshot/'snapshot.json').read_bytes()).hexdigest(),
        'files':len(s['files']),'lean_processes_started':0,'git_mutations':0}
(a.snapshot/'head-binding.json').write_text(json.dumps(record,indent=2)+'\n'); print(json.dumps(record))
