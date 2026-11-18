#!/usr/bin/env python3
"""ROOT-ONLY canonical static scan setup; starts Python/read-only Git, never Lean."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
for n in ['snapshot','tools','out','scratch']:ap.add_argument('--'+n,type=Path,required=True)
a=ap.parse_args();s=json.loads((a.snapshot/'snapshot.json').read_text());b=json.loads((a.snapshot/'head-binding.json').read_text())
assert b['source_bytes_equal_head'] and b['head']==s['head_at_snapshot']
assert b['snapshot_sha256']==hashlib.sha256((a.snapshot/'snapshot.json').read_bytes()).hexdigest()
root=Path(s['root']);a.out.mkdir(parents=True,exist_ok=True);a.scratch.mkdir(parents=True,exist_ok=True)
for p,r in s['files'].items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==r['sha256'],p
files=sorted(s['files']);mods=[s['files'][p]['module'] for p in files]
subprocess.run([sys.executable,'-I',str(a.tools/'seal/review/touched.py'),str(root),s['base'],
 b['head'],str(a.out/'touched.json'),*files],check=True,stdout=(a.out/'touched.tsv').open('w'))
probe=a.scratch/'ExplicitKinds.lean';env=dict(os.environ,SCAN_IMPORTS=' '.join(mods))
subprocess.run([sys.executable,'-I',str(a.tools/'seal/scan1_g40.py'),
 str(a.tools/'seal/review/archived-gate10-tools/scan_explicit.py'),str(root),
 str(a.out/'touched.json'),str(a.out/'explicit-items.json'),str(probe),*files],check=True,env=env)
(a.out/'explicit-order.txt').write_text(probe.relative_to(root).with_suffix('').as_posix()+'\n')
(a.out/'explicit-status.json').write_text(json.dumps({'status':'PREPARED_NOT_RUN',
 'source_head':b['head'],'native_kind_probe_verified':False,'foreign_reader_pass':None},indent=2)+'\n')
