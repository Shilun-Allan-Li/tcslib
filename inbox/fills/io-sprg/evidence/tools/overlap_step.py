# io-sprg root-only isolated overlap search driver, Mac 2026-11-18.
# Invokes unchanged serial/no-o runner through pinned slot wrapper; one probe per invocation.
# Search-only heartbeat limit 100000 bounds diagnostics, not mathematical owner proofs.
import argparse,subprocess
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('family');ap.add_argument('name');ap.add_argument('mode',choices=['exact','apply']);a=ap.parse_args()
homes={'Params':'OverlapParams','Basic':'OverlapEncoding','Encoding':'OverlapEncoding','BucketsSparse':'OverlapBucketsSparse','BucketsSparseV2':'OverlapBucketsSparseV2','AlgebraMatrixV2':'OverlapAlgebraV2','AlgebraSupportV2':'OverlapAlgebraSupportV2','LPN':'OverlapLPN','Algebra':'OverlapAlgebra','AlgebraV2':'OverlapAlgebra','Stretch':'OverlapStretchFinal','Bridges':'M1Bridges'}
home=Path('/private/tmp/io-sprg-proof-notes')/homes[a.family]
s=(home/'templates'/(a.name+'.lean.template')).read_text();assert s.count('__PROBE_BODY__')==1
assert not any(l.startswith('import TCSlib.Cryptography.Obfuscation') for l in s.splitlines())
if not any(c in s for c in ('∑','∏')):s=s.replace('open scoped BigOperators\n','')
s=s.replace('set_option maxHeartbeats 0','set_option maxHeartbeats 100000')
s=s.replace('__PROBE_BODY__','by\n  '+a.mode+'?');assert s.count(':= by')==1
p=Path('/private/tmp/io-sprg-overlap')/(a.family+'_'+a.name+'-'+a.mode+'.lean')
assert not p.exists(),'Use a fresh name or archive previous run explicitly; never overwrite probe history'
p.write_text(s);order=Path('evidence/logs/overlap-current-order.txt');order.write_text(str(p.with_suffix(''))+'\n')
subprocess.run(['python3','-I','evidence/tools/seal/runner_full.py','.',str(order),'.lake/io-sprg-oleans','evidence/overlap/runs'],check=True)
print('SEARCH_FINISHED',a.family,a.name,a.mode)
