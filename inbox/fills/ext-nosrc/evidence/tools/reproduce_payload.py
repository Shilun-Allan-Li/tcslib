"""Replay the complete format-patch series at the pinned base and compare src bytes.
Run as python3 -I evidence/tools/reproduce_payload.py PAYLOAD_DIRECTORY.
Uses a fresh source-only scratch directory; no packages, toolchains or oleans are copied.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
payload=Path(sys.argv[1]).resolve()
base='eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
files=sorted(p.relative_to(payload/'src').as_posix() for p in (payload/'src').rglob('*') if p.is_file())
scratch=Path(tempfile.mkdtemp(prefix='ext-nosrc-replay-',dir='/private/tmp'))
for name in files:
 p=subprocess.run(['git','show',base+':'+name],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if p.returncode==0:
  dest=scratch/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.stdout)
for patch in sorted((payload/'patches').glob('*.patch')):
 subprocess.run(['git','apply','--check',str(patch)],cwd=scratch,check=True)
 subprocess.run(['git','apply',str(patch)],cwd=scratch,check=True)
rows=[]
for name in files:
 actual=(scratch/name).read_bytes();expected=(payload/'src'/name).read_bytes()
 assert actual==expected,name
 rows.append({'path':name,'sha256':hashlib.sha256(actual).hexdigest(),'equal':True})
print(json.dumps({'base':base,'scratch':str(scratch),'patch_count':len(list((payload/'patches').glob('*.patch'))),'files':rows,'result':'PASS'},indent=2))
