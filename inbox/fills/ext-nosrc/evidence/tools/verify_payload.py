"""Verify exact artifact manifests and optional ZIP equality. Run as python3 -I.
Usage: verify_payload.py PAYLOAD_DIRECTORY [ZIP_PATH]
"""
from pathlib import Path
import hashlib,json,sys,zipfile
root=Path(sys.argv[1]).resolve()
assert root.name=='ext-nosrc'
def digest(raw):return hashlib.sha256(raw).hexdigest()
def verify(folder):
 rows={}
 for line in (folder/'SHA256SUMS').read_text().splitlines():
  value,name=line.split('  ',1);p=Path(name)
  assert not p.is_absolute() and '..' not in p.parts,name
  assert name not in rows,name
  rows[name]=value
 actual={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'SHA256SUMS'}
 assert actual==set(rows),{'missing':sorted(set(rows)-actual),'unlisted':sorted(actual-set(rows))}
 for name,value in rows.items():
  path=folder/name
  assert not path.is_symlink(),name
  assert digest(path.read_bytes())==value,name
 return len(rows)
assert (root/'REPORT.md').is_file() and (root/'patches').is_dir() and (root/'src').is_dir() and (root/'evidence').is_dir()
counts={'evidence_manifest_files':verify(root/'evidence'),'payload_manifest_files':verify(root)}
if len(sys.argv)>2:
 archive=Path(sys.argv[2])
 with zipfile.ZipFile(archive) as z:
  assert z.testzip() is None
  entries=z.namelist();expected={p.relative_to(root.parent).as_posix():p for p in root.rglob('*') if p.is_file()}
  assert len(entries)==len(set(entries)) and set(entries)==set(expected)
  assert all(s.startswith('ext-nosrc/') for s in entries)
  for name,path in expected.items():assert z.read(name)==path.read_bytes(),name
 counts.update(zip_files=len(entries),zip_sha256=digest(archive.read_bytes()),zip_bytes=archive.stat().st_size)
print(json.dumps({'result':'PASS',**counts},indent=2))
