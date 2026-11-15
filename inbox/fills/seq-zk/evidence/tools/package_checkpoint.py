"""Build a source/evidence checkpoint; manifests cover exactly the delivered ordinary files."""
from pathlib import Path
import subprocess,shutil,hashlib,sys
lead=Path.cwd();dest=Path(sys.argv[1]);rev=sys.argv[2];base='107f1e8c218733eac12d6b9bee6fece441271317'
number=sys.argv[3] if len(sys.argv)>3 else '1'
assert not dest.exists(),dest
dest.mkdir(parents=True)
shutil.copy2(lead/('evidence/CHECKPOINT'+number+'-REPORT.md'),dest/'REPORT.md')
shutil.copytree(lead/('evidence/checkpoint'+number+'-patches'),dest/'patches')
paths=subprocess.check_output(['git','diff','--name-only',base,rev],text=True).splitlines()
for path in paths:
 p=dest/'src'/path;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(subprocess.check_output(['git','show',rev+':'+path]))
shutil.copytree(lead/'evidence',dest/'evidence')
def manifest(root):
 files=sorted(p for p in root.rglob('*') if p.is_file() and p!=root/'SHA256SUMS')
 assert not [p for p in root.rglob('*') if p.is_symlink()]
 text=''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(root).as_posix()+'\n' for p in files)
 (root/'SHA256SUMS').write_text(text)
 return files
def verify(root):
 rows={}
 for l in (root/'SHA256SUMS').read_text().splitlines():
  digest,path=l.split('  ',1);assert path not in rows;rows[path]=digest
 actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p!=root/'SHA256SUMS'}
 assert actual==set(rows),(actual-set(rows),set(rows)-actual)
 for p,digest in rows.items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==digest,p
 return len(rows)
manifest(dest/'evidence');manifest(dest)
print('Evidence manifest verified:',verify(dest/'evidence'),'files')
print('Top manifest verified:',verify(dest),'files')
print('Sources:',len(paths));print('Payload:',dest)
print('Top manifest SHA256:',hashlib.sha256((dest/'SHA256SUMS').read_bytes()).hexdigest())
