"""Assemble a reviewable exchange payload; performs no push or commit."""
from pathlib import Path
import argparse,subprocess,shutil,hashlib,json
p=argparse.ArgumentParser();p.add_argument('destination',type=Path);p.add_argument('--head',required=True);a=p.parse_args()
root=Path.cwd();base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb';dst=a.destination.resolve()
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();assert head==a.head
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','TCSlib'],text=True).strip(),'uncommitted Lean changes'
if dst.exists():raise SystemExit('Use a fresh payload destination; refusing to overwrite')
dst.mkdir(parents=True)
files=subprocess.check_output(['git','diff','--name-only',base,head],text=True).splitlines()
for f in files:
 assert f.endswith('.lean'),f
 assert not f.lower().endswith('.pdf')
 d=dst/'src'/f;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(subprocess.check_output(['git','show',head+':'+f]))
shutil.copy2('REPORT.md',dst/'REPORT.md')
for f in Path('evidence').rglob('*'):
 if not f.is_file():continue
 assert f.suffix.lower()!='.pdf',f
 d=dst/f;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,d)
patches=dst/'patches';patches.mkdir()
subprocess.run(['git','-c','core.quotePath=false','format-patch','--no-signature','-o',str(patches),base+'..'+head],check=True,stdout=subprocess.PIPE)
fmt='%H%x09%an <%ae>%x09%cn <%ce>%x09%s%x09%G?'
rows=subprocess.check_output(['git','log','--reverse','--format='+fmt,base+'..'+head],text=True)
(patches/'COMMITS.tsv').write_text('hash\tauthor\tcommitter\tsubject\tsigning\n'+rows)
paths=sorted(f for f in dst.rglob('*') if f.is_file());manifest=''.join(hashlib.sha256(f.read_bytes()).hexdigest()+'  '+f.relative_to(dst).as_posix()+'\n' for f in paths)
(dst/'SHA256SUMS').write_text(manifest)
print(json.dumps({'source_head':head,'files':len(paths)+1,'lean_files':len(files),'payload':str(dst),'manifest_sha256':hashlib.sha256(manifest.encode()).hexdigest()},indent=2))
