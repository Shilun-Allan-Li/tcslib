# io-sprg checkpoint packager,2026-11-18. Root only; invokes no Lean.
# Writes only an explicit io-sprg payload destination and private temporary directories.
# Format-patch --always and am --empty=keep preserve the verified empty M0 marker.
import argparse,hashlib,json,os,pathlib,shutil,subprocess,tempfile,zipfile
P=pathlib.Path
ap=argparse.ArgumentParser();ap.add_argument('--source',required=True)
ap.add_argument('--dest',required=True);ap.add_argument('--report',required=True)
ap.add_argument('--head',default='HEAD');ap.add_argument('--zip');a=ap.parse_args()
root=P(a.source).resolve();dest=P(a.dest).resolve();base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
assert dest.name=='io-sprg' and dest.parent.name=='fills' and dest.parent.parent.name=='inbox'
def git(*args,cwd=root,env=None):
 r=subprocess.run(['git',*args],cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if r.returncode:raise RuntimeError(r.stdout)
 return r.stdout
head=git('rev-parse',a.head).strip();assert head==git('rev-parse','fill/io-sprg').strip();changed=git('diff','--name-only',base,head).splitlines()
assert all(f=='TCSlib.lean' or f.startswith('TCSlib/Cryptography/Obfuscation') for f in changed)
assert all(f.endswith('.lean') for f in changed)
tree_checks=[]
for rev in [base]+git('rev-list','--reverse',base+'..'+head).splitlines():
 paths=git('ls-tree','-r','--name-only',rev).splitlines()
 pdfs=[p for p in paths if p.lower().endswith('.pdf')]
 assert not pdfs,(rev,pdfs)
 tree_checks.append(dict(commit=rev,paths=len(paths),pdf_paths=pdfs))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def manifest(folder,name):
 files=sorted(p for p in folder.rglob('*') if p.is_file() and p!=folder/name)
 assert not any(p.is_symlink() or p.suffix.lower()=='.pdf' for p in folder.rglob('*'))
 (folder/name).write_text(''.join(sha(p)+'  '+p.relative_to(folder).as_posix()+'\n' for p in files))
 return files
with tempfile.TemporaryDirectory(prefix='io-sprg-package-',dir='/private/tmp') as td:
 stage=P(td)/'io-sprg';stage.mkdir();(stage/'patches').mkdir();(stage/'bundle').mkdir()
 shutil.copy2(a.report,stage/'REPORT.md')
 shutil.copytree(root/'evidence',stage/'evidence')
 (stage/'evidence/pdf-commit-trees.json').write_text(json.dumps(tree_checks,indent=2)+'\n')
 for f in changed:
  p=stage/'src'/f;p.parent.mkdir(parents=True,exist_ok=True)
  p.write_bytes(subprocess.check_output(['git','show',head+':'+f],cwd=root))
 fmt='%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%G?'
 metadata=git('log','--reverse','--format='+fmt,base+'..'+head)
 (stage/'patches/COMMITS.tsv').write_text('hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'+metadata)
 git('format-patch','--always','--full-index','--binary','--no-signature','--output-directory',str(stage/'patches'),base+'..'+head)
 bundle=stage/'bundle/io-sprg.bundle';git('bundle','create',str(bundle),base+'..fill/io-sprg')
 (stage/'evidence/bundle-verify.txt').write_text(git('bundle','verify',str(bundle)))
 replay=P(td)/'replay';git('clone','--shared','--no-checkout',str(root),str(replay))
 git('switch','--detach',base,cwd=replay)
 patches=sorted((stage/'patches').glob('*.patch'));records=metadata.splitlines();assert len(patches)==len(records)
 checks=[]
 for patch,row in zip(patches,records):
  expected,an,ae,ad,cn,ce,cd,signing=row.split('\t')
  env=dict(os.environ,GIT_COMMITTER_NAME=cn,GIT_COMMITTER_EMAIL=ce,GIT_COMMITTER_DATE=cd)
  output=git('-c','commit.gpgsign=false','am','--empty=keep',str(patch),cwd=replay,env=env)
  actual=git('rev-parse','HEAD',cwd=replay).strip();assert actual==expected,(actual,expected)
  checks.append(dict(commit=expected,replayed=actual,patch=patch.name,output=output))
 assert git('rev-parse','HEAD',cwd=replay).strip()==head
 (stage/'evidence/replay.json').write_text(json.dumps(dict(base=base,head=head,all_hashes_match=True,commits=checks),indent=2)+'\n')
 (stage/'evidence/payload-source-binding.json').write_text(json.dumps(dict(base=base,head=head,files=changed),indent=2)+'\n')
 manifest(stage/'evidence','SHA256SUMS');manifest(stage,'SHA256SUMS')
 # Verify both path sets exactly, and every digest, after generating the manifests.
 for folder in [stage,stage/'evidence']:
  lines=(folder/'SHA256SUMS').read_text().splitlines();listed={}
  for line in lines:
   digest,path=line.split('  ',1);assert not path.startswith('./') and path not in listed
   listed[path]=digest;assert sha(folder/path)==digest
  actual={p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=folder/'SHA256SUMS'}
  assert set(listed)==actual
 dest.mkdir(parents=True,exist_ok=True)
 for p in dest.iterdir():
  if p.is_dir():shutil.rmtree(p)
  else:p.unlink()
 for p in stage.iterdir():
  if p.is_dir():shutil.copytree(p,dest/p.name)
  else:shutil.copy2(p,dest/p.name)
 if a.zip:
  zp=P(a.zip).resolve();zp.parent.mkdir(parents=True,exist_ok=True)
  with zipfile.ZipFile(zp,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
   for p in sorted(stage.rglob('*')):
    if p.is_file():z.write(p,'io-sprg/'+p.relative_to(stage).as_posix())
 print(json.dumps(dict(head=head,commits=len(checks),source_files=len(changed),payload_files=len([p for p in dest.rglob('*') if p.is_file()]),destination=str(dest),zip=a.zip,all_manifests_exact=True)))
