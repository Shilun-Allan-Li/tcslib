#!/usr/bin/env python3
"""Export an exact proof tip, unsigned patches and reproducible commit metadata."""
import argparse, hashlib, json, os, runpy, shutil, subprocess
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--ref',required=True)
parser.add_argument('--out',required=True)
parser.add_argument('--report',required=True)
args=parser.parse_args()
root=Path.cwd();out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
base='6ce4658db08a1dc2a03a149987197660db078011'
ref=subprocess.check_output(['git','rev-parse',args.ref],text=True).strip()
files=subprocess.check_output(['git','diff','--name-only',base,ref],text=True).splitlines()
assert files and all(p.startswith('TCSlib/') and p.endswith('.lean') for p in files)
patchdir=out/'patches';patchdir.mkdir()
subprocess.run(['git','format-patch','--no-signature','--output-directory',str(patchdir),base+'..'+ref],check=True,stdout=subprocess.DEVNULL)
commits=subprocess.check_output(['git','rev-list','--reverse',base+'..'+ref],text=True).splitlines()
rows=[]
for c in commits:
 line=subprocess.check_output(['git','show','-s','--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%G?',c],text=True).strip()
 cols=line.split('\t');assert len(cols)==8 and cols[7]=='N',cols
 cols[7]='none';rows.append(cols)
(patchdir/'COMMITS.tsv').write_text('hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'+''.join('\t'.join(r)+'\n' for r in rows))
shutil.copyfile(args.report,out/'REPORT.md')
inventory=[];headers=[]
lex=runpy.run_path('evidence/tools/header_lexer.py')
for path in files:
 raw=subprocess.check_output(['git','show',ref+':'+path]);p=out/'src'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
 text=raw.decode();width=[i for i,s in enumerate(text.splitlines(),1) if len(s)>100]
 assert not width,(path,width)
 old=subprocess.run(['git','show',base+':'+path],capture_output=True,text=True)
 base_text=old.stdout if old.returncode==0 else ''
 n=len(text.splitlines());assert n+(28 if path.endswith('/Yao.lean') else 0)<= (1200 if path.endswith('/Yao.lean') else 999)
 inventory.append(dict(path=path,base_lines=len(base_text.splitlines()),lines=n,sha256=hashlib.sha256(raw).hexdigest(),width_max=max(map(len,text.splitlines()),default=0)))
 old_names={d['name'] for d in lex['declarations'](base_text)}
 for d in lex['declarations'](text):
  if d['name'] not in old_names:
   headers.append('## '+path+' · '+d['name']+'\n\n```lean\n'+d['header'].strip()+'\n```\n')
ev=out/'evidence/interfaces';ev.mkdir(parents=True)
(ev/'source-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
(ev/'source-signatures.md').write_text('# New declaration source-header excerpts\n\n'
    'The auxiliary source lexer can truncate a type at Boolean `||` or a type-level `let`.\n'
    'These excerpts are not the complete interface record. Fully elaborated stored types,\n'
    'including implicit section variables and private/generated constants, are exported in\n'
    '`full-stored-signatures.md` and retained in the authoritative axiom/closure probe log.\n\n'
    +'\n'.join(headers))
# A fresh shared clone reads only Git objects; no package/cache tree is copied.
scratch=Path('/private/tmp')/(out.name+'-reproduce')
assert not scratch.exists(),scratch
log=out/'evidence/patch-reproduction.log'
with log.open('w') as f:
 subprocess.run(['git','clone','--shared','--no-checkout',str(root),str(scratch)],check=True,stdout=f,stderr=subprocess.STDOUT)
 subprocess.run(['git','checkout','--detach',base],cwd=scratch,check=True,stdout=f,stderr=subprocess.STDOUT)
 patches=sorted(patchdir.glob('*.patch'));assert len(patches)==len(rows)
 for row,patch in zip(rows,patches):
  env=os.environ.copy();env.update(GIT_COMMITTER_NAME=row[4],GIT_COMMITTER_EMAIL=row[5],GIT_COMMITTER_DATE=row[6])
  subprocess.run(['git','-c','commit.gpgsign=false','am',str(patch)],cwd=scratch,env=env,check=True,stdout=f,stderr=subprocess.STDOUT)
  got=subprocess.check_output(['git','rev-parse','HEAD'],cwd=scratch,text=True).strip()
  assert got==row[0],(got,row[0]);f.write('REPRODUCED '+got+'\n');f.flush()
print(json.dumps(dict(ref=ref,files=len(files),commits=len(rows),payload=str(out),reproduced=True)))
