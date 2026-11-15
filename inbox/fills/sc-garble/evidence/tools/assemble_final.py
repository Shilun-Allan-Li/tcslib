#!/usr/bin/env python3
"""Assemble a complete, replayed, exact-manifest final delivery from committed source."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
BASE='fbd37f447596d4207c8d08b7ef7602f57fe95198'
root=Path.cwd();payload=Path('/private/tmp/sc-garble-runtime/final/sc-garble')
replay=Path('/private/tmp/sc-garble-runtime/replay-final')
assert Path('evidence/logs/remaining-validation-PASS.txt').exists()
correction=[json.loads(l)for l in Path('evidence/logs/seals-final-correction-02/results.jsonl').read_text().splitlines()]
assert len(correction)==4 and all(r['exit']==0 and r['errors']==0 for r in correction)
assert not subprocess.check_output(['git','diff','--name-only','--','TCSlib'])
assert not subprocess.check_output(['git','diff','--cached','--name-only'])
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','merge-base',BASE,head],text=True).strip()==BASE
files=subprocess.check_output(['git','diff','--name-only',BASE,head],text=True).splitlines()
assert len(files)==14 and all(f.startswith('TCSlib/')and f.endswith('.lean')for f in files)
sweep=[json.loads(l)for l in Path('evidence/logs/final-sweep/results.jsonl').read_text().splitlines()]
assert len(sweep)==174 and all(r['exit']==0 and r['errors']==0 for r in sweep)
assert sum(r['sorries']for r in sweep)==25 and sum(r['sorries']>0 for r in sweep)==11
lookup={r['module']:r for r in sweep}
for f in files:
 expected=subprocess.check_output(['git','show',head+':'+f])
 actual=Path(lookup[f[:-5]]['log']).with_suffix('.source.lean').read_bytes()
 assert actual==expected,('delivered source differs from final sweep input',f)
seals=json.loads(Path('evidence/seals/analysis.json').read_text())
assert len(seals)==80 and all(not r['errors']for r in seals if r['variant']=='A')
assert Path('evidence/unfold/final-verdict.json').exists()
assert not json.loads(Path('evidence/unfold/final-verdict.json').read_text())['violations']
assert all(not r['issues']for r in json.loads(Path('evidence/headers/final/results.json').read_text()))
adm=json.loads(Path('evidence/admissions/final.json').read_text())
assert adm['base_count']==32 and adm['current_count']==25 and len(adm['removed'])==7 and not adm['added']
for kind in ['FAIL','WARN']:
 a={l for l in Path('evidence/logs/lint-base.log').read_text().splitlines()if l.startswith(kind)}
 b={l for l in Path('evidence/logs/lint-final.log').read_text().splitlines()if l.startswith(kind)}
 assert a==b,(kind,a-b,b-a)
if payload.exists():shutil.rmtree(payload)
(payload/'patches').mkdir(parents=True)
subprocess.run(['git','format-patch','--full-index','--output-directory',str(payload/'patches'),
                BASE+'..HEAD'],check=True)
commits=subprocess.check_output(['git','rev-list','--reverse',BASE+'..HEAD'],text=True).splitlines()
rows=[]
for commit in commits:
 fields=subprocess.check_output(['git','show','-s',
  '--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI',commit],text=True).strip().split('\t')
 assert b'\ngpgsig 'not in subprocess.check_output(['git','cat-file','commit',commit])
 rows.append(fields+['none'])
(payload/'patches/COMMITS.tsv').write_text(
 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'+
 ''.join('\t'.join(r)+'\n'for r in rows))
if replay.exists():shutil.rmtree(replay)
logpath=Path('evidence/replay/final.log');logpath.parent.mkdir(parents=True,exist_ok=True)
with logpath.open('w')as log:
 subprocess.run(['git','clone','--shared','--no-checkout',str(root),str(replay)],
  check=True,stdout=log,stderr=subprocess.STDOUT)
 subprocess.run(['git','checkout','--detach',BASE],cwd=replay,check=True,stdout=log,stderr=subprocess.STDOUT)
 for row,patch in zip(rows,sorted((payload/'patches').glob('*.patch'))):
  env=os.environ.copy();env.update(GIT_COMMITTER_NAME=row[4],GIT_COMMITTER_EMAIL=row[5],GIT_COMMITTER_DATE=row[6])
  subprocess.run(['git','-c','commit.gpgsign=false','am',str(patch)],cwd=replay,env=env,
   check=True,stdout=log,stderr=subprocess.STDOUT)
  actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=replay,text=True).strip()
  log.write('EXPECTED '+row[0]+' ACTUAL '+actual+'\n');assert actual==row[0]
 log.write('PASS: every unsigned commit hash reproduced exactly.\n')
line_rows=[]
for f in files:
 data=subprocess.check_output(['git','show',head+':'+f]);dest=payload/'src'/f
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 old=subprocess.run(['git','show',BASE+':'+f],capture_output=True)
 lines=data.decode().splitlines()
 assert len(lines)<=1000 and all(len(l)<=100 for l in lines)
 line_rows.append((f,len(old.stdout.decode().splitlines())if not old.returncode else 0,len(lines)))
slots=Path('/Users/seyoonr/.lean-slots/slots.log').read_text().splitlines(True)
Path('evidence/logs/slots.log').write_text(''.join(l for l in slots if 'tag=sc-garble 'in l))
shutil.copytree('evidence',payload/'evidence',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
report=Path('evidence/final-report-template.md').read_text()
values={'@@HEAD@@':head,'@@TABLE@@':'\n'.join('| `'+p+'` | '+str(a)+' | '+str(b)+' |'for p,a,b in line_rows),
 '@@SIGNATURES@@':Path('evidence/declarations/final-signatures.txt').read_text().rstrip(),
 '@@AXIOMS@@':Path('evidence/logs/final-axiom-summary.txt').read_text().rstrip(),
 '@@SEALS@@':Path('evidence/seals/final-summary.txt').read_text().rstrip()}
for key,value in values.items():report=report.replace(key,value)
assert not re.search(r'@@[A-Z]+@@',report)
(payload/'REPORT.md').write_text(report)
def manifest(folder):
 paths=sorted(p for p in folder.rglob('*')if p.is_file()and p!=folder/'SHA256SUMS')
 (folder/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+
   p.relative_to(folder).as_posix()+'\n'for p in paths))
 listed=[l[66:]for l in (folder/'SHA256SUMS').read_text().splitlines()]
 assert listed==[p.relative_to(folder).as_posix()for p in paths]
 r=subprocess.run(['shasum','-a','256','-c','SHA256SUMS'],cwd=folder,capture_output=True,text=True)
 assert r.returncode==0,r.stdout+r.stderr
 print('EXACT MANIFEST PASS',folder,len(paths),'files')
manifest(payload/'evidence');manifest(payload)
print('PAYLOAD',payload,'SOURCE_HEAD',head,'COMMITS',len(rows))
