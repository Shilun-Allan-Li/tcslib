#!/usr/bin/env python3
"""Find explicit tactic references to definitions, including core/Mathlib (review inventory)."""
from pathlib import Path
import re,json,runpy
lex=runpy.run_path('evidence/tools/header_lexer.py')
# Reuse the namespace-resolving scanner without running its comparison-tip driver.
namespace={};exec(Path('evidence/tools/name_clash.py').read_text().split('\ncomparisons = ')[0],namespace)
scan=namespace['scan']
helpers=sorted(Path('TCSlib/Cryptography/SecureComputation/Yao/HybridProof').rglob('*.lean'))
refs=[];owned={};locals_={}
for p in helpers:
 source=p.read_text();code,_=lex['lex'](source);owned[str(p)]={r['name'] for r in scan(source) if r['kind'] in ['def','abbrev']}
 locals_[str(p)]=set(re.findall(r'\b(?:let|have)\s+([^\s:(=]+)',code))
 for match in re.finditer(r'\b(simp_all|simp_rw|simp|rw|dsimp)\s*(?:only\s*)?\[',code):
  start=match.end();depth=0;items=[];last=start;j=start
  for j in range(start,len(code)):
   ch=code[j]
   if ch in '([{':depth+=1
   elif ch in ')]}':
    if ch==']' and depth==0:items.append(code[last:j]);break
    depth-=1
   elif ch==',' and depth==0:items.append(code[last:j]);last=j+1
  for item in items:
   head=re.match(r'\s*[←→]?\s*([\w.\u2080-\u209f]+)',item)
   if head:refs.append(dict(path=str(p),line=code[:match.start()].count('\n')+1,tactic=match.group(1),token=head.group(1)))
 for match in re.finditer(r'\b(unfold|delta)\s+([^\n]+)',code):
  for token in re.findall(r'[\w.\u2080-\u209f]+',match.group(2).split(' at ')[0]):refs.append(dict(path=str(p),line=code[:match.start()].count('\n')+1,tactic=match.group(1),token=token))
heads={r['token'].split('.')[-1] for r in refs};catalog={}
roots=[Path('TCSlib'),Path('.lake/packages/mathlib/Mathlib'),Path.home()/'.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init']
files=0
for root in roots:
 for p in root.rglob('*.lean'):
  source=p.read_text();files+=1
  # Cheap prefilter; only parse files with a potentially referenced definition header.
  defs=re.findall(r'^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:def|abbrev)\s+([^\s({\[:=]+)',source,re.M)
  if not any(n.split('.')[-1] in heads for n in defs):continue
  for row in scan(source):
   if row['kind'] in ['def','abbrev'] and row['short'].split('.')[-1] in heads:
    catalog.setdefault(row['name'],[]).append(dict(path=str(p),line=row['line'],kind=row['kind']))
findings=[]
for ref in refs:
 token=ref['token']
 if token in locals_[ref['path']] or token in ['show','if','by','true','false']:continue
 hits=[(name,homes) for name,homes in catalog.items() if name==token or name.endswith('.'+token)]
 if any(name in owned[ref['path']] for name,_ in hits):continue
 if hits:findings.append(dict(**ref,hits=[dict(name=n,homes=h) for n,h in hits]))
out=Path('evidence/unfold');out.mkdir(exist_ok=True)
(out/'explicit-definition-review.json').write_text(json.dumps(dict(files_scanned=files,tactic_references=len(refs),findings=findings),indent=2)+'\n')
print('SCANNED',files,'files;',len(refs),'explicit tactic references;',len(findings),'definition-reference candidates')
for row in findings:print(row['path'],row['line'],row['tactic'],row['token'],[h['name'] for h in row['hits']])
