"""Read-only source import graph. Does not invoke Lean, git, or any subprocess."""
from pathlib import Path
import json,re
base=Path('/private/tmp/io-sprg-proof-notes/OverlapAlgebra')
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
mathlib=repo/'.lake/packages/mathlib'
if not (mathlib/'Mathlib').exists():
 mathlib=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/packages/mathlib')
index=json.loads((base/'probe-index.json').read_text())
cache={}
def strip(s):
 out=[];i=0;depth=0;quote=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif quote:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quote=False;i+=1
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s)if j<0 else j
  elif s[i]=='"':quote=True;i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
def children(m):
 if m in cache:return cache[m]
 if m.startswith('TCSlib.'):
  p=repo/(m.replace('.','/')+'.lean')
 elif m.startswith('Mathlib.'):
  p=mathlib/(m.replace('.','/')+'.lean')
 else:return []
 if not p.exists():raise RuntimeError('Unresolved project/Mathlib module '+m)
 result=[]
 for line in strip(p.read_text()).splitlines():
  mm=re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+)$',line)
  if mm:result.extend(mm[1].split())
 cache[m]=result;return result
def closure(roots):
 todo=list(roots);seen=set()
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);todo.extend(children(m))
 return seen
rows={}
for r in index:
 c=closure(r['imports']);owned=sorted(m for m in c if m.startswith('TCSlib.Cryptography.Obfuscation.'))
 current=closure(['TCSlib.Cryptography.Obfuscation.StructuredSeed.'+r['family']])
 rootsmissing=sorted(m for m in r['imports']if m not in current)
 assert not owned,(r['name'],owned)
 assert not rootsmissing,(r['name'],rootsmissing)
 rows[r['name']]={'closure_size':len(c),'Obfuscation_modules':owned,
  'direct_roots_not_in_owner_closure':rootsmissing,
  'TCSlib_modules':sorted(m for m in c if m.startswith('TCSlib.'))}
(base/'import-exclusion-audit.json').write_text(json.dumps({
 'method':'Comment/string aware static source graph; Lean/Std/Init/external library modules terminal.',
 'mathlib_read_path':str(mathlib),'all29_exclude_all_Obfuscation':True,
 'all_direct_roots_in_current_owner_closure':True,'probes':rows},indent=2)+'\n')
print('Static import graph: all 29 exclude every Obfuscation module; every direct root is already in its owner closure.')
