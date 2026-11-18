"""Synthetic source import graph for a proposed split. No Lean or source edits."""
from pathlib import Path
import json,re
base=Path('/private/tmp/io-sprg-proof-notes/LPNModularity')
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
mathlib=repo/'.lake/packages/mathlib'
plan=json.loads((base/'move-boundaries.json').read_text())
changes=plan['proposed_imports'];owner=plan['facade'];cache={}
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
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':quote=True;i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
def current(m):
 if m in cache:return cache[m]
 if m.startswith('TCSlib.'):
  p=repo/(m.replace('.','/')+'.lean')
 elif m.startswith('Mathlib.'):
  p=mathlib/(m.replace('.','/')+'.lean')
 else:return []
 if not p.exists():raise RuntimeError('Missing source '+m)
 out=[]
 for l in strip(p.read_text()).splitlines():
  z=re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+)$',l)
  if z:out.extend(z[1].split())
 cache[m]=out;return out
def children(m,new):
 return changes[m] if new and m in changes else current(m)
def closure(root,new):
 todo=[root];seen=set()
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);todo.extend(children(m,new))
 return seen
def cycles(root):
 visiting=set();done=set();route=[]
 def visit(m):
  if m in visiting:raise RuntimeError('Cycle: '+' -> '.join(route+[m]))
  if m in done:return
  visiting.add(m);route.append(m)
  for x in children(m,True):visit(x)
  route.pop();visiting.remove(m);done.add(m)
 visit(root);return len(done)
old=closure(owner,False);new=closure(owner,True)
assert new-old==set(changes)-{owner}
assert not old-new
upstreams={}
for m in changes[owner+'.Defs']:
 c=closure(m,False)
 forbidden=[x for x in c if x in{owner,
  'TCSlib.Cryptography.Obfuscation.StructuredSeed.Security',
  'TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets'}]
 assert not forbidden
 upstreams[m]={'closure_count':len(c),'return_edges_to_facade_security_targets':forbidden}
roots=[owner,'TCSlib.Cryptography.Obfuscation.StructuredSeed.Security',
 'TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets',
 'TCSlib.Cryptography.Obfuscation.StructuredSeed']
checks={r:cycles(r)for r in roots}
result={'status':'STATIC_SOURCE_GRAPH_ONLY',
 'new_owned_modules_only':sorted(new-old),'lost_modules':sorted(old-new),
 'new_external_TCSlib_modules':[],'new_Mathlib_modules':[],
 'acyclic_reachable_roots':checks,'Defs_upstream_return_checks':upstreams,
 'important_distinction':{
 'raw_LPN':'TCSlib.Cryptography.Obfuscation.StructuredSeed.LPN',
 'reduction_facade':owner,
 'base_seed_encoding':'TCSlib.Cryptography.Obfuscation.StructuredSeed.Encoding',
 'new_reduction_encoding':owner+'.Encoding'},'proposed_imports':changes}
(base/'import-cycle-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('Acyclic from LPN facade, Security, Targets and StructuredSeed. Exactly 4 new owned module nodes; no new external TCSlib/Mathlib closure.')
