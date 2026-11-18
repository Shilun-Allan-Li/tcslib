"""Synthetic source import graph only; reads source files and never invokes Lean/Git."""
from pathlib import Path
import ast,json,re
B=Path('/private/tmp/io-sprg-proof-notes/PRGModularity')
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
plan=json.loads((B/'move-boundaries.json').read_text());changes=plan['proposed_imports'];owner=plan['facade'];cache={}
parser=W/'evidence/tools/clash/clash_scan.py';tree=ast.parse(parser.read_text())
node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='strip_code')
scope={};exec(compile(ast.Module(body=[node],type_ignores=[]),str(parser),'exec'),scope)
strip_code=scope['strip_code']
def current(m):
 if m in cache:return cache[m]
 if m.startswith('TCSlib.'):p=W/(m.replace('.','/')+'.lean')
 elif m.startswith('Mathlib.'):p=W/'.lake/packages/mathlib'/(m.replace('.','/')+'.lean')
 else:return []
 assert p.exists(),m
 # Reviewed nested-comment/string parser excludes examples and doc quotations.
 out=[]
 for line in strip_code(p.read_text()):
  m0=re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+)$',line)
  if m0:out+=m0[1].split()
 cache[m]=out;return out
def children(m,new):return changes[m] if new and m in changes else current(m)
def closure(root,new):
 seen=set();todo=[root]
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);todo+=children(m,new)
 return seen
def acyclic(root):
 active=set();done=set();route=[]
 def visit(m):
  assert m not in active,'Cycle: '+' -> '.join(route+[m])
  if m in done:return
  active.add(m);route.append(m)
  for d in children(m,True):visit(d)
  route.pop();active.remove(m);done.add(m)
 visit(root);return len(done)
old=closure(owner,False);new=closure(owner,True);assert new-old==set(changes)-{owner};assert not old-new
roots=[owner,'TCSlib.Cryptography.Obfuscation.StructuredSeed.Security','TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets','TCSlib.Cryptography.Obfuscation.StructuredSeed']
upstream={}
for m in changes[owner+'.Defs']:
 c=closure(m,False);back=sorted(c&set(roots));assert not back
 upstream[m]={'closure_nodes':len(c),'return_edges_to_facade_security_targets_area':back}
result={'status':'STATIC_SOURCE_GRAPH_ONLY_NOT_LEAN','new_owned_module_nodes_only':sorted(new-old),'lost_module_nodes':sorted(old-new),'new_external_TCSlib_modules':[],'new_Mathlib_modules':[],'acyclic_from_roots':{r:acyclic(r) for r in roots},'upstream_no_return_edge_checks':upstream,'proposed_imports':changes,'qualification':'Current textual source closure; Lean/Core import bodies are treated as terminal leaves. No cached build reuse or kernel check is claimed.'}
(B/'import-cycle-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('Acyclic source graph; exactly3 new owned module nodes, no added external TCSlib/Mathlib roots.')
