"""Exact import-following static overlay audit. No Lean/Git/cache or source writes."""
from pathlib import Path
import ast
import hashlib
import json
import re

W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/LPNModularityFull')
P=Path('/private/tmp/io-sprg-proof-notes/PRGModularity')
owner='TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN'
prg='TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG'
# Pure comment/string lexer only: do not execute parser CLI or Git helpers.
tree=ast.parse((W/'evidence/tools/clash/clash_scan.py').read_text());nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='strip_code']
lex={};exec(compile(ast.Module(body=nodes,type_ignores=[]),'<reviewed-pure-strip-code>','exec'),lex)

def imports(source):
 result=[]
 for line in lex['strip_code'](source):
  m=re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+?)\s*$',line)
  if m:result.extend(m[1].split())
 return result

lpnoverlay={owner+'.'+leaf:imports((B/(leaf+'.lean.template')).read_text()) for leaf in ['Defs','Encoding','Transport','Hop']}
lpnoverlay[owner]=imports((B/'Facade.lean.template').read_text())
expected=json.loads((B/'template-validation.json').read_text())['proposed_imports']
assert lpnoverlay==expected
prgoverlay={prg+'.'+leaf:imports((P/(leaf+'.lean.template')).read_text()) for leaf in ['Defs','Encoding','Hop']}
prgoverlay[prg]=imports((P/'Facade.lean.template').read_text())
cache={};source_sha={}
def current(module):
 if module in cache:return cache[module]
 assert module=='TCSlib' or module.startswith('TCSlib.')
 path=W/(module.replace('.','/')+'.lean');raw=path.read_bytes();source_sha[module]=hashlib.sha256(raw).hexdigest()
 cache[module]=imports(raw.decode());return cache[module]
def walk(root,overlay):
 done=set();active=[];external=set()
 def visit(module):
  if module in active:raise RuntimeError('Cycle: '+' -> '.join(active+[module]))
  if module in done:return
  if module!='TCSlib' and not module.startswith('TCSlib.'):
   external.add(module);return
  active.append(module)
  for child in overlay[module] if module in overlay else current(module):visit(child)
  active.pop();done.add(module)
 visit(root);return done,external
roots=[owner,'TCSlib.Cryptography.Obfuscation.StructuredSeed.Security',
 'TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets','TCSlib.Cryptography.Obfuscation.StructuredSeed']
results={}
for label,overlay,added in [('LPN_only',lpnoverlay,set(lpnoverlay)-{owner}),
 ('LPN_and_PRG',dict(lpnoverlay,**prgoverlay),(set(lpnoverlay)-{owner})|(set(prgoverlay)-{prg}))]:
 checks={}
 for root in roots:
  before,be=walk(root,{})
  after,ae=walk(root,overlay)
  expected_new=added if root!=owner else set(lpnoverlay)-{owner}
  assert after-before==expected_new,(label,root,after-before,expected_new)
  assert not before-after and ae==be,(label,root,'external root delta')
  checks[root]={'acyclic':True,'old_TCSlib_nodes':len(before),'new_TCSlib_nodes':len(after),
   'exact_new_owned_nodes':sorted(after-before),'lost_old_nodes':[],
   'new_external_modules':sorted(ae-be),'removed_external_modules':sorted(be-ae),
   'direct_Mathlib_root_count':sum(m=='Mathlib' or m.startswith('Mathlib.') for m in ae)}
 results[label]=checks
for module in lpnoverlay[owner+'.Defs']:
 closure,external=walk(module,{})
 assert not closure&{owner,'TCSlib.Cryptography.Obfuscation.StructuredSeed.Security',
 'TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets'}
report={'status':'STATIC_IMPORT_FOLLOWING_ONLY_NOT_COMPILED','LPN_overlay':lpnoverlay,
 'combined_PRG_overlay':prgoverlay,'checks':results,
 'scope':'Follow exact TCSlib import paths, treat Lean/Mathlib/other package imports as external roots; no broad filesystem scan or Mathlib recursion. External root sets remain exactly equal.',
 'source_sha256':source_sha,'new_LPN_children':4,'combined_new_children':7,
 'expected_total_owners_after_LPN_only':30,'expected_total_owners_after_both_splits':33,
 'new_Mathlib_cache_roots':[],'generated_kernel_types_checked':False}
(B/'import-cycle-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print('LPN4 and combined LPN4+PRG3 acyclic from4 roots; no lost modules or external/cache-root delta')
