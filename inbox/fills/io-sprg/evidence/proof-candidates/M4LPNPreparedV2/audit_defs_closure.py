"""Independent lexical import/target-absence audit; no Lean, Git or CLI execution."""
from pathlib import Path
import ast,hashlib,json,re
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange');B=Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared')
F=W/'evidence/tools/freeze_global.py';tree=ast.parse(F.read_text())
nodes=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom)) or isinstance(n,ast.FunctionDef) and n.name=='parser_functions']
scope={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(F),'exec'),scope)
C=scope['parser_functions'](W/'evidence/tools/clash/clash_scan.py',{'strip_code','parse_decls'},{'KINDS','MODS','ATTR','DECL_RE','NAME_RE'})
root='TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN.Defs'
probes=json.loads((B/'overlap/exact-probe-index.json').read_text());targets=[p['name'] for p in probes];leaves=[n.rsplit('.',1)[-1] for n in targets]
cache={};bindings={};codecache={}
def children(mod):
 if mod in cache:return cache[mod]
 if mod.startswith('TCSlib.'):p=W/(mod.replace('.','/')+'.lean')
 elif mod.startswith('Mathlib.'):p=W/'.lake/packages/mathlib'/(mod.replace('.','/')+'.lean')
 else:cache[mod]=[];return []
 assert p.exists(),mod
 raw=p.read_bytes();bindings[str(p)]=hashlib.sha256(raw).hexdigest();code=C['strip_code'](raw.decode());codecache[mod]=(p,raw.decode(),code);out=[]
 for line in code:
  m=re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+)$',line)
  if m:out+=m[1].split()
 cache[mod]=out;return out
seen=set();todo=[root]
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);todo+=children(m)
forbidden=[root.removesuffix('.Defs')+x for x in ('','.Transport','.Sections','.Hop','.Encoding')]
forbidden+=['TCSlib.Cryptography.Obfuscation.StructuredSeed.Security','TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets']
assert not (set(forbidden)&seen),set(forbidden)&seen
found={};leafhits=[];declcount=0;localcount=0;external_prefix=[]
for mod,(p,text,code) in codecache.items():
 if mod.startswith('TCSlib.'):
  localcount+=1
  ds=C['parse_decls'](text);declcount+=len(ds)
  for d in ds:
   if d['full'] in targets:found[d['full']]={'module':mod,'line':d['line']}
  for i,line in enumerate(code,1):
   for leaf in leaves:
    if re.search(r'(?<![\w\u0080-\uffff])'+re.escape(leaf)+r'(?![\w\u0080-\uffff])',line):leafhits.append({'leaf':leaf,'module':mod,'line':i})
 elif any('TCSlib.Cryptography.Obfuscation.StructuredSeed' in line for line in code):external_prefix.append(mod)
assert not found,found
assert not leafhits,leafhits
assert not external_prefix,external_prefix
required=['TCSlib.Cryptography.Asymptotic.OneWayLemmas','TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging','TCSlib.Cryptography.Games.Bridges.Experiments','Mathlib.LinearAlgebra.Matrix.Defs']
assert all(m in seen for m in required),[m for m in required if m not in seen]
for file,h in bindings.items():assert hashlib.sha256(Path(file).read_bytes()).hexdigest()==h,file
result={'status':'INDEPENDENT_STATIC_DEFS_CLOSURE_TARGET_ABSENCE_PASS_NOT_LEAN','root':root,'closure_nodes':len(seen),'local_TCSlib_modules_parsed':localcount,'local_TCSlib_declarations_parsed':declcount,'source_modules_hashed':len(bindings),'targets':targets,'target_declarations_found':found,'target_leaf_code_occurrences':leafhits,'excluded_target_owning_or_facade_modules':forbidden,'already_transitive_required_public_API_modules':required,'external_source_owned_namespace_prefix_occurrences':external_prefix,'statement_probe_project_imports':[root],'probe_harness_extra_import':'Lean.Elab.Tactic.LibrarySearch','qualification':'Reviewed lexical parsers and source import graph only; no fresh Lean environment or generated-constant query. All ten exact files use anonymous example declarations. No target helper, dependent later helper, original lpn_hop, reduction facade, Security or Targets is imported. No self-hit or imported-goal assumption is introduced.'}
(B/'overlap/defs-target-absence-audit.json').write_text(json.dumps(result,indent=2)+'\n');(B/'overlap/defs-import-closure.txt').write_text('\n'.join(sorted(seen))+'\n');(B/'overlap/defs-import-source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
print('Independent static pass:',len(seen),'closure nodes;',localcount,'TCSlib modules;',declcount,'parsed declarations; all10 targets absent.')
