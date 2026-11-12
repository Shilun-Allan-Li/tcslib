from pathlib import Path
import re,json,hashlib,difflib,shutil
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');F=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');P=A/'native-project';P.mkdir();(P/'.lake').mkdir();(P/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True);(P/'lean-toolchain').write_bytes((W/'lean-toolchain').read_bytes())
base={str(p.relative_to(F/'source-before'))[:-4]:p.read_text() for p in (F/'source-before'/'TCSlib').rglob('*.lean.txt')};assert len(base)==929
sources=dict(base)
for p in (F/'source-current'/'TCSlib').rglob('*.lean.txt'):sources[str(p.relative_to(F/'source-current'))[:-4]]=p.read_text()
cf='TCSlib/Complexity/TuringMachine/CfgFacts.lean';det='TCSlib/Complexity/TuringMachine/Deterministic.lean';sim='TCSlib/Complexity/TuringMachine/Simulation.lean'
api=next(r['full'] for r in json.loads((F/'declaration-freeze.json').read_text())['new_declarations'])
doc='/-- A one-step run from any configuration is exactly one machine step. -/\n';api=doc+api+'\n'
assert api in sources[cf]
sources[cf]=base[cf]
held=json.loads((F/'final-held-imports.json').read_text())
for r in held:
 p=r['path'];line='import TCSlib.Complexity.TuringMachine.CfgFacts\n';assert sources[p].count(line)==1;sources[p]=sources[p].replace(line,'')
# The existing namespace is already Turing.MultiTapeTM. Root qualification keeps
# the exact full public declaration name; every binder/target and proof is copied
# byte for byte from the frozen CfgFacts option.
alt_api=api.replace('theorem MultiTapeTM.runFrom_one','theorem _root_.Turing.MultiTapeTM.runFrom_one',1)
marker="lemma runFrom_succ_eq_step'";a=sources[det].index(marker);b=sources[det].index('/-- Running `a + b`',a)
sources[det]=sources[det][:b]+alt_api+'\n'+sources[det][b:]
old="MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero";assert sources[sim].count(old)==1;sources[sim]=sources[sim].replace(old,'MultiTapeTM.runFrom_one')
graph={p[:-5].replace('/','.'):re.findall(r'^import\s+(\S+)',s,re.M) for p,s in sources.items()};original_graph={p[:-5].replace('/','.'):re.findall(r'^import\s+(\S+)',s,re.M) for p,s in base.items()};assert graph==original_graph
seen=set();active=set();order=[]
def visit(m):
 if m in active:raise RuntimeError('cycle '+m)
 if m in seen:return
 active.add(m)
 for n in graph.get(m,[]):visit(n)
 active.remove(m);seen.add(m);order.append(m)
for m in sorted(graph):visit(m)
def closure(m):
 todo=[m];out=set()
 while todo:
  n=todo.pop()
  if n not in out:out.add(n);todo.extend(graph.get(n,[]))
 return out
visibility=[]
for p,s in sorted(sources.items()):
 path=P/p;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(s)
 if s!=base[p]:
  for folder,text in [('source-before',base[p]),('source-proposed',s)]:
   dst=A/folder/(p+'.txt');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(text)
 if 'MultiTapeTM.runFrom_one' in s:
  m=p[:-5].replace('/','.');c=closure(m);assert det[:-5].replace('/','.') in c,p
  visibility.append({'path':p,'generic_reader_visible':True,'existing_imports_unchanged':graph[m]==original_graph[m],'closure':sorted(c)})
changed=[p for p in sorted(sources) if sources[p]!=base[p]];assert len(changed)==61
patch=''.join(''.join(difflib.unified_diff(base[p].splitlines(True),sources[p].splitlines(True),fromfile='a/'+p,tofile='b/'+p)) for p in changed)
(A/'alternative-complete.patch').write_text(patch)
(A/'alternative-vs-CfgFacts-option.patch').write_text(''.join(''.join(difflib.unified_diff((F/'source-current'/(p+'.txt')).read_text().splitlines(True) if (F/'source-current'/(p+'.txt')).exists() else base[p].splitlines(True),sources[p].splitlines(True),fromfile='CfgFacts-option/'+p,tofile='Deterministic-option/'+p)) for p in sorted(set(changed+[cf]))))
(A/'API-CfgFacts.lean.txt').write_text(api);(A/'API-Deterministic.lean.txt').write_text(alt_api)
assert api.split('runFrom_one',1)[1]==alt_api.split('runFrom_one',1)[1]
(A/'proposal-provenance.json').write_text(json.dumps({'status':'UNAPPROVED ALTERNATIVE: revises explicit CfgFacts-home ruling; no adoption inferred','source_pin':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','records_head':'8e5f2266b6ababbd0784f717e65a4903a0e3a0f0','frozen_CfgFacts_option':str(F),'frozen_CfgFacts_manifest_sha256':'5069e96884fbd28d3f3ca4819c7cd005de4d13b2acfaa3d312ce8e1137b73d56','all929_private_source_project':True,'whole61_changed_owner_captures':changed,'eight_CfgFacts_import_proposals_removed':[r['path'] for r in held],'all_existing_imports_exact_baseline':True,'all929_import_graph_acyclic':True,'Simulation_former_cycle_site_repointed':True,'same_full_public_name':'Turing.MultiTapeTM.runFrom_one','API_binders_target_and_proof_byte_identical':True,'namespace_qualification_only_lexical_difference':'Inside existing namespace Turing.MultiTapeTM, declaration spelled _root_.Turing.MultiTapeTM.runFrom_one. All text after the declaration name is byte-identical.','CfgFacts_exact_baseline_source':sources[cf]==base[cf],'no_source_worktree_Git_or_canonical_mutations':True},indent=2)+'\n')
(A/'all-source-hashes.json').write_text(json.dumps([{'path':p,'baseline_sha256':hashlib.sha256(base[p].encode()).hexdigest(),'alternative_sha256':hashlib.sha256(sources[p].encode()).hexdigest(),'changed':sources[p]!=base[p]} for p in sorted(sources)],indent=2)+'\n')
(A/'import-graph.json').write_text(json.dumps(graph,indent=2)+'\n');(A/'reader-visibility.json').write_text(json.dumps(visibility,indent=2)+'\n')
print('Prepared unapproved alternative61 changed owners;929 private sources; original acyclic imports exactly restored; all reader sites have Deterministic visibility.')
