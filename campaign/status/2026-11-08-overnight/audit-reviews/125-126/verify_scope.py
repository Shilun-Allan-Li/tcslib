from pathlib import Path
import json,re,ast,sys,hashlib,collections,difflib
out=Path(__file__).resolve().parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
def dump(name,d):p=out/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parsed_captures(gate,side,paths):
 helper=gate/'reproduction-tools/copy-text-screen-v3.py';tree=ast.parse(helper.read_text());nodes=[]
 for node in tree.body:
  if isinstance(node,ast.FunctionDef) and node.name in {'strip','scopes','qualify','body'}:nodes.append(node)
  elif isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id in {'DECL','SCOPE'} for t in node.targets):nodes.append(node)
 ns={'re':re,'sys':sys};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper)+'<parser-only>','exec'),ns)
 basenames=collections.Counter(Path(path).name for path in paths);result={}
 for path in paths:
  raw=(gate/'review/source'/side/(path+'.txt')).read_text();text=ns['strip'](raw);matches=list(ns['DECL'].finditer(text));events=ns['scopes'](path,text);found=[]
  for i,m in enumerate(matches):
   end=matches[i+1].start() if i+1<len(matches) else len(text);body=re.sub(r'\s+','',ns['body'](text[m.start():end]));namespace=[n for off,n in events if off<=m.start()][-1]
   if len(body)>=60:found.append((m[3],ns['qualify'](namespace,m[3]),'proof' if m[2] in ('theorem','lemma') else 'term',body))
  shorts=collections.Counter(r[0] for r in found);qualified=collections.Counter(r[1] for r in found);seen=collections.Counter()
  for name,qname,kind,body in found:
   if shorts[name]==1:labelname=name
   elif qualified[qname]==1:labelname=qname
   else:seen[qname]+=1;labelname=qname+'#'+str(seen[qname])
   label=(Path(path).name if basenames[Path(path).name]==1 else path)+'::'+labelname
   assert label not in result;result[label]={'kind':kind,'body':body,'qualified_name':qname,'path':path}
 return result
P=re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%$')
results=[]
for number,slug in [(125,'word-leaves'),(126,'restart-reader')]:
 gate=R/'campaign/gates'/str(number).__add__('-'+slug);review=gate/'review';scope=json.loads((review/'control-evidence-binding.json').read_text());paths=(review/'screen-population.txt').read_text().splitlines();assert len(paths)==len(set(paths))==33
 bodies={side:parsed_captures(gate,side,paths) for side in ['BASE','HEAD']};rows={};headers={}
 for side,name in [('BASE','screen/BASE/screen-BASE.txt'),('HEAD','screen/HEAD.txt')]:
  raw=(review/name).read_text().splitlines();headers[side]=raw[0];pairs={}
  for line in raw[1:]:
   m=P.fullmatch(line);assert m,line;a,b,n,d,pct=m.groups();n=int(n);d=int(d);pct=int(pct);assert a in bodies[side] and b in bodies[side] and d==len(bodies[side][b]['body']) and bodies[side][a]['kind']==bodies[side][b]['kind'];pairs[(a,b)]=(n,d,pct)
  rows[side]=pairs
  dest=out/str(number)/'screen'/Path(name).name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((review/name).read_bytes())
 new=sorted(set(rows['HEAD'])-set(rows['BASE']));gone=sorted(set(rows['BASE'])-set(rows['HEAD']));score=[k for k in set(rows['HEAD'])&set(rows['BASE']) if rows['HEAD'][k]!=rows['BASE'][k]]
 expected=json.loads((review/'screen/pair-delta.json').read_text());assert not new and [(x['target'],x['source']) for x in expected['gone']]==gone
 assert len(rows['BASE'])==2107 and len(rows['HEAD'])=={125:2097,126:2106}[number]
 capture_new=sorted(set(bodies['HEAD'])-set(bodies['BASE']));capture_gone=sorted(set(bodies['BASE'])-set(bodies['HEAD']));body_changed=sorted(k for k in set(bodies['BASE'])&set(bodies['HEAD']) if bodies['BASE'][k]['body']!=bodies['HEAD'][k]['body'])
 assert len(bodies['BASE'])==2433 and len(bodies['HEAD'])=={125:2431,126:2433}[number]
 if number==125:
  assert not capture_new and not body_changed and capture_gone==['Hardness.lean::clA5_pt_head','Hardness.lean::clA5_pt_tail']
  folder=review/'inputs/word-full-two-scopes';pairs=scope['every_control_pair'];assert len(pairs)==scope['positive_kernel_checked_count']==scope['negative_matching_identity_count']==30
  positive=(folder/'HardnessLeaves-controls-native-attempt1.log').read_text();negative=(folder/'HardnessLeaves-controls-sealed-attempt1.log').read_text()
  assert len({x['kernel_name'] for x in pairs})==30 and all(x['kernel_name'] in positive and x['positive_kernel_checked'] and x['negative_same_identity_failed'] for x in pairs)
  for receipt in scope['receipts']:
   run=json.loads((folder/receipt['receipt']).read_text());assert run['exit']==receipt['exit'] and run['errors']==receipt['errors']
   source=folder/receipt['source'];assert source.exists()
  native=(folder/'HardnessLeaves-scope-native-instrumented.lean.txt').read_text();sealed=(folder/'HardnessLeaves-scope-sealed-instrumented.lean.txt').read_text()
  remove=lambda s:'\n'.join(line for line in s.splitlines() if not line.startswith('attribute [local irreducible]'))
  assert remove(native)==remove(sealed)
  mapping=json.loads((folder/'selected-two-chunk-mappings.json').read_text());assert all(native.count(row['new_chunk'])==1 for row in mapping)
  assert sealed.index('attribute [local irreducible]')<min(sealed.index(row['new_chunk']) for row in mapping)
  for name in ['HardnessLeaves-scope-native-instrumented.lean.txt','HardnessLeaves-scope-sealed-instrumented.lean.txt','HardnessLeaves-controls-native.lean.txt','HardnessLeaves-controls-sealed.lean.txt','control-identities.json','definition-inventories.json']:
   target=out/'125/native'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((folder/name).read_bytes())
  assert len(scope['guard_names'])==15 and len(scope['default_simp_definitions_removed_in_both'])==3
 else:
  assert not capture_new and not capture_gone and body_changed==['UniversalK.lean::exists_selfStartupTMK']
  assert len(scope['all_pairs'])==scope['positive_examples_pass']==scope['negative_same_identity_failures']==6
  negative=(review/'inputs/rs1/ControlsSealed.out').read_text();errorlines=[int(x) for x in re.findall(r'ControlsSealed.lean:(\d+):\d+: error: Type mismatch',negative)];assert errorlines==[12,20,28,36,43,50]
  unsealed=(review/'inputs/rs1/ControlsUnsealed.lean.txt').read_text();sealed=(review/'inputs/rs1/ControlsSealed.lean.txt').read_text()
  for pair in scope['all_pairs']:assert unsealed.count(pair['exact_identity'])==sealed.count(pair['exact_identity'])==1
  for name,expected_exit in [('HinitSealed',0),('ControlsUnsealed',0),('ControlsSealed',1)]:
   run=json.loads((review/'inputs/rs1'/(name+'-run.json')).read_text());assert run['exit']==expected_exit
  assert len(scope['ordinary_or_focused_guards'])==3
 # Complete lint stdout retained and exact diff is data; no linter execution claimed here.
 qa=[]
 for kind in ['style-lint','campaign-lint']:
  a=review/'qa'/('BASE-'+kind+'.txt');b=review/'qa'/('HEAD-'+kind+'.txt');diff=''.join(difflib.unified_diff(a.read_text().splitlines(True),b.read_text().splitlines(True),fromfile='BASE',tofile='HEAD'))
  target=out/str(number)/'qa';target.mkdir(parents=True,exist_ok=True)
  for source in [a,b]:(target/source.name).write_bytes(source.read_bytes())
  (target/(kind+'.diff')).write_text(diff);qa.append({'kind':kind,'BASE_sha256':sha(a),'HEAD_sha256':sha(b),'uncapped_diff':str(number)+'/qa/'+kind+'.diff'})
 results.append({'gate':number,'actual33_population':paths,'parser_capture_counts':{k:len(v) for k,v in bodies.items()},'pair_counts':{k:len(v) for k,v in rows.items()},'new_pairs':new,'gone_pairs':[{'target':a,'source':b,'BASE_score':rows['BASE'][(a,b)]} for a,b in gone],'changed_score_pairs':[{'target':a,'source':b,'BASE':rows['BASE'][(a,b)],'HEAD':rows['HEAD'][(a,b)]} for a,b in score],'source_capture_new':capture_new,'source_capture_gone':capture_gone,'source_body_changed':body_changed,'all_other_capture_bodies_exact':True,'control_binding_verified_to_literal_sources_and_original_run_records':True,'guard_scope':scope,'lint_stdout_and_diff':qa})
dump('SCOPE-SCREEN-QA-CHECK.json',{'gates':results,'new_matching_screen_or_Lean_execution':False,'operation':'Pure source extraction, linear raw-pair comparison and original run/source/hash verification only. No lcs/tiling or native replay.'})
print(json.dumps([{'gate':x['gate'],'captures':x['parser_capture_counts'],'pairs':x['pair_counts'],'new':len(x['new_pairs']),'gone':len(x['gone_pairs']),'scores_changed':len(x['changed_score_pairs'])} for x in results]))
