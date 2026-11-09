from pathlib import Path
import json,hashlib,subprocess,re,collections
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/gates/122-first-halt-reuse/review';head='f3c8c050ef98375bc237c72bde74f83d33833374';g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest();tree={}
for line in g('ls-tree','-r',head).decode().splitlines():
 spec,p=line.split('\t',1)
 if p.startswith('TCSlib/') and p.endswith('.lean'):tree[p]=spec.split()[2]
ids=list(dict.fromkeys(tree.values()));raw=subprocess.check_output(['git','--no-optional-locks','-C',str(R),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode());blob={};at=0
for oid in ids:
 e=raw.index(b'\n',at);n=int(raw[at:e].split()[2]);at=e+1;blob[oid]=raw[at:at+n];at+=n+1
sources={p:blob[oid].decode() for p,oid in tree.items()};graph={p:[m.replace('.','/')+'.lean' for m in re.findall(r'(?m)^(?:public )?import\s+(TCSlib\.[\w.]+)',s)] for p,s in sources.items()}
def chain(a,b):
 q=collections.deque([[a]]);seen={a}
 while q:
  row=q.popleft()
  if row[-1]==b:return row
  for n in graph.get(row[-1],[]):
   if n not in seen:seen.add(n);q.append(row+[n])
 return None
foreign=json.loads((P/'inputs/historical-fh10-e0b/inputs/safe285/FOOTPRINTS17.json').read_text());held=json.loads((O/'SOURCE-VERIFICATION.json').read_text())['held7'];fh={r['suffix']:r for r in foreign};deps=[];capturepaths=set()
for row in held:
 root=fh[row['name'].rsplit('.',1)[-1]];mods={x['owner'].replace('.','/')+'.lean' for x in root['foreign_definition_mentions'] if x['ordinary_guard_target']};reach=[]
 for p in sorted(mods):
  c=chain(row['path'],p);assert c,(row['id'],p);reach.append({'foreign_home':p,'shortest_existing_import_chain':c});capturepaths.add(p)
 deps.append({'id':row['id'],'target':row['name'],'path':row['path'],'direct_imports':graph[row['path']],'full_historical_ordinary_foreign_heads':[x for x in root['foreign_definition_mentions'] if x['ordinary_guard_target']],'ordinary_foreign_home_import_chains':reach,'all_foreign_homes_already_imported':True,'historical_footprint_status':'proposal70abd boundary inventory; source locations/current reads independently rechecked, not a new baseline guard execution'})
# Explicit source lookup of published reader candidates. Full captured homes remain the authority.
reader_specs=[('step_of_some','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('runFrom_zero','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('runFrom_succ','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('runFrom_with_q₀','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('initCfg_eq','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('mem_visitedByTapeHead_iff','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('spaceUsed_eq_sum','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('spaceUsedByTape_eq_card','TCSlib/Complexity/TuringMachine/Deterministic.lean'),('computesFunInTime_iff','TCSlib/Complexity/TuringMachine/Finite.lean'),('computesFunInTimeVia_iff','TCSlib/Complexity/TuringMachine/Finite.lean'),('computesInTime_iff','TCSlib/Complexity/TuringMachine/Finite.lean'),('exists_first_halt','TCSlib/Complexity/TuringMachine/Finite.lean'),('ccfg_state','TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean'),('ccfg_work','TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean'),('PB_ccfg','TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean'),('seam_eq_mkCfg','TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean'),('mkCfg_state','TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean'),('initCfg_eq_bootCfg','TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean')];readers=[]
for name,path in reader_specs:
 hits=[{'line':i,'source_line':l} for i,l in enumerate(sources[path].splitlines(),1) if re.search(r'\b(?:lemma|theorem)\s+'+re.escape(name)+r'\b',l)];assert hits,(name,path);readers.append({'name':name,'path':path,'source_declarations':hits});capturepaths.add(path)
cap=[]
for p in sorted(capturepaths):
 b=blob[tree[p]];d=O/'site-dependencies/source-homes'/(p+'.txt');d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b);cap.append({'path':p,'source':head,'Git_blob':tree[p],'bytes':len(b),'sha256':H(b),'definition_and_reader_source_capture_complete':True})
# Capture direct-import lines and source-only declaration catalogs, including attributes adjacent to definitions.
catalog=[]
for p in sorted(capturepaths):
 lines=sources[p].splitlines()
 for i,l in enumerate(lines):
  if re.match(r'^(?:@\[[^\n]*\]\s*)?(?:private\s+|protected\s+)?(?:def|abbrev|lemma|theorem|structure|class)\s+',l):catalog.append({'path':p,'line':i+1,'source_line':l})
packet={'source':head,'per_held_site':deps,'existing_public_reader_source_lookup':readers,'complete_foreign_home_captures':cap,'source_only_declaration_catalog':catalog,'limits':'Source/import dependency review only. No source changes, new proof, new API, or Lean/native/seal checks. A located existing reader makes only its particular substep mechanical; no whole-target repair is claimed. Lack of a selected source-catalog reader is not a global API absence proof.'};(O/'SITE-DEPENDENCIES.json').write_text(json.dumps(packet,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'held_sites':len(deps),'all_foreign_homes_reachable_without_new_import':True,'complete_captured_homes':len(cap),'located_existing_reader_rows':len(readers),'no_new_execution':True},indent=2))
