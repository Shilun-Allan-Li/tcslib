from pathlib import Path
import re,json,hashlib,collections
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4];WT=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-sg1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def stripped(s):
 out=[];i=0;d=0
 while i<len(s):
  if d:
   if s.startswith('/-',i):d+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):d-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):d=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i]);i+=1
 return ''.join(out)
paths=['TCSlib/Complexity/ClassNP/SAT.lean','TCSlib/Complexity/CookLevin/Hardness.lean']
catalog=[];all_decls={}
for rel in paths+['TCSlib/Complexity/ClassNP/PolyTimePairing.lean']:
 raw=(WT/rel).read_text();s=stripped(raw)
 matches=list(re.finditer(r'(?m)^(?:@\[[^\]]*\]\s*)*(?:private\s+)?(?:noncomputable\s+)?(?:def|abbrev|lemma|theorem|structure|inductive)\s+([^\s({:]+)',s))
 all_decls[rel]=[]
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else len(s);chunk=s[m.start():end];pos=chunk.find(':=');head=chunk[:pos] if pos>=0 else chunk
  row={'file':rel,'name':m.group(1),'line':s[:m.start()].count('\n')+1,'header':head.strip(),'source_span':raw[m.start():end].rstrip(),'source_span_sha256':hashlib.sha256(raw[m.start():end].encode()).hexdigest()};all_decls[rel].append(row)
  if rel in paths and 'PolyTimeComputable' in head:catalog.append(row)
(OUT/'all-polytime-header-candidates.json').write_text(json.dumps(catalog,indent=2)+'\n')
lookup={r['name']:r for rel in paths for r in all_decls[rel]}
repoints={
'sat_pt_mapSnd':('PolyTimeComputable.pairMapSnd + existing pairMapSnd.eq_1 function equality','map_consumer','audit6'),
'clNative_map':('PolyTimeComputable.pairMapSnd + existing pairMapSnd.eq_1 function equality','map_consumer','audit6'),
'sat_pt_pair':('PolyTimeComputable.pairEncode hf hg','pair_consumer','audit6'),
'clNative_pair':('PolyTimeComputable.pairEncode hf hg','pair_consumer','audit6'),
'sat_pt_append':('PolyTimeComputable.append hf hg','append_consumer','audit6'),
'clNative_append':('PolyTimeComputable.append hf hg','append_consumer','audit6'),
'sat_pt_pair_input':('PolyTimeComputable.pairEncode hf polyTimeComputable_id','pair_input_consumer','additional_generic_closure'),
'sat_pt_unaryLength':('polyTimeComputable_unary','unary_length_consumer','additional_generic_closure'),
'clNative_unary':('polyTimeComputable_polyUnary C e','unary_consumer','additional_generic_closure'),
'clNative_linear':('polyTimeComputable_of_linear h','not separately native-tested; exact source public signature','additional_linear_lift'),
'clA5_pt_const':('polyTimeComputable_const w','const_consumer','additional_constant_lift'),
'clA5_pt_cond':('polyTimeComputable_ite hp hf hg','cond_consumer','additional_generic_closure'),
'clA5_pt_and':('polyTimeComputable_and hp hq','and_consumer','additional_generic_closure')}
rows=[]
for name,(replacement,test,kind) in repoints.items():
 r=lookup[name];rows.append({**r,'replacement':replacement,'bounded_probe':test,'classification':kind})
(OUT/'mechanical-repoint-candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
# Check existing named acknowledgments explicitly, not by general similarity.
prior=json.loads((ROOT/'campaign/gates/106-sg1-dedup/review/round2-current/retained-family-rechecks.json').read_text())
accepted_transducer=set(prior['five_kinds']['finite_word_transducer_cfg_run_poly_and_projections'])
assert {'satMap_poly','sat_pt_head','sat_pt_tail'}<=accepted_transducer
# Inspect actual source import reachability, without execution/cache/Git changes.
def deps(m):
 f=WT/(m.replace('.','/')+'.lean')
 if not f.exists():return []
 return re.findall(r'(?m)^import\s+([^\s]+)',stripped(f.read_text()))
closures={}
for rel in paths:
 m=rel.removesuffix('.lean').replace('/','.');seen=set();todo=[m]
 while todo:
  x=todo.pop()
  if x in seen:continue
  seen.add(x);todo.extend(y for y in deps(x) if y.startswith('TCSlib.'))
 closures[rel]={'PolyTimePairing_imported':'TCSlib.Complexity.ClassNP.PolyTimePairing' in seen,'PolyTimeBlockLoop_imported':'TCSlib.Complexity.ClassNP.PolyTimeBlockLoop' in seen,'PolyTimePrefix_imported':'TCSlib.Complexity.ClassNP.PolyTimePrefix' in seen,'TCSlib_module_count':len(seen)}
assert all(x['PolyTimePairing_imported'] for x in closures.values())
(OUT/'import-crosscheck.json').write_text(json.dumps(closures,indent=2)+'\n')
source_count=len(all_decls['TCSlib/Complexity/ClassNP/PolyTimePairing.lean']);assert source_count==26
source_members=['polyTimeComputable_of_linear','polyTimeComputable_const','PolyTimeComputable.pairMapSnd','PolyTimeComputable.pairEncode','PolyTimeComputable.append','polyTimeComputable_unary','polyTimeComputable_polyUnary','polyTimeComputable_ite','polyTimeComputable_and']
assert all(any(r['name']==n for r in all_decls['TCSlib/Complexity/ClassNP/PolyTimePairing.lean']) for n in source_members)
summary={'bounded_header_candidates':len(catalog),'by_file':dict(collections.Counter(r['file'] for r in catalog)),'audit_generic_members':6,'additional_confirmed_generic_closure_members':5,'additional_linear_lift_member':1,'additional_constant_lift_member':1,'mechanically_repointable_total':13,'unrepaired_canonical_PolyTimePairing_source_inclusive_lower_bound':{'members':source_members,'count':9,'denominator':26,'fraction':9/26,'one_fifth_crossing':True,'not_acknowledged_or_exhaustive':True},'already_direct_public_adapters':['sat_pt_linear','sat_pt_const','sat_pt_cond','sat_pt_and','sat_comp_on_image'],'explicit_existing_transducer_scope':['satMap_poly','sat_pt_head','sat_pt_tail'],'separate_candidates_not_cleared':{'clNative_image':'Generic polynomial composition correct only on source image. No exact class-level public theorem found in bounded ClassNP search; public PolyTimeComputable.comp has total correctness premise, not this weaker image premise. Do not call acknowledged/clean or infer API necessity from this bounded check.','clNative_fill':'Bit-parametric length-preserving native scan; true specialization matches unaryLength, but complete arbitrary-bit contract has no exact public FP closure identified in this bounded search. Not counted as confirmed canonical duplicate.','clA5Iter_native':'Generic iteration candidate; existing PolyTimeBlockLoop public loop family is not imported by either file. No exact statement/repoint was tested here; no import/API/debt permission inferred.',
'other_header_candidates':'Many mention private client encodings/numeric operators/fields. Full raw catalogue retained; not a semantic all-repository audit or acknowledgment.'}}
(OUT/'scope-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
receipt=json.loads((ROOT/'campaign/gates/106-sg1-dedup/findings-r2-receipt.json').read_text());f=ROOT/'campaign/gates/106-sg1-dedup/findings-r2.md';assert f.stat().st_size==receipt['bytes'] and sha(f)==receipt['sha256'];(OUT/'findings-r2.received.txt').write_bytes(f.read_bytes())
inputs={str(p):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in [f,ROOT/'campaign/gates/106-sg1-dedup/findings-r2-receipt.json',ROOT/'campaign/duplication-ledger.md',ROOT/'campaign/gates/106-sg1-dedup/resolutions.md']+[WT/r for r in paths+['TCSlib/Complexity/ClassNP/PolyTimePairing.lean','TCSlib/Complexity/ClassNP/NP.lean','TCSlib/Complexity/ClassNP/PolyTime.lean']]}
(OUT/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
print(json.dumps(summary,indent=2)[:2600])
