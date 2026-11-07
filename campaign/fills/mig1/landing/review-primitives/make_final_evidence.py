"""Freeze owned proof repairs and wrap the exact 42+21 strong-seal population."""
from pathlib import Path
import os,sys,importlib.util,json,hashlib,difflib,re
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4]
p=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad/TCSlib/Complexity/TuringMachine/Build/Primitives.lean';data=p.read_bytes();text=data.decode();copy=out/'milestone3-source.lean.txt';assert copy.read_bytes()==data
H=lambda s:hashlib.sha256(s if isinstance(s,bytes) else s.encode()).hexdigest();N=lambda s:'Turing.FinTM.'+s
spec=importlib.util.spec_from_file_location('compare',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
baseline=(out/'baseline.lean.txt').read_text();m1=(out/'milestone1-source.lean.txt').read_text();old={d['name']:d for d in m.decls(baseline)};before={d['name']:d for d in m.decls(m1)};new={d['name']:d for d in m.decls(text)}
assert set(old)-set(new)=={N('catalogRewind')};adds=sorted(set(new)-set(old));assert len(adds)==7
assert all(new[n]['private'] and new[n]['kind']=='lemma' for n in adds)
assert all(old[n]['header']==new[n]['header'] for n in set(old)&set(new))
assert [x['name'] for x in m.decls(baseline) if x['name'] in new]==[x['name'] for x in m.decls(text) if x['name'] in old]
assert [l for l in baseline.splitlines() if l.startswith('import ')]==[l for l in text.splitlines() if l.startswith('import ')]
assert old[N('emitter_first_entry')]['raw']==new[N('emitter_first_entry')]['raw']
proofdefs={N('emitterP2SmallIndex'),N('emitterP2PairIndex')};masked=[]
for n in old.keys()&new.keys():
 if old[n]['kind'] in ['def','abbrev','inductive','structure','instance'] and old[n]['raw']!=new[n]['raw']:
  assert n in proofdefs,n
  mask=lambda x:x[:x.index("  inj' := by")]+"  inj' := <AUTHORIZED_PROOF_FIELD>\n"
  assert mask(old[n]['raw'])==mask(new[n]['raw']),n
  masked.append({'name':n,'exact_inj_field_only':True,'masked_sha256':H(mask(old[n]['raw'])),'before_sha256':H(old[n]['raw']),'after_sha256':H(new[n]['raw'])})
assert {x['name'] for x in masked}==proofdefs
# T1 four caller bodies are identical modulo their one callee identifier each.
t1=list(map(N,['lenStart','splitRestore_run','splitBody_rewind','emitterP2_prepare_run']));t1rows=[]
for n in t1:
 a=before[n]['raw'];b=new[n]['raw'];assert a.count('catalogRewind')==1 and a.replace('catalogRewind','timed_rewind')==b,n
 t1rows.append({'name':n,'exact_single_callee_substitution':True,'before_sha256':H(a),'after_sha256':H(b)})
# Strip only exterior whitespace after the parser blanks trailing comments; real token content remains exact.
changed_after_m1=sorted(n for n in before.keys()&new.keys() if before[n]['code'].strip()!=new[n]['code'].strip());targets=sorted((set(adds)|set(changed_after_m1))-set(t1));assert len(targets)==21,(len(targets),targets)
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b','\n'.join(d['code'] for d in m.decls(text)))
freeze={'source_sha256':H(data),'bytes':len(data),'lines':text.count('\n'),'all_surviving_headers_visibility_order_unchanged':True,'imports_identical':True,'public_source_delta':0,'new_declarations':adds,'all_new_private_proof_lemmas':True,'removed_declarations':[N('catalogRewind')],'runtime_definition_freeze':'All original def/abbrev/inductive/structure/instance chunks raw-byte identical except the exact authorized inj proof fields below.','proof_field_exceptions':masked,'emitter_first_entry_byte_identical':True,'changed_after_milestone1':changed_after_m1,'additional_strong_seal_targets':targets,'sorry_admit_axiom_unsafe_absent':True,'four_T1_callers_outside_strong_region_claim':t1rows,'T1_scope':'Parent confirmed exact four identifier substitutions, byte equality modulo swaps and whole-source compile suffice for mechanical retirement; no broader legacy-body seal claim.'}
(out/'milestone3-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n');(out/'milestone3.sha256').write_text(H(data)+'  milestone3-source.lean.txt\n');(out/'final-proof-repair.diff').write_text(''.join(difflib.unified_diff(baseline.splitlines(keepends=True),text.splitlines(keepends=True),fromfile='baseline-af3273f75/Primitives.lean',tofile='current-owned/Primitives.lean')))
base_manifest=json.loads((out/'Full-sections-sealed-v1-manifest.json').read_text());names=sorted({r['name'] for r in base_manifest['regions']}|set(targets));assert len(names)==63
irr=json.loads((out/'controls36-additions.json').read_text())['definitions'];assert len(irr)==len(set(irr))==36
all_decls=[x.start() for x in re.finditer(r'^(?:private )?(?:lemma|theorem|def|abbrev|inductive|instance|structure)\b',text,re.M)];docs=[x.start() for x in re.finditer(r'^/--',text,re.M)];stops=[x.start() for x in re.finditer(r'^(?:end |namespace |attribute |section )',text,re.M)];regions=[]
for i,name in enumerate(names):
 short=name.removeprefix('Turing.FinTM.');matches=list(re.finditer(r'^(?:private )?(?:lemma|theorem|def|inductive|instance)\s+'+re.escape(short)+r'(?=\s|[(:{])',text,re.M));assert len(matches)==1,name;ds=matches[0].start();pd=max([x for x in all_decls if x<ds],default=-1);pc=max([x for x in docs if x<ds],default=-1);start=pc if pc>pd else ds;end=min([x for x in all_decls+docs+stops if x>ds],default=len(text));header='section PrimitivesFinalSeal'+str(i)+'\nattribute [local irreducible] '+' '.join(irr)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n';footer='\nend PrimitivesFinalSeal'+str(i)+'\n';regions.append({'name':name,'start':start,'end':end,'header':header,'footer':footer,'source_chunk_sha256':H(text[start:end])})
sr=sorted(regions,key=lambda r:r['start']);assert all(a['end']<=b['start'] for a,b in zip(sr,sr[1:]));result=text
for r in reversed(sr):result=result[:r['start']]+r['header']+result[r['start']:r['end']]+r['footer']+result[r['end']:]
restored=result
for r in regions:restored=restored.replace(r['header'],'',1).replace(r['footer'],'',1)
assert restored==text
q=out/'Final-sections-sealed-v1.lean.txt';assert not q.exists();q.write_text(result)
(out/'Final-sections-sealed-v1-manifest.json').write_text(json.dumps({'source_sha256':H(data),'sealed_input_sha256':H(result),'definitions':irr,'sections':63,'restores_exact_source':True,'four_T1_caller_legacy_bodies_not_strong_sealed':t1,'regions':regions},indent=2)+'\n')
print(json.dumps({'sha256':H(data),'bytes':len(data),'lines':text.count('\n'),'new_private_lemmas':adds,'strong_seal_sections':len(regions),'strong_seal_definitions':len(irr),'T1_only_callee_repoints':t1},indent=2))
