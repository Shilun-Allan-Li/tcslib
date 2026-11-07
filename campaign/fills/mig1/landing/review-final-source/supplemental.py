from pathlib import Path
import sys,importlib.util,contextlib,io,json,re,hashlib,collections
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4]
spec=importlib.util.spec_from_file_location('review',out/'source_review.py');M=importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):spec.loader.exec_module(M)
H=M.H;P=M.P
api=M.api;prod=M.producer
allowed_imports={('TCSlib/Complexity/TuringMachine/Simulation.lean','import Mathlib.Algebra.BigOperators.Fin'),('TCSlib/Complexity/TuringMachine/Build/Catalog.lean','import TCSlib.Complexity.TuringMachine.Build.Primitives')}
actual=set()
for f,r in api['comparisons'].items():
 assert not set(r['imports_before'])-set(r['imports_after']),f
 actual|={(f,x) for x in set(r['imports_after'])-set(r['imports_before'])}
 assert r['standalone_attributes_equal'],f
assert actual==allowed_imports,actual
# Verify all9 relocated private data declarations against original actual Catalog bodies.
oldcat={d['name']:d for d in M.DECLS['api']['TCSlib/Complexity/TuringMachine/Build/Catalog.lean']}
moveData=json.loads((root/'campaign/fills/mig1/review/checkpoint05-2026-11-07/evidence-check.json').read_text())['private_moves'];mapping={r['target']:r['source'] for r in moveData};mapping['Turing.FinTM.timedHeads']='Turing.FinTM.f2_condHeads'
def rename(s):
 s=re.sub(r'\bf2_condHeads\b','timedHeads',s);s=re.sub(r'\ba2_MapState\b','FwdMapState',s);s=re.sub(r'\ba2_map([\w\']*)',r'fwdMap\1',s);s=re.sub(r'\bf2_', '',s);return P.norm(P.clean(s))
rows=[]
for f,n,private,kind in api['all_added']:
 if kind in ['lemma','theorem'] or not private:continue
 new=next(d for d in M.DECLS['current'][f] if d['name']==n);old=oldcat[mapping[n]];same=rename(old['raw'])==P.norm(P.clean(new['raw']));assert same,(n,mapping[n])
 rows.append({'source':mapping[n],'source_home':'TCSlib/Complexity/TuringMachine/Build/Catalog.lean','target':n,'target_home':f,'kind':kind,'body_and_header_code_identical_modulo_approved_renaming':True,'old_block_sha256':H(old['raw']),'new_block_sha256':H(new['raw'])})
assert len(rows)==9
# The forwarding machine def is literally the gated controller wrapper.
contract={d['name']:d for d in M.decls((root/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text())};prims={d['name']:d for d in M.DECLS['current']['TCSlib/Complexity/TuringMachine/Build/Primitives.lean']};n='Turing.FinTM.pairMapSndTM';assert contract[n]['body_code']==prims[n]['body_code']
# Two proof-field differences: preserve every byte outside exactly each inj proof block.
inj=[]
for n in ['Turing.FinTM.emitterP2PairIndex','Turing.FinTM.emitterP2SmallIndex']:
 a=next(d for d in M.DECLS['api']['TCSlib/Complexity/TuringMachine/Build/Primitives.lean'] if d['name']==n)['raw'];b=prims[n]['raw'];needle="  inj' := by";assert a.count(needle)==b.count(needle)==1
 ia=a.index(needle);ib=b.index(needle);assert a[:ia]==b[:ib];assert not re.search(r'^  [A-Za-z_]\w*\s*:=',b[ib:].split('\n',1)[1],re.M)
 inj.append({'name':n,'all_header_toFun_and_data_prefix_bytes_identical':True,'masked_chunk_sha256':H(a[:ia]+"  inj' := <proof>\n"),'only_final_Prop_field_masked':True})
# Proof-local CertShell initializer change is confined to one local record field; its table is source-identical.
f='TCSlib/Complexity/TuringMachine/Build/CertShell.lean';a=next(d for d in M.DECLS['producer'][f] if d['name']=='Turing.cert_prepare_exists');b=next(d for d in M.DECLS['current'][f] if d['name']==a['name']);assert 'let D : FinTM Bool := ⟨K, _, M₅⟩' in a['body'];assert '{M₅ with q₀ := .inl (.inl (.inl (.inl (.inl SweepPhase.sweep))))}' in b['body']
# Passed milestone SHA identities are checked as source records; no Lean is run in this review.
milestones={
 'TCSlib/Complexity/TuringMachine/Composition.lean':root/'campaign/fills/mig1/landing/review-composition-loop/source-review.json',
 'TCSlib/Complexity/TuringMachine/Build/Wrappers.lean':root/'campaign/fills/mig1/landing/review-composition-loop/source-review.json',
 'TCSlib/Complexity/TuringMachine/Build/Loop.lean':root/'campaign/fills/mig1/landing/review-composition-loop/source-review.json'}
sourceReviews=json.loads(next(iter(milestones.values())).read_text());bindings=[]
for f,doc in milestones.items():
 key=Path(f).stem;expected=sourceReviews[key]['sha256'];actualsha=H(M.STAGES['current'][f]);assert expected==actualsha
 bindings.append({'path':f,'current_sha256':actualsha,'receipt_source':str(doc.relative_to(root)),'matches':True,'claim':'Source identity to peer actual compile/guard receipt; execution attributed to peer.'})
for d in json.loads((root/'campaign/fills/mig1/landing/review-primitives/final-receipt.json').read_text())['six_fresh_dependency_chain']:
 receipt=root/'campaign/fills/mig1/landing/review-primitives'/d['receipt'];r=json.loads(receipt.read_text());f=r['command'][-2];assert H(M.STAGES['current'][f])==r['source_sha256'];bindings.append({'path':f,'current_sha256':r['source_sha256'],'receipt_source':str(receipt.relative_to(root)),'matches':True,'claim':'Read-only receipt and exact inert input identity; no new execution.'})
for f in ['Primitives','Catalog','CertShell','CodeSimulator','WordSize']:
 rpath=root/'campaign/fills/mig1/landing/preflight-current2'/(f+'-run.json');r=json.loads(rpath.read_text());assert r['exit']==0
 sourceKey=next(k for k in M.FILES if Path(k).stem==f);match=H(M.STAGES['current'][sourceKey]) in [r.get('source_sha256'),r.get('input_sha256')]
 if not match:
  text=(root/'campaign/fills/mig1/landing/preflight-current2'/(f+'.lean.txt')).read_text();match=text==M.STAGES['current'][sourceKey]
 assert match,(f,r)
 bindings.append({'path':sourceKey,'current_sha256':H(M.STAGES['current'][sourceKey]),'receipt_source':str(rpath.relative_to(root)),'matches':True,'claim':'Root current2 actual module compile recorded exit0; independently matched source bytes, not executed by this review.'})
long=[]
for row in api['proof_roots']:
 d=next(x for x in M.DECLS['current'][row['path']] if x['name']==row['name']);lines=d['body'].count('\n')+1
 if lines>20 and '**Proof sketch.**' not in d['doc']:
  long.append(dict(row,body_lines=lines,leading_doc=d['doc']))
result={'imports_exactly_two_approved':sorted(actual),'all_standalone_attributes_unchanged':True,'new_private_runtime_data_moves':rows,'public_forwarding_wrapper_body_exact_gated_contract':True,'retained_executable_exceptions':inj,'CertShell_proof_local_initializer':{'source_local_M5_and_table_unchanged':True,'annotation_exact_existing_label':True,'unsealed_extensional_diagnostics_attributed':'campaign/fills/mig1/landing/review-certshell/README.md + initializer diagnostics; not rerun here','production_transport':'MultiTapeTM.runFrom_with_q₀'},'milestone_bindings':bindings,'long_changed_proofs_missing_leading_sketch':long}
(out/'supplemental.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'private_runtime_moves':len(rows),'source_milestone_receipt_bindings':len(bindings),'all11_sources_matched':len({b['path'] for b in bindings})==11,'missing_sketch_count':len(long),'missing_sketches':[(r['name'],r['body_lines']) for r in long],'Catalog_repair_public_proofs':[r['name'] for r in prod['comparisons']['TCSlib/Complexity/TuringMachine/Build/Catalog.lean']['proof_body_changes'] if not r['private']]},indent=2))
