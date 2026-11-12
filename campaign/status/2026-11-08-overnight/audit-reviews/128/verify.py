from pathlib import Path
import json,hashlib,subprocess,re,datetime,ast,sys
out=Path(__file__).resolve().parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');X=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange');I=Path('/private/tmp/ab34-audit-intake-128-xqztge16');gate=R/'campaign/gates/128-ladner-statements';review=gate/'review';v=review/'evidence/actual-validation162'
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def git(repo,*args):return subprocess.check_output(['git','-C',str(repo),*args])
def get(repo,rev,path):return git(repo,'show',rev+':'+path)
def cp(src,name):p=out/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(src.read_bytes())
def dump(name,d):p=out/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
pub=j(gate/'publication.json');H=pub['source'];B='9b5dcf46408db681bcbc721930ef2203fa6bc47d';old='63eb044c55032d8d9570e54e99d520522f2449e5'
assert H=='1096e50b4e105392737ec52939b1db0cdbd9316d' and pub['records']=='be1fbf132ebdca9e6fdfbe73d97d045eaa9e4c8b' and pub['exchange']=='975a34b566e0ecfd26352792703fb2b049c7399a' and pub['sections']==885
report=I/'gate128-ladner-statements-findings.md';assert sha(report.read_bytes())=='b5f4ea4caa516da59fe05bba89e74fe240d88df14dcd4a46c27a90b37e3ab268';cp(report,'findings-original.md');cp(I/'INTAKE.json','INTAKE.json')
for repo,rev in [(R,H),(R,B),(R,old),(R,pub['records']),(X,pub['exchange'])]:assert git(repo,'rev-parse',rev+'^{commit}').decode().strip()==rev;git(repo,'cat-file','-e',rev+'^{commit}')
folder=pub['folder'];bundle=get(X,pub['exchange'],folder+'/128-ladner-statements-bundle.md');listing=get(X,pub['exchange'],folder+'/BUNDLE-FILES.txt').decode().splitlines();assert sha(bundle)==pub['sha256'] and len(bundle)==pub['bytes'] and len(listing)==len(set(listing))==885
markers=list(re.finditer(rb'(?m)^## ===== (.*?) =====\n\n',bundle));assert [x[1].decode() for x in markers]==listing
section_rows=[]
for index,m in enumerate(markers):
 path=listing[index];rev=H if path.endswith('.lean') else pub['records'];expected=get(R,rev,path);end=markers[index+1].start() if index+1<len(markers) else len(bundle);section=bundle[m.end():end];wrapper=None
 if section.startswith(b'```') and not section.startswith(expected):
  first=section.index(b'\n')+1;fence=section[:first].split()[0];last=section.rfind(fence);assert last>=first and not section[last+len(fence):].strip(b'\n');wrapper=section[:first].decode().strip();section=section[first:last]
 assert section.startswith(expected) and not section[len(expected):].strip(b'\n'),path
 section_rows.append({'path':path,'revision':rev,'bytes':len(expected),'sha256':sha(expected),'fence_envelope':wrapper,'payload_exact_Git':True})
for line in get(X,pub['exchange'],folder+'/SHA256SUMS').decode().splitlines():
 digest,name=line.split(maxsplit=1);assert sha(get(X,pub['exchange'],folder+'/'+name.strip()))==digest
for n in ['publication.json','prompt.md','pack.md','BUNDLE-FILES.txt','adoption.json']:cp(gate/n,n)
assert sha((gate/'prompt.md').read_bytes())==pub['prompt_sha256']
manifest=j(review/'MANIFEST.json');assert sha((review/'MANIFEST.json').read_bytes())=='58a2dbe4517714ebfab50a673f09d942c937f64ab3340ad979d1c07c2e390200' and len(manifest['files'])==777
for row in manifest['files']:
 b=(review/row['path']).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes'];assert get(R,pub['records'],'campaign/gates/128-ladner-statements/review/'+row['path'])==b,row['path']
cp(review/'MANIFEST.json','original777-MANIFEST.json')
def lmap(pin):return {l.split('\t',1)[1]:l.split()[2] for l in git(R,'ls-tree','-r',pin).decode().splitlines() if l.split('\t',1)[1].endswith('.lean')}
bm=lmap(B);hm=lmap(H);owner='TCSlib/Complexity/Diagonalization/Ladner.lean';facade='TCSlib/Complexity/Diagonalization.lean';assert len(bm)==1003 and len(hm)==1004 and owner not in bm and [k for k in sorted(set(bm)|set(hm)) if bm.get(k)!=hm.get(k)]==[facade,owner]
owner_bytes=get(R,H,owner);assert sha(owner_bytes)=='166c77cc4d86b0ae1a4e2d32967628cc5f3f4710c7ec5fc0cedbde5c75333311' and owner_bytes==get(R,old,owner) and get(R,B,'TCSlib.lean')==get(R,H,'TCSlib.lean')
helper=review/'reproduction-tools/copy-text-screen-v3.py';tree=ast.parse(helper.read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='strip');ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),'strip-only','exec'),ns)
assert ns['strip'](owner_bytes.decode())==ns['strip']((review/'evidence/prototype132/Ladner-v2.lean.txt').read_text())
assert ns['strip'](get(R,H,facade).decode()).replace('import TCSlib.Complexity.Diagonalization.Ladner\n','')==ns['strip'](get(R,B,facade).decode())
selected=j(v/'SELECTED17-METADATA.json');raw=(v/'attempts/03-imported-inventory-lock-access/raw.out').read_text();raw_rows=[json.loads(line.split('ABI|',1)[1]) for line in raw.splitlines() if 'ABI|' in line];assert raw_rows==selected and len(selected)==17
sorry=[r['source_name'] for r in selected if 'sorryAx' in r['axioms']];assert len(sorry)==7 and 'Complexity.ladner' in sorry and all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in selected if r['source_name'] not in sorry)
foot=j(v/'FOREIGN-FOOTPRINT.json');assert len(foot['guard_names'])==9 and len(foot['complete_definition_records'])==146 and len(foot['theorem_boundaries'])==6 and all(not r['proof_value_traversed'] for r in foot['theorem_boundaries'])
ax=j(v/'AX-AND-CONTROL-COMPARISON.json');assert ax['full17_imported_native_sealed_AX_sets_exact'] and ax['all6_edge_AX_standard_only'] and ax['native_sealed_edge_AX_sets_exact'] and ax['same18_control_identity_pairs_effective'] and len(ax['complete_identity_pairs'])==18
for attempt,exit,errors,warnings in [('03-imported-inventory-lock-access',0,0,0),('04-whole-owner-edges-native',0,0,6),('05-controls-native',0,0,0),('06-whole-owner-edges-sealed',0,0,6),('07-controls-sealed',1,18,0)]:
 r=j(v/'attempts'/attempt/'run.json');assert (r['exit'],r['errors'],r['sorry_warnings'])==(exit,errors,warnings)
actual=j(v/'inputs/passed-Nlad2/RESULT.json');assert actual['pass'] and actual['head']==H and actual['modules']==2 and actual['failed']==0 and actual['static_exit']==0 and actual['complete_input_objects']==895 and actual['complete_output_objects']==896
anchor=j(review/'anchors/MAC8/object-hashes.json');before=j(v/'inputs/passed-Nlad2/input-before.json');after=j(v/'inputs/passed-Nlad2/input-after.json');output=j(v/'inputs/passed-Nlad2/output.json');assert len(anchor)==895 and anchor==before==after and set(output)-set(anchor)=={owner[:-5]+'.olean'} and not(set(anchor)-set(output)) and [k for k in anchor if anchor[k]!=output[k]]==[facade[:-5]+'.olean']
assert {k:row['git_blob'] for k,row in j(v/'inputs/passed-Nlad2/source-before.json').items()}==hm
imports=j(v/'OWNER-IMPORT-CONTEXT.json');assert len(imports['rows'])==115 and imports['changed_facade_not_imported']
objects1=j(v/'inputs/passed-Nlad1/output.json')
for row in imports['rows']:
 for pin in [B,old,H]:assert git(R,'rev-parse',pin+':'+row['path']).decode().strip()==row['Git_blob_BASE_63eb_1096']
 assert anchor[row['object_path']]==objects1[row['object_path']]==output[row['object_path']]==row['MAC8_Nlad1_Nlad2_object_SHA256']
assert objects1[owner[:-5]+'.olean']==output[owner[:-5]+'.olean']=='6b7b2adeb3182d7c610c75d166eebb66a3cad3ae5752e8cf4a6a44a88ae2fc96'
# Actual final comparison rows/input aliases have already been bound in frozen777; recheck complete directed scores and capture populations directly.
comparison=j(review/'screen/PAIR-COMPARISON.json');assert comparison['persistent_pair_count']==2275 and not comparison['new_pairs'] and not comparison['gone_pairs'] and not comparison['changed_score_pairs'] and comparison['all_pair_rows_after_header_byte_exact']
base_lines=(review/'screen/actual-root-run/BASE.txt').read_text().splitlines();head_lines=(review/'screen/actual-root-run/LADNER.txt').read_text().splitlines();assert base_lines[1:]==head_lines[1:] and len(base_lines)-1==2275
assert len((review/'screen-population.txt').read_text().splitlines())==49 and len((review/'screen-population-BASE48.txt').read_text().splitlines())==48
assert j(review/'screen/ACTUAL-RUN-BINDING.json')['all151_post_run_inputs_exact_to_supplied_full_capture_or_alias']
for n in ['bindings/THEOREM-BOUNDARY-REVIEW.json','bindings/RULE10-SCOPE-CLARIFICATION.json','bindings/PRIVATE-EDGE-ARGUMENT-REVIEW.json','bindings/CURRENT-STANDARDS.json','screen/PAIR-COMPARISON.json','screen/DISPOSITIONS.json','screen/CAPTURE-MAPPING-SUMMARY.json','evidence/actual-validation162/SELECTED17-METADATA.json','evidence/actual-validation162/AX-AND-CONTROL-COMPARISON.json','evidence/actual-validation162/CURRENT-SOURCE-BINDING.json','evidence/actual-validation162/OWNER-IMPORT-CONTEXT.json','evidence/actual-validation162/FOREIGN-FOOTPRINT.json','evidence/actual-validation162/ARGUMENT-REVIEW.json','standards/campaign/items/ladner/2026-11-08-source-check.md','standards/campaign/items/ladner/LADNER-design.md']:
 cp(review/n,'evidence/'+n)
# Exact source inputs for mathematical/source-origin review; full values are source text, not rendered theorem proof values.
for path in [owner,facade,'TCSlib/Complexity/TuringMachine/Encoding.lean','TCSlib/Complexity/Diagonalization/EXPCOM.lean','TCSlib/Complexity/ClassNP/SAT.lean','TCSlib/Complexity/Formulas/CNFEncoding.lean']:
 b=get(R,H,path);dest=out/'source'/ (path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
dump('VERIFICATION.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':H,'BASE':B,'records':pub['records'],'exchange':pub['exchange'],'report_SHA256':sha(report.read_bytes()),'bundle_SHA256':sha(bundle),'bundle_bytes':len(bundle),'all885_ordered_sections':section_rows,'all777_frozen_payloads_exact_and_committed':True,'source_paths':{'BASE':1003,'HEAD':1004,'changed':[facade,owner],'owner_genuinely_absent_BASE':True,'owner_sha256':sha(owner_bytes),'formal_code_exact_v2':True,'facade_old_formal_code_restored_by_import_removal':True},'metadata':{'selected_count':17,'standard_only_count':10,'sorryAx_count':7,'sorryAx_roots':sorry,'raw_ABI_reconstruction_exact':True},'guard':{'ordinary_TCSlib_heads':9,'raw_definition_rows':146,'encountered_theorem_boundaries':6,'generated_same_owner_stop_boundaries':2,'controls':18,'private_edges':6,'no_unrestricted_proof_value_closure':True},'replay':actual,'whole_MAC8_lineage_exact_895_to896':True,'all115_internal_source_and_object_context_rows_exact':True,'source63eb_execution_transport_to1096_not_relabelled_as_fresh':True,'actual48_49_screen':{'persistent_pairs':2275,'new':0,'gone':0,'changed_scores':0,'all_pair_lines_byte_exact':True},'new_Lean_or_replay_or_screen_or_proof_execution':False,'scope':'Publication/source/data/coherence checks and conceptual statement assessment only; no mathematical hole filled.'})
print(json.dumps({'sections':885,'payloads':777,'metadata':17,'standard_roots':10,'admitted_targets_plus_packaging':7,'guard_heads':9,'controls':18,'replay':'2/0/6,895→896','actual_pairs':2275,'new':0,'gone':0,'score_changes':0}))
