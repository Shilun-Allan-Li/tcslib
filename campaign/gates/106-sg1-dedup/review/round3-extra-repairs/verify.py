from pathlib import Path
import json,hashlib,re
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
c=json.loads((OUT/'context.json').read_text());changes=json.loads((OUT/'changes-proposed.json').read_text());before=(OUT/'Hardness-before.lean.txt').read_text();after=(OUT/'Hardness-after.lean.txt').read_text();restored=after
for r in changes:
 new=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];old=r['old_doc']+'\n'+r['header']+'\n'+r['old_body'];assert restored.count(new)==1;restored=restored.replace(new,old)
assert restored==before
assert hashlib.sha256(Path(c['worktree'],c['owned_file']).read_bytes()).hexdigest()==c['after_sha256']
prior=ROOT/'campaign/gates/106-sg1-dedup/review/round3-closure-repairs';pm=json.loads((prior/'MANIFEST.json').read_text())
for row in pm['files']:
 f=prior/row['path'];assert f.stat().st_size==row['bytes'] and hashlib.sha256(f.read_bytes()).hexdigest()==row['sha256']
sealed=(OUT/'Hardness-sealed-v1.lean.txt').read_text();native=(OUT/'Hardness-native-v1.lean.txt').read_text();clean=sealed
for r in json.loads((OUT/'changes-v1.json').read_text()):
 token=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];wrapped='section SG1ExtraSeal_'+r['name']+'\n'+(OUT/'guard-attributes.txt').read_text()+token+'end SG1ExtraSeal_'+r['name']+'\n';assert clean.count(wrapped)==1;clean=clean.replace(wrapped,token)
assert clean==native
meta={};runs=[];guards=set((OUT/'guard-definitions.txt').read_text().splitlines());assert len(guards)==20
for name in ['Small-native-v1','Small-sealed-v1','Small-native-v2','Small-sealed-v2','Hardness-native-v1','Hardness-sealed-v1']:
 receipt=json.loads((OUT/(name+'-run.json')).read_text());raw=(OUT/(name+'.out')).read_text();src=(OUT/(name+'.lean.txt')).read_text()
 assert receipt['exit']==receipt['errors']==0,name
 assert hashlib.sha256(src.encode()).hexdigest()==receipt['input_sha256'] and hashlib.sha256(raw.encode()).hexdigest()==receipt['output_sha256']
 roots=re.findall(r'^ROOT\|([^|]+)\|private=(\w+)',raw,re.M);assert len(roots)==2 and all(b=='true' for _,b in roots)
 axs=[{'name':n,'kind':k,'axioms':[x.strip() for x in a.split(',') if x.strip()]} for n,k,a in re.findall(r'^PROOFAX\|([^|]+)\|kind=([^|]+)\|\[([^\]]*)\]',raw,re.M)];assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in axs)
 fs=[dict(zip(['root','name','owner','hints'],row)) for row in re.findall(r'^FOREIGNDEF\|([^|]+)\|([^|]+)\|([^|]+)\|hints=(\w+)$',raw,re.M)];assert {r['name'] for r in fs if r['hints']=='regular'}<=guards
 cited=[dict(zip(['root','name','owner','kind','private'],row)) for row in re.findall(r'^CITED\|([^|]+)\|([^|]+)\|([^|]+)\|kind=([^|]+)\|private=(\w+)$',raw,re.M)];assert not any(r['private']=='true' for r in cited)
 ranges=[]
 version_changes=json.loads((OUT/'changes-v1.json').read_text()) if name.endswith('v1') else changes
 for r in version_changes:
  token=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];pos=src.index(token);a=src[:pos].count('\n')+1;ranges.append((a,a+token.count('\n')))
 warnings=[{'line':int(a),'column':int(b),'message':t} for a,b,t in re.findall(r'^.*?:(\d+):(\d+): warning: (.*)$',raw,re.M)];changed=[r for r in warnings if any(a<=r['line']<=b for a,b in ranges)];assert (len(changed)==2 and all('simp argument is unused' in x['message'] for x in changed)) if name.endswith('v1') else not changed
 meta[name]={'roots':roots,'AX_roots_descendants':axs,'foreign_definitions':fs,'CITED':cited,'warnings':warnings,'warnings_in_changed_sections':changed}
 runs.append({'name':name,**{k:receipt[k] for k in ['exit','errors','seconds','input_sha256','output_sha256']},'warnings':len(warnings)})
assert {(r['name'],r['kind'],tuple(r['axioms'])) for r in meta['Hardness-native-v1']['AX_roots_descendants']}=={(r['name'],r['kind'],tuple(r['axioms'])) for r in meta['Hardness-sealed-v1']['AX_roots_descendants']}
controls=json.loads((OUT/'control-check.json').read_text());assert controls['definitions']==20 and controls['pointwise_and_abstracted_pairs']==40 and controls['all_exact_multiplicities_match']
for r in changes:
 assert not re.search(r'\b(sorry|admit|unsafe|unfold)\b',r['new_body'])
# Same-home definitions are intentionally available only as unchanged owner-local slices.
assert 'private def clHeaderTail' in (OUT/'owner-local-context.lean.txt').read_text()
summary={'status':'Final warning-only cleanup prechecked native/sealed; full v1 native/seal PASS; final full-source combined15 rerun reserved for parent','authorized_source_file':c['owned_file'],'proofs_changed':2,'adjacent_docs_changed':2,'old_source_restored_by_exact_reverse_changes':True,'all_old_headers_imports_attrs_order_defs_tables_and_other_bodies_frozen':True,'actual_after_sha256':c['after_sha256'],'actual_source_stable':True,'prior13_review_payloads_unchanged':True,'guard_count':20,'fresh_paired_controls':40,'root_count':2,'compiled_descendants':len(meta['Hardness-sealed-v1']['AX_roots_descendants'])-2,'all_selected_standard_AX':True,'foreign_regular_defs':sorted({r['name'] for r in meta['Hardness-sealed-v1']['foreign_definitions'] if r['hints']=='regular'}),'abbrev_projections':sorted({r['name'] for r in meta['Hardness-sealed-v1']['foreign_definitions'] if r['hints']=='abbrev'}),'no_imported_private_CITED':True,'source_raw_sorry_before_after':[len(re.findall(r'\bsorry\b',before)),len(re.findall(r'\bsorry\b',after))],'guard_removal_exact_native_identity':True,'samehome_change_step':'clA5Pair_sizes change reduces only unchanged private clHeaderField/clHeaderTail owner definitions; decoder and all foreign ordinary definitions remain opaque','final_small_v2_no_warnings':True,'full_v1_new_unused_simp_warnings':2,'final_full_source_native_seal_NOT_RUN_after_only_two_unused_arguments_removed':True,'runs':runs,'no_source_other_than_Hardness_no_Git_commit_push_no_cache_snapshot_compiledoutput_screen':True,'combined15_metadata_replay':'Parent work, NOT RUN here'}
(OUT/'compiled-metadata.json').write_text(json.dumps(meta,indent=2)+'\n');(OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['actual_after_sha256','root_count','compiled_descendants','guard_count','fresh_paired_controls','foreign_regular_defs','final_small_v2_no_warnings']},indent=2))
