import hashlib,json,re,subprocess
from pathlib import Path
B=Path('/private/tmp/ab34-gates123125-peer-v2');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');PUB=json.loads((B/'inputs/publications.json').read_text());BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d'
def git(*args):return subprocess.run(['git','-C',str(R),*args],capture_output=True,check=True).stdout
def sha(x):return hashlib.sha256(x).hexdigest()
def jsonfile(p):return json.loads(p.read_text())
def tree(rev):
 t={}
 for row in git('ls-tree','-r','-z',rev).split(b'\0'):
  if not row:continue
  m,p=row.split(b'\t',1);p=p.decode()
  if p.endswith('.lean'):t[p]=m.decode().split()[2]
 return t
def contents(rev,t):
 names=sorted(t);raw=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=''.join(rev+':'+p+'\n' for p in names).encode(),capture_output=True,check=True).stdout;off=0;out={}
 for p in names:
  e=raw.index(b'\n',off);h,typ,n=raw[off:e].split();assert h.decode()==t[p] and typ==b'blob';n=int(n);off=e+1;out[p]=raw[off:off+n];off+=n;assert raw[off:off+1]==b'\n';off+=1
 assert off==len(raw);return out
for p in PUB:
 gate=p['gate'];D=B/str(gate);prefix=f'campaign/gates/{gate}-{p["slug"]}';Q=D/'sections'/prefix/'review';T=D/'sections'/prefix/'reproduction-tools';A=D/'sections/campaign/status/2026-11-08-mig1-merge';anchor=jsonfile(A/'object-hashes.json');ib=jsonfile(Q/'replay/input-before.json');ia=jsonfile(Q/'replay/input-after.json');ob=jsonfile(Q/'replay/output.json');assert ib==ia==anchor and len(ib)==len(ob)==895 and ib.keys()==ob.keys();assert jsonfile(A/'Lean-tree.json')==tree(BASE)
 if gate==123:
  old=Path('/private/tmp/ab34-gate123-publication-peer/records-inputs/campaign/gates/123-ch7-run/review');assert (Q/'MANIFEST.json').read_bytes()==(old/'MANIFEST.json').read_bytes()
  for row in jsonfile(Q/'MANIFEST.json')['files']:assert (Q/row['path']).read_bytes()==(old/row['path']).read_bytes()
  report={'gate':123,'full315_frozen_review_unchanged_from_independently_checked_V1':True,'source_and_all_source_log_ABI_boundary_screen_claims_transfer_by_exact315_byte_identity':True,'new_bundled_MAC8_anchor895_matches_replay_input_before_after':True,'new_bundled_source_anchor1003_matches_BASE_Git_blobs':True,'old_major_input_gap_resolved':True,'old_frozen_report_not_mutated':True}
 else:
  H=p['source'];htree=tree(H);btree=tree(BASE);head=contents(H,htree);base=contents(BASE,btree);actual=jsonfile(Q/'replay/source-before.json');expected={n:{'git_blob':htree[n],'sha256':sha(v),'bytes':len(v)} for n,v in head.items()};assert len(actual)==len(expected)==1003 and actual==expected
  changed=[n for n in head if head[n]!=base[n]];OWNER='TCSlib/Complexity/CookLevin/Hardness.lean';assert changed==[OWNER] and not git('diff','--name-only',BASE,p['records'],'--','*.lean')
  focus=Q/'inputs/word-full-two-scopes';chunks=jsonfile(focus/'selected-two-chunk-mappings.json');bt=base[OWNER].decode();ht=head[OWNER].decode();restored=ht
  for row in chunks:
   assert bt.count(row['old_chunk'])==ht.count(row['new_chunk'])==1
   assert sha(row['old_chunk'].encode())==row['old_chunk_sha256'] and sha(row['new_chunk'].encode())==row['new_chunk_sha256']
   old_decl=row['old_chunk'][row['old_chunk'].index('private lemma '):];new_decl=row['new_chunk'][row['new_chunk'].index('private lemma '):];assert old_decl.split(':=',1)[0]==new_decl.split(':=',1)[0]
   restored=restored.replace(row['new_chunk'],row['old_chunk'])
  assert restored==bt and len(chunks)==2
  assert [x for x in bt.splitlines() if x.startswith('import ') or x.startswith('attribute ') or x.startswith('@[')]==[x for x in ht.splitlines() if x.startswith('import ') or x.startswith('attribute ') or x.startswith('@[')]
  for api in (focus/'API-source').rglob('*.lean.txt'):
   path=api.relative_to(focus/'API-source').as_posix()[:-4];assert api.read_bytes()==head[path]==base[path]
  index=jsonfile(Q/'replay/compiled-source-index.json');down=(Q/'replay/down.txt').read_text().splitlines();rows=jsonfile(Q/'replay/module-results.json');assert len(index)==len(down)==len(rows)==26
  for row in index:
   assert (Q/row['capture']).read_bytes()==head[row['path']] and sha(head[row['path']])==row['sha256'] and htree[row['path']]==row['git_blob']
  assert [r['module'] for r in rows]==down and {r['path'][:-5] for r in index}==set(down)
  for row in rows:assert row['exit']==row['errors']==row['sorry']==0 and row['pass'] and row['fresh_output'] and sha((Q/'replay/logs'/(row['module']+'.log')).read_bytes())==row['log_sha256']
  assert (Q/'replay/static.txt').read_text()=='modules 26, mismatches 0, static total 0\n'
  assert [n for n in ob if ob[n]!=ib[n]]==[OWNER[:-5]+'.olean']
  # Prove exact recorded prospective tree has the pushed source's entire Lean map.
  req=jsonfile(Q/'replay/request.json');assert req['head']==H and req['prospective_Lean_equals_pushed_head'] and tree(req['prospective_tree'])==htree
  # Full selected metadata, read from raw logs and verified against exact two-run JSON.
  meta={}
  for side in ['BASE','HEAD']:
   raw=(Q/'metadata'/f'{side}.log').read_bytes();run=jsonfile(Q/'metadata'/f'{side}-run.json');request=jsonfile(Q/'metadata'/f'{side}-request.json');capture=jsonfile(Q/'metadata'/f'{side}-selected.json');roots=[json.loads(l.split('ABI|',1)[1]) for l in raw.decode().splitlines() if 'ABI|' in l];assert roots==capture['roots'] and len(roots)==2 and capture['private_type_auxiliaries']==[] and raw.decode().count('COMPLETE|2')==1
   assert sha(raw)==run['raw_sha256'] and len(raw)==run['raw_bytes'] and run['exit']==run['errors']==run['warnings']==0 and run['roots_observed']==2 and run['probe_source_sha256']==request['source_probe_sha256']==sha((Q/'selected-metadata-probe.lean.txt').read_bytes())
   assert request['complete_snapshot_owner_object_before_sha256']==(ib if side=='BASE' else ob)[OWNER[:-5]+'.olean'];assert all(r['private'] and r['kind']=='theorem' and r['axioms']==['propext','Classical.choice','Quot.sound'] and not r['simp_lemma'] and not r['simp_unfold'] for r in roots);meta[side]=roots
  assert meta['BASE']==meta['HEAD']
  # Actual scope and control files are the receipt-bound native-project instrumented inputs.
  invlog=(focus/'inventory-HardnessLeaves-attempt1.log').read_text();guards=json.loads(re.search(r'^GUARDS\|(.+)$',invlog,re.M)[1]);simps=json.loads(re.search(r'^SIMPDEFS\|(.+)$',invlog,re.M)[1]);assert len(guards)==15 and simps==['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg']
  native=(focus/'native-project/HardnessLeavesScopeNative.lean.txt').read_text();sealed=(focus/'native-project/HardnessLeavesScopeSealed.lean.txt').read_text()
  for row in chunks:assert native.count(row['new_chunk'])==sealed.count(row['new_chunk'])==1
  for text in [native,sealed]:assert re.search(r'^attribute \[-simp\] (.+)$',text,re.M)[1].split()==simps
  assert re.search(r'^attribute \[local irreducible\] (.+)$',sealed,re.M)[1].split()==guards
  assert sealed.replace('attribute [local irreducible] '+' '.join(guards)+'\n','')==native
  runs=[('scope-native','HardnessLeavesScopeNative.lean.txt',0,0),('scope-sealed','HardnessLeavesScopeSealed.lean.txt',0,0),('controls-native','HardnessLeavesControlsNative.lean.txt',0,0),('controls-sealed','HardnessLeavesControlsSealed.lean.txt',1,30)]
  for label,fn,exitcode,errors in runs:
   run=jsonfile(focus/f'HardnessLeaves-{label}-attempt1.json');raw=(focus/f'HardnessLeaves-{label}-attempt1.log').read_bytes();assert sha(raw)==run['sha256'] and len(raw)==run['bytes'] and run['exit']==exitcode and run['errors']==errors and run['sorry_warnings']==0 and sha((focus/'native-project'/fn).read_bytes())==run['probe_sha256']
  nl=(focus/'HardnessLeaves-controls-native-attempt1.log').read_text();sl=(focus/'HardnessLeaves-controls-sealed-attempt1.log').read_text();positives=re.findall(r'^CONTROL\|([^|]+)\|(point|abstract)\|PASS\|kernelChecked=([^\n]+)$',nl,re.M);negatives=re.findall(r'^CONTROL\|([^|]+)\|(point|abstract)\|FAIL$',sl,re.M);expected=[(n,mode) for n in guards for mode in ['point','abstract']];assert [(n,m) for n,m,_ in positives]==negatives==expected and len(set(n for _,_,n in positives))==30 and sl.count('error:')==30
  report={'gate':125,'all1003_source_map_entries_exact_pushed_HEAD':True,'full_prospective_tree_Lean_map_exact_HEAD':True,'only_changed_file':OWNER,'exact2_private_chunks_and_docstrings_restore_BASE_all_other_bytes':True,'private_literal_headers_imports_attributes_runtime_public_source_exact':True,'all7_API_source_captures_exact_BASE_HEAD':True,'all26_compiled_sources_module_logs_result_rows_exact':True,'static_source_log_admissions_total':0,'input895_exact_bundled_MAC8_anchor_before_after':True,'output895_same_keys_only_owner_changed':True,'raw_full_selected2_type_universe_metadata_AX_simp_exact':True,'no_private_type_auxiliaries_in_selected_types':True,'full2_actual_instrumented_scope_chunks_exact_HEAD':True,'15ordinary_guards_3default_simp_removals_exact':True,'effective30kernel_positive_negative_control_pairs_exact':True,'scope_limit':'Exact two selected declarations; historical whole-owner extras not substituted for PR-head replay; no global ABI/simp/AX equality'}
 (D/'SOURCE-LOG-ANCHOR-CHECK.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
