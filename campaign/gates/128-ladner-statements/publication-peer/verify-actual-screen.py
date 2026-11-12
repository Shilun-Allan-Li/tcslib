from pathlib import Path
import json,hashlib,re,subprocess,os
P=Path('/private/tmp/ab34-gate128-ready-draft');O=Path('/private/tmp/ab34-gate128-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');J=lambda p:json.loads(p.read_text());h=lambda b:hashlib.sha256(b).hexdigest();env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0';binding=J(P/'screen/ACTUAL-RUN-BINDING.json');req=J(P/'screen/REQUEST.json');archive=[]
for r in binding['archive']:
 b=(P/r['capture']).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];archive.append(dict(r,exact=True))
complete=J(P/'screen/actual-root-run/COMPLETE.json');assert complete['pass'];results={r['side']:r for r in complete['results']};actualinputs=[]
for r in binding['all_actual_source_and_tool_input_rows']:
 q=P/r['capture_or_exact_alias'];b=q.read_bytes();e=req['exports'][r['phase']];assert len(b)==r['bytes'] and h(b)==r['sha256']==e['sha256'][r['path']];blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest();gitroot=R/'.lake/packages/mathlib' if r['path'].startswith('Mathlib/') else R;pin=req['Mathlib_package'] if r['path'].startswith('Mathlib/') else e['source'];actual=subprocess.check_output(['git','-C',str(gitroot),'rev-parse',pin+':'+r['path']],env=env).decode().strip();assert actual==blob;actualinputs.append(dict(r,actual_Git_blob=blob,exact=True))
assert len(actualinputs)==151;raws={p:(P/'screen/actual-root-run'/(p+'.txt')).read_bytes() for p in ['BASE','NAT','LADNER']}
for side,b in raws.items():
 r=results[side];assert r['exit']==0 and r['source_unchanged'] and r['bytes']==len(b) and r['sha256']==h(b) and r['source']==req['exports'][side]['source']
assert results['BASE']['population']==48 and results['LADNER']['population']==49 and raws['BASE'].split(b'\n',1)[1]==raws['LADNER'].split(b'\n',1)[1]
pattern=re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%',re.M);parsed={};indices={};summ=[]
for side,label,count in [('BASE','BASE',2675),('LADNER','LADNER',2680)]:
 mapped=J(P/'screen'/('mapped-'+label+'-captures.json'));inds={r['screen_label']:r for r in mapped['full_rows'] if r['meets_60_character_capture_threshold']};assert len(inds)==count;indices[side]=inds
 for r in mapped['full_rows']:
  src=(P/r['source_capture']).read_bytes();assert h(src)==r['source_sha256'];text=src.decode();a=r['source_start_character'];b=r['source_end_character_exclusive'];assert 0<=a<=b<=len(text) and text.count('\n',0,a)+1==r['source_start_line']
 rows=pattern.findall(raws[side].decode());assert len(rows)==2275;d={}
 for target,source,n,c,pct in rows:
  assert target in inds and source in inds and int(c)==inds[source]['normalized_body_chars'] and inds[target]['parser_kind']==inds[source]['parser_kind'];assert int(n)>=60 and 2*int(n)>=int(c);d[(target,source)]=(int(n),int(c),int(pct))
 assert len(d)==2275;parsed[side]=d;summ.append({'phase':side,'filtered_captures':count,'pairs':len(d),'sum_recorded_matched_chars':sum(v[0] for v in d.values()),'all_existing_labels_kind_denominators_bound':True})
assert parsed['BASE']==parsed['LADNER'];old=indices['BASE'];new=indices['LADNER'];assert set(old)<=set(new)
for label,r in old.items():assert r['parser_kind']==new[label]['parser_kind'] and r['normalized_body_chars']==new[label]['normalized_body_chars'] and r['normalized_body_sha256']==new[label]['normalized_body_sha256']
extra=sorted(set(new)-set(old));assert len(extra)==5 and all(s.startswith('Ladner.lean::') for s in extra);assert not any(t in extra or s in extra for t,s in parsed['LADNER'])
comparison=J(P/'screen/PAIR-COMPARISON.json');assert comparison['new_pairs']==comparison['gone_pairs']==comparison['changed_score_pairs']==[] and comparison['persistent_pair_count']==2275;rows=comparison['all_persistent_pairs_uncapped'];assert len(rows)==2275
for r in rows:assert parsed['BASE'][(r['target'],r['source'])]==(r['matched_chars'],r['source_normalized_chars'],r['percent']) and r['BASE_score_exact']
disp=J(P/'screen/DISPOSITIONS.json');assert disp['new_pairs']['count']==disp['gone_pairs']['count']==disp['changed_score_pairs']['count']==0;assert all(disp[k]['full_rows']==[] for k in ['new_pairs','gone_pairs','changed_score_pairs']);clarify=J(P/'bindings/THEOREM-BOUNDARY-REVIEW.json');own=J(O/'auxiliary-theorem-boundary-inspection.json');assert clarify['all6_theorem_boundary_rows_verbatim']==own['encountered_theorem_boundaries']
receipt={'actual_archived_complete_PASS':True,'LADNER_head':'1096e50b4e105392737ec52939b1db0cdbd9316d','BASE48_HEAD49_population_exact':True,'all151_source_tool_aliases_actual_Git_SHA_bytes_exact':True,'all97_gate_source_captures_complete':True,'all_pair_bytes_after_first_header_identical':True,'new':0,'gone':0,'persistent_score_changes':0,'persistent_unchanged_pairs':2275,'all2275_uncapped_disposition_vectors_exact':True,'new_filtered_parser_labels_5_no_pair_participation':extra,'extraction_counts_not17_authored_declarations_or_debt_count':True,'same_owner_generated_theorem_boundary_clarification_matches_raw':True,'new_Lean_screens_or_pair_scoring_by_peer':False,'results':[results['BASE'],results['LADNER']],'format_counts':summ,'raw_archives':archive,'all151_inputs':actualinputs}
(O/'actual-screen-and-dispositions-checks.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'actual_result':'PASS BASE48/LADNER49','counts':summ,'pairs_changed':[0,0,0],'source_tool_inputs_Git_bound':151,'new_filter_captures':len(extra),'no_new_scoring':True}))
