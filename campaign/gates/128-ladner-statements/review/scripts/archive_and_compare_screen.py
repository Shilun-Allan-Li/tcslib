from pathlib import Path
import json, hashlib, re, datetime
root=Path(__file__).resolve().parents[1]
shared=Path('/private/tmp/ab34-late-context-screen')
def readj(path): return json.loads(path.read_text())
def sha(data): return hashlib.sha256(data).hexdigest()
def dump(path,obj): path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
complete=readj(shared/'COMPLETE.json');request=readj(shared/'REQUEST.json');results=readj(shared/'RESULTS.json')
assert complete['pass'] and complete['populations']==[48,48,49] and [r['side'] for r in results]==['BASE','NAT','LADNER']
assert sha((shared/'REQUEST.json').read_bytes())==sha((root/'screen/REQUEST.json').read_bytes())
assert request['base']=='9b5dcf46408db681bcbc721930ef2203fa6bc47d' and request['Ladner_source']=='1096e50b4e105392737ec52939b1db0cdbd9316d'
archive=root/'screen/actual-root-run';archive.mkdir(parents=True,exist_ok=True)
archive_names=['REQUEST.json','driver.py','RESULTS.json','COMPLETE.json','progress.json','population-common48.txt','population-Ladner49.txt','BASE.txt','NAT.txt','LADNER.txt','NAT-pairdiff.txt','LADNER-pairdiff.txt']
archive_rows=[]
for name in archive_names:
 data=(shared/name).read_bytes();data.decode('utf-8');(archive/name).write_bytes(data)
 archive_rows.append({'original_path':str(shared/name),'capture':'screen/actual-root-run/'+name,'bytes':len(data),'sha256':sha(data)})
for result in results:
 data=(archive/(result['side']+'.txt')).read_bytes()
 assert len(data)==result['bytes'] and sha(data)==result['sha256'] and result['exit']==0 and result['source_unchanged']
# All three shared-driver input trees are present via full selected source captures or exact NAT aliases.
captures=readj(root/'bindings/FULL-SCREEN-SOURCE-CAPTURES.json')['rows'];nat=readj(root/'screen/SHARED-RUN-NAT-INPUTS.json')['rows']
locators={phase:{r['path']:r['capture'] for r in captures if r['phase']==phase} for phase in ['BASE','LADNER']}
locators['NAT']={r['original_path']:r['full_capture_or_exact_alias'] for r in nat}
for phase in ['BASE','LADNER']:
 locators[phase]['scripts/copy-text-screen-v3.py']='reproduction-tools/copy-text-screen-v3.py'
 locators[phase]['devtools/seyoon/pairdiff.py']='reproduction-tools/pairdiff.py'
input_rows=[]
for phase in ['BASE','NAT','LADNER']:
 part=request['exports'][phase]
 assert len(part['files'])=={'BASE':48,'NAT':48,'LADNER':49}[phase]
 for path,digest in part['sha256'].items():
  data=(shared/'exports'/phase/path).read_bytes();capture=locators[phase][path];saved=(root/capture).read_bytes()
  assert sha(data)==digest and data==saved
  input_rows.append({'phase':phase,'path':path,'source_or_package_origin':part['source'] if not path.startswith('Mathlib/') else request['Mathlib_package'],'capture_or_exact_alias':capture,'bytes':len(data),'sha256':digest,'matches_actual_post_run_export':True})
assert len(input_rows)==151
maps={phase:readj(root/'screen'/('mapped-'+phase+'-captures.json')) for phase in ['BASE','LADNER']}
indices={phase:{row['screen_label']:row for row in maps[phase]['full_rows']} for phase in maps}
P=re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%$')
H=re.compile(r'^declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars$')
def parse(phase):
 lines=(archive/(phase+'.txt')).read_text().splitlines();header=H.fullmatch(lines[0]);assert header
 stats={'parser_captures':int(header[1]),'directed_pairs':int(header[2]),'reproduced_text_chars':int(header[3].replace(',',''))}
 assert stats['parser_captures']==len(indices[phase])
 pairs={}
 for line in lines[1:]:
  m=P.fullmatch(line);assert m,line
  target,source,n,d,pct=m.groups();n=int(n);d=int(d);pct=int(pct);key=(target,source)
  assert key not in pairs and target in indices[phase] and source in indices[phase]
  a=indices[phase][target];b=indices[phase][source]
  assert a['parser_kind']==b['parser_kind'] and d==b['normalized_body_chars']
  assert n>=60 and n*2>=d and n<=min(a['normalized_body_chars'],b['normalized_body_chars'])
  assert f'{n/d:.0%}'==str(pct)+'%'
  pairs[key]={'target':target,'source':source,'matched_chars':n,'source_normalized_chars':d,'percent':pct,'raw_line':line.strip()}
 assert len(pairs)==stats['directed_pairs'] and sum(r['matched_chars'] for r in pairs.values())==stats['reproduced_text_chars']
 return stats,pairs,lines
base,bp,bl=parse('BASE');head,hp,hl=parse('LADNER')
new=sorted(set(hp)-set(bp));gone=sorted(set(bp)-set(hp));score=[]
for key in sorted(set(bp)&set(hp)):
 if any(bp[key][k]!=hp[key][k] for k in ['matched_chars','source_normalized_chars','percent']):score.append(key)
assert not new and not gone and not score
assert bl[1:]==hl[1:]
endpoints={name for pair in hp for name in pair}
assert not any(name.startswith('Ladner.lean::') for name in endpoints)
persistent=[]
for target,source in sorted(hp):
 row=dict(hp[(target,source)]);row['BASE_score_exact']=True
 row['target_index']={'file':'screen/mapped-LADNER-captures.json','screen_label':target}
 row['source_index']={'file':'screen/mapped-LADNER-captures.json','screen_label':source}
 persistent.append(row)
dump(root/'screen/PAIR-COMPARISON.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'Independent linear parsing and exact directed-identity/score/endpoint checks of actual root output. No lcs, tiling, pair scoring, screen or Lean execution.','BASE_source':request['base'],'HEAD_source':request['Ladner_source'],'BASE_population':48,'HEAD_population':49,'BASE':base,'HEAD':head,'new_pairs':[],'gone_pairs':[],'changed_score_pairs':[],'persistent_pair_count':len(persistent),'all_pair_rows_after_header_byte_exact':True,'all_endpoint_labels_and_denominators_match_full_source_capture_indices':True,'all_like_kind_and_thresholds_checked':True,'unique_persistent_endpoint_capture_labels':len(endpoints),'all_persistent_pairs_uncapped':persistent})
dump(root/'screen/DISPOSITIONS.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Actual source1096 BASE48 versus LADNER49. Current measured change inventories only; no global debt clearance.','new_pairs':{'count':0,'full_rows':[],'disposition':'None to disposition; no new textual pair at the declared tool threshold.'},'gone_pairs':{'count':0,'full_rows':[],'disposition':'None; no existing family is retired or old proof exempted.'},'changed_score_pairs':{'count':0,'full_rows':[],'disposition':'All2275 directed identities retain numerator, denominator and rounded score.'},'new_parser_captures':readj(root/'screen/CAPTURE-MAPPING-SUMMARY.json')['new_screened_parser_captures'],'new_capture_pair_participation':'All five added Ladner parser captures are absent from both endpoints of every actual reported pair. This is only the stated>=60 chars/half-source threshold, not semantic absence.','existing_context':'All2275 persistent pair rows and complete endpoint source spans are retained. Previously acknowledged families and their scopes/windows remain under the current duplication ledger; no blanket new debt waiver, threshold exception, discharge or global absence claim.','no_new_source_or_design_decision':True,'actual_raw_inputs':['screen/actual-root-run/BASE.txt','screen/actual-root-run/LADNER.txt','screen/actual-root-run/LADNER-pairdiff.txt'],'complete_linear_comparison':'screen/PAIR-COMPARISON.json'})
dump(root/'screen/ACTUAL-RUN-BINDING.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual_root_complete':complete,'archive':archive_rows,'all_actual_source_and_tool_input_rows':input_rows,'all151_post_run_inputs_exact_to_supplied_full_capture_or_alias':True,'selected_gate128_phases':['BASE','LADNER'],'shared_unrelied_on_phase':'NAT','actual_head_population_file':'screen-population.txt','actual_base_population_file':'screen-population-BASE48.txt','head_Ladner_absent_at_BASE_never_faked_empty':True,'Mathlib_origin':request['Mathlib_package'],'LADNER_result':next(r for r in results if r['side']=='LADNER'),'audited_source':request['Ladner_source'],'independent_comparison_only_no_new_Lean_or_screen':True})
print(json.dumps({'BASE':base,'HEAD':head,'new':len(new),'gone':len(gone),'score_changed':len(score),'persistent':len(persistent),'endpoint_labels':len(endpoints),'input_rows_verified':len(input_rows),'LADNER_SHA256':next(r for r in results if r['side']=='LADNER')['sha256']}))
