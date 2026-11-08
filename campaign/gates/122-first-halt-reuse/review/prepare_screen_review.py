from pathlib import Path
import json,re,hashlib,shutil,subprocess,collections
O=Path(__file__).parent;D=Path('/private/tmp/ab34-fh13-screen44');scope=json.loads((O/'scope.json').read_text());complete=D/'COMPLETE.json'
if not complete.exists():print('Awaiting actual root HEAD screen completion; no result copied or finalized.');raise SystemExit(0)
request=json.loads((D/'EXECUTION-REQUEST.json').read_text());result=json.loads(complete.read_text());runs=json.loads((D/'RESULTS.json').read_text());assert result['pass'] and result['head']==scope['HEAD'] and result['population']==44 and len(runs)==2 and [r['side'] for r in runs]==['BASE','HEAD'];Q=O/'screen';Q.mkdir(exist_ok=True)
for n in ['EXECUTION-REQUEST.json','REQUEST.json','RESULTS.json','COMPLETE.json','progress.json','driver.py','screen-population.txt','BASE.txt','HEAD.txt','pairdiff.txt']:shutil.copyfile(D/n,Q/n)
helper=[]
for side in ['BASE','HEAD']:
 for path in ['scripts/copy-text-screen-v3.py','devtools/seyoon/pairdiff.py']:
  raw=(D/'exports'/side/path).read_bytes();assert hashlib.sha256(raw).hexdigest()==request['exports'][side]['sha256'][path];p=Q/'helpers'/side/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw);helper.append({'side':side,'path':path,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
 for path in request['population']:assert hashlib.sha256((O/'source'/side/(path+'.txt')).read_bytes()).hexdigest()==request['exports'][side]['sha256'][path]
(Q/'HELPER-SOURCE-HASHES.json').write_text(json.dumps(helper,indent=2)+'\n');P=re.compile(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%');parsed={};summary={};lookup={}
for side in ['BASE','HEAD']:
 run=next(r for r in runs if r['side']==side);raw=(Q/(side+'.txt')).read_bytes();assert run['exit']==0 and run['source_unchanged'] and len(raw)==run['bytes'] and hashlib.sha256(raw).hexdigest()==run['sha256'];text=raw.decode();m=re.match(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',text);assert m
 rows=[]
 for line in text.splitlines()[1:]:
  if not line.strip():continue
  n=P.fullmatch(line);assert n,line;rows.append({'target':n.group(1),'source':n.group(2),'matched_chars':int(n.group(3)),'source_chars':int(n.group(4)),'percent':int(n.group(5))})
 assert len(rows)==int(m.group(2)) and len({(r['target'],r['source']) for r in rows})==len(rows);parsed[side]={(r['target'],r['source']):r for r in rows};summary[side]={'filtered_bodies':int(m.group(1)),'directed_pairs':len(rows),'reproduced_chars':int(m.group(3).replace(',','')),'exit':run['exit'],'sha256':run['sha256'],'seconds':run['seconds']};records=json.loads((O/'preparation'/(side+'-screen-label-source-index.json')).read_text());assert len(records)==summary[side]['filtered_bodies'];lookup[side]={r['label']:r for r in records};assert all(r['target'] in lookup[side] and r['source'] in lookup[side] for r in rows)
B=parsed['BASE'];H=parsed['HEAD'];new=[H[k] for k in H if k not in B];gone=[B[k] for k in B if k not in H];changed=[{'BASE':B[k],'HEAD':H[k]} for k in H if k in B and B[k]!=H[k]];canonical={s:{tuple(r['canonical_source_identity']):r for r in lookup[s].values()} for s in ['BASE','HEAD']};roots=json.loads((O/'HEADER-FREEZE13.json').read_text());rootbykey={}
for side in ['BASE','HEAD']:
 for r in lookup[side].values():
  hits=[x for x in roots if x['path']==r['path'] and (r['qualified_name']==x['name'] or r['qualified_name'].endswith('.'+x['name']))]
  assert len(hits)<=1
  if hits:rootbykey[tuple(r['canonical_source_identity'])]=hits[0]
changes=[]
for key in sorted(set(canonical['BASE'])|set(canonical['HEAD'])):
 a=canonical['BASE'].get(key);b=canonical['HEAD'].get(key)
 if a and b and a['normalized_body']==b['normalized_body']:continue
 assert key in rootbykey,(key,'unexpected changed extracted body');changes.append({'source_identity':key,'root_id':rootbykey[key]['id'],'name':rootbykey[key]['name'],'BASE':a,'HEAD':b,'filtered_out_at_HEAD':b is None,'declaration_still_exists_in_source':True})
assert {r['root_id'] for r in changes}==set(scope['kept_ids']);(Q/'changed-reader-source-bodies13.json').write_text(json.dumps(changes,indent=2)+'\n')
# Materialize every source span needed for all changed pair identities; full population sources remain supplied.
affected={('HEAD',r[f]) for r in new for f in ['target','source']}|{('BASE',r[f]) for r in gone for f in ['target','source']}|{(s,r[s][f]) for r in changed for s in ['BASE','HEAD'] for f in ['target','source']};chunks=[]
for i,(side,label) in enumerate(sorted(affected),1):
 r=lookup[side][label];raw=(O/'source'/side/(r['path']+'.txt')).read_text();chunk=raw[r['raw_decl_start']:r['raw_v3_span_end']];p=Q/'changed-pair-source-spans'/side/(str(i).zfill(4)+'.lean.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(chunk);chunks.append({'side':side,'label':label,'source':r['path'],'source_start_line':r['source_start_line'],'raw_char_start':r['raw_decl_start'],'raw_v3_span_end':r['raw_v3_span_end'],'qualified_name':r['qualified_name'],'canonical_source_identity':r['canonical_source_identity'],'kind':r['kind'],'normalized_body_sha256':r['normalized_body_sha256'],'evidence':str(p.relative_to(O)),'scope':'Exact raw span underlying v3 extraction, may include following doc/scope text; full source and separately frozen complete thirteen target scopes supplied.'})
(Q/'changed-pair-source-spans-index.json').write_text(json.dumps(chunks,indent=2)+'\n');delta={'HEAD':scope['HEAD'],'BASE':scope['BASE'],'source_population':44,'summary':summary,'new':new,'BASE_only':gone,'persistent_score_changed':changed,'persistent_exact_count':sum(k in B and B[k]==H[k] for k in H),'directed_identity':'target,source; all row scores/raw stdout retained','changed_pair_source_spans':len(chunks),'not_unique_copy_counts':True};(Q/'pair-delta.json').write_text(json.dumps(delta,indent=2)+'\n')
changedkeys={tuple(r['source_identity']) for r in changes};reviews=[]
for status,rows in [('NEW',new),('BASE_ONLY',gone),('PERSISTENT_SCORE_CHANGED',changed)]:
 for row in rows:
  side='BASE' if status=='BASE_ONLY' else 'HEAD';actual=row['HEAD'] if status=='PERSISTENT_SCORE_CHANGED' else row;target=lookup[side][actual['target']];source=lookup[side][actual['source']];ids=sorted({rootbykey[tuple(r['canonical_source_identity'])]['id'] for r in [target,source] if tuple(r['canonical_source_identity']) in changedkeys},key=str);assert ids,(status,actual,'delta without changed-reader source');reviews.append({'status':status,'pair':row,'changed_reader_ids':ids,'target_source_identity':target['canonical_source_identity'],'source_source_identity':source['canonical_source_identity'],'review_status':'PENDING final explicit source inspection','no_global_absence_or_debt_retirement_inferred':True})
(Q/'PAIR-REVIEW-PENDING.json').write_text(json.dumps(reviews,indent=2)+'\n');print(json.dumps({'summary':summary,'new':len(new),'BASE_only':len(gone),'persistent_score_changed':len(changed),'changed_body_roots':[(r['root_id'],r['filtered_out_at_HEAD']) for r in changes],'source_spans':len(chunks),'finalized':False},indent=2));print('NEW PAIRS');print(json.dumps(new,indent=2))
