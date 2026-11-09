from pathlib import Path
import json,re,hashlib,collections,subprocess,os
P=Path('/private/tmp/ab34-gate122-fh13-frozen');O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');C=R/'campaign/gates/122-first-halt-reuse'
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
def save(n,a):(O/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
# Parse existing full screen rows only. No pair matching/LCS/scoring is run.
rx=re.compile(r'^\s*(.*?)\s+reproduces\s+(.*?): (\d+)/(\d+) = (\d+)%$')
def parse(side):
 raw=(P/'screen'/(side+'.txt')).read_bytes();lines=raw.decode().splitlines();m=re.fullmatch(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',lines[0]);assert m
 rows=[]
 for line in lines[1:]:
  z=rx.fullmatch(line);assert z,line
  a,b,c,d,e=z.groups();rows.append({'target':a,'source':b,'matched_chars':int(c),'source_chars':int(d),'percent':int(e)})
 assert len(rows)==int(m[2]) and sum(x['matched_chars'] for x in rows)==int(m[3].replace(',',''))
 dd={(x['target'],x['source']):x for x in rows};assert len(dd)==len(rows)
 return dd,{'filtered_bodies':int(m[1]),'directed_pairs':len(rows),'reproduced_chars':sum(x['matched_chars'] for x in rows),'sha256':H(raw),'bytes':len(raw)}
a,sa=parse('BASE');b,sb=parse('HEAD');assert (sa['filtered_bodies'],len(a),sa['reproduced_chars'])==(2662,2583,540404);assert(sb['filtered_bodies'],len(b),sb['reproduced_chars'])==(2660,2564,538136)
new=set(b)-set(a);gone=set(a)-set(b);changed={k for k in a.keys()&b.keys() if a[k]!=b[k]};same={k for k in a.keys()&b.keys() if a[k]==b[k]}
assert len(new)==0 and len(gone)==19 and len(changed)==4 and len(same)==2560
D=J(P/'screen/pair-delta.json');assert D['new']==[]
assert {(r['target'],r['source']) for r in D['BASE_only']}==gone
assert {(r['BASE']['target'],r['BASE']['source']) for r in D['persistent_score_changed']}==changed
for r in J(P/'screen/RESULTS.json'):
 s=sa if r['side']=='BASE' else sb;assert r['sha256']==s['sha256'] and r['bytes']==s['bytes'] and r['exit']==0 and r['source_unchanged']
complete=J(P/'screen/COMPLETE.json');assert complete['pass'] and complete['population']==44
# Comment removal and body extraction bind captured raw source spans, without re-scoring.
def strip(t):
 out=[];i=0;depth=0
 while i<len(t):
  if t.startswith('/-',i):depth+=1;i+=2
  elif depth and t.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif t.startswith('--',i):
   j=t.find('\n',i);i=len(t) if j<0 else j
  else:out.append(t[i]);i+=1
 assert depth==0
 return ''.join(out)
def norm_body(t):
 t=strip(t);d=0
 for i,ch in enumerate(t):
  if ch in '([{⟨':d+=1
  elif ch in ')]}⟩':d-=1
  elif t.startswith(':=',i) and d==0:return re.sub(r'\s+','',t[i+2:])
 raise AssertionError('no top-level := in proof span')
spans=J(P/'screen/changed-pair-source-spans-index.json');assert len(spans)==18
spanchecks=[];spanindex={}
for s in spans:
 src=(P/'source'/s['side']/(s['source']+'.txt')).read_text();sl=src[s['raw_char_start']:s['raw_v3_span_end']];cap=(P/s['evidence']).read_text()
 assert cap==sl and src.count('\n',0,s['raw_char_start'])+1==s['source_start_line']
 norm=norm_body(cap);assert H(norm.encode())==s['normalized_body_sha256']
 spanindex[s['side'],s['label']]=(s,norm)
 spanchecks.append({'side':s['side'],'label':s['label'],'path':s['source'],'start_line':s['source_start_line'],'raw_start':s['raw_char_start'],'raw_end':s['raw_v3_span_end'],'capture_equals_actual_source_slice':True,'slice_bytes':len(sl.encode()),'capture_sha256':H(cap.encode()),'normalized_body_sha256':s['normalized_body_sha256'],'normalized_chars':len(norm)})
review=J(P/'screen/pair-dispositions.json');assert len(review)==23;rowchecks=[]
for n,r in enumerate(review,1):
 assert r['row']==n and r['source_review_complete'] and r['no_new_fix_required'] and r['review_status']=='SOURCE_REVIEW_COMPLETE'
 pp=r['pair']['HEAD'] if r['status']=='PERSISTENT_SCORE_CHANGED' else r['pair'];k=pp['target'],pp['source']
 if r['status']=='BASE_ONLY':assert k in gone and pp==a[k];side='BASE'
 else:assert k in changed and r['pair']['BASE']==a[k] and r['pair']['HEAD']==b[k];side='HEAD'
 for role in ['target','source']:
  ss,body=spanindex[side,pp[role]]
  refs=[x for x in r['raw_span_references'] if x['role']==role];assert len(refs)==1
  x=refs[0];assert x['side']==side and x['raw_screen_span']==ss['evidence'] and x['normalized_body_sha256']==ss['normalized_body_sha256']
  if role=='source':assert len(body)==pp['source_chars']
 for x in r['complete_changed_proof_references']:
  for side2 in ['BASE','HEAD']:assert H((P/x[side2+'_complete_chunk']).read_bytes())==x[side2+'_complete_chunk_sha256']
 rowchecks.append({'row':n,'status':r['status'],'pair':r['pair'],'raw_literal_sources_verified':True,'complete_changed_roots_verified':r['changed_reader_ids'],'peer_disposition':'ACCEPT_SOURCE_EXPLANATION_WITH_RECORDED_LIMITS','source_reason':r['source_reason']})
# Bind all 88 actual screen inputs and four helper captures to request and original Git blobs.
req=J(P/'screen/EXECUTION-REQUEST.json');assert len(req['population'])==44
assert (P/'screen-population.txt').read_text()==(P/'screen/screen-population.txt').read_text()
for side in ['BASE','HEAD']:
 assert set(req['exports'][side]['sha256'])==set(req['population'])|{'scripts/copy-text-screen-v3.py','devtools/seyoon/pairdiff.py'}
 for path,h in req['exports'][side]['sha256'].items():
  cap=P/'source'/side/(path+'.txt') if path in req['population'] else P/'screen/helpers'/side/path
  assert H(cap.read_bytes())==h
helperchecks=[]
for x in J(P/'screen/HELPER-SOURCE-HASHES.json'):
 cap=P/'screen/helpers'/x['side']/x['path'];raw=cap.read_bytes();assert H(raw)==x['sha256'] and len(raw)==x['bytes']
 pin=req['base'] if x['side']=='BASE' else req['head']
 orig=subprocess.check_output(['git','-C',str(R),'show',pin+':'+x['path']],env=os.environ|{'GIT_OPTIONAL_LOCKS':'0'})
 assert raw==orig;helperchecks.append(x)
# Check lint receipts and only documented position/line-count identity normalization.
Q=P/'inputs/current77/qa';qa=J(Q/'comparison.json');rq=J(Q/'REQUEST.json');assert len(rq['files'])==8
for r in J(Q/'RUNS.json'):
 assert r['actual_execution'];assert len(r['argv'])>=8
 for k in ['stdout','stderr']:
  raw=(Q/r[k]).read_bytes();assert len(raw)==r[k+'_bytes'] and H(raw)==r[k+'_sha256']
 assert r['exit']==(1 if r['kind']=='style' else 0)
for kind,total in [('style',68),('campaign',18)]:
 idrows=J(Q/(kind+'-identity-dispositions.json'));assert len(idrows)==total
 assert sum(x['new_count'] for x in idrows)==sum(x['removed_count'] for x in idrows)==0
 assert sum(not x['raw_rows_equal'] for x in idrows)==(44 if kind=='style' else 14)
 for side in ['BASE','HEAD']:
  records=J(Q/(side+'-'+kind+'-findings.json'));assert records['count_files']==8 and records['explicit_files']==rq['files']
  if kind=='campaign':assert records['default_CHECK8B'] is False
  actual=collections.Counter((x['path'],x.get('level','FINDING'),x['message']) for x in records['findings'])
  represented=collections.Counter((x['path'],x.get('level','FINDING'),x['message']) for group in idrows for x in group[side]);assert actual==represented
 for row in idrows:
  for side in ['BASE','HEAD']:
   for x in row[side]:
    msg=x['message'];path=x['path']
    if kind=='style':msg=re.sub('^'+re.escape(path)+r':(?:\d+:)?\s*','',msg)
    msg=re.sub(r'\b\d+ lines\b','<N> lines',msg)
    assert msg==row['identity']['message_with_only_source_positions_and_dynamic_line_counts_normalized']
for s in J(Q/'size-dispositions.json'):
 for side in ['BASE','HEAD']:
  raw=(P/'source'/side/(s['path']+'.txt')).read_bytes();m=s[side];assert len(raw)==m['bytes'] and H(raw)==m['sha256'] and len(raw.decode().splitlines())==m['lines_splitlines']
 assert not s['crossed1000'] and not s['crossed600']
# Read-only root adoption check. This does not assert Git staging/commit or final publication.
pm=J(C/'PATH-MAP.json');assert pm['source_manifest_sha256']==H((P/'MANIFEST.json').read_bytes())
paths=pm['paths'];files=J(P/'MANIFEST.json')['files'];assert set(paths)=={x['path'] for x in files}
paths=paths|{x:'campaign/gates/122-first-halt-reuse/review/'+x for x in ['MANIFEST.json','SHA256SUMS']}
for old,newpath in paths.items():assert (P/old).read_bytes()==(R/newpath).read_bytes()
bl=(C/'BUNDLE-FILES.txt').read_text().splitlines();assert len(bl)==len(set(bl))
for path in bl:assert (R/path).is_file(),path
portable=(P/'BUNDLE-FILES.portable.txt').read_text().splitlines();assert {paths[x] for x in portable}<=set(bl)
canon={'all2439_frozen_and_integrity_files_copied_byte_exact':True,'total_path_map':True,'bundle_list_rows_observed':len(bl),'all_selected_paths_exist':True,'all1423_portable_inputs_in_selection':True,'no_staging_or_final_bundle_claim':True,'canonical_pack_sha256_observed':H((C/'pack.md').read_bytes()),'canonical_adoption_sha256_observed':H((C/'adoption.json').read_bytes())}
save('actual44-screen-and23-source-row-checks.json',{'pass':True,'BASE':sa,'HEAD':sb,'new':0,'gone':19,'persistent_score_changed':4,'persistent_exact':2560,'no_new_pair_scoring':True,'source_span_checks18':spanchecks,'all23_dispositions':rowchecks,'request88_source_bindings':True,'helper4_Git_bindings':helperchecks})
save('actual8-owner-QA-and-canonical-path-checks.json',{'pass':True,'QA':qa,'actual6_stdout_stderr_receipts_verified':True,'only_position_dynamic_line_count_identity_normalization':True,'canonical_adoption':canon,'pending_history_note':'Frozen screen/PAIR-REVIEW-PENDING.json is preparation history superseded by pair-dispositions.json/.md and FINAL-REVIEW; root canonical clarification requested.'})
print('PASS actual44 rows0/19/4; all18 raw spans and23 dispositions; inherited lint only; total canonical2439 byte mapping and1492 selected paths')
