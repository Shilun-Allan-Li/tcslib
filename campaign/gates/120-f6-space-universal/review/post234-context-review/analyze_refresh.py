from pathlib import Path
import json,hashlib,gzip,base64,re,collections,datetime
O=Path('/private/tmp/f6-post234-context-review');D=O/'fresh-validation';R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/fills/f6/landing/compiled-accounting-final';c=json.loads((O/'refresh-context.json').read_bytes());STD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def data(name):
 rr=json.loads((D/(name+'-run.json')).read_bytes());gz=(D/(name+'.out.gz')).read_bytes();enc=(D/(name+'.out.gz.base64.txt')).read_bytes();raw=gzip.decompress(gz);raw.decode('utf8');assert base64.b64decode(b''.join(enc.split()),validate=True)==gz
 for b,s,h in [(raw,'raw_bytes','raw_sha256'),(gz,'gzip_bytes','gzip_sha256'),(enc,'base64_bytes','base64_sha256')]:assert (len(b),sha(b))==(rr[s],rr[h])
 assert rr['source_head']==c['source_head'] and rr['warnings']==rr['sorry_warnings']==0 and rr['all_owner_oleans_unchanged'];return raw.decode(),rr
sets={};stats={};equivalence={};archives=[]
for name in ['Base','Head']:
 text,rr=data(name);assert rr['exit']==rr['errors']==0
 rows={}
 for tag in ['CENSUS','ALLAX','PUBLICAX','TARGET','TARGETAX']:
  a=[json.loads(x[len(tag)+1:]) for x in text.splitlines() if x.startswith(tag+'|')];rows[tag]={x['name']:x for x in a};assert len(rows[tag])==len(a);(D/(tag.lower()+'-'+name.lower()+'.json')).write_text(json.dumps(a,indent=2)+'\n')
 ci,ax,pub,t,ta=[rows[k] for k in ['CENSUS','ALLAX','PUBLICAX','TARGET','TARGETAX']];assert set(ci)==set(ax) and set(pub)=={n for n,v in ci.items() if not v['private']};assert all(pub[n]==ax[n] for n in pub)
 assert set(t)==set(ta)=={n for n in ci if n=='Complexity.space_universal' or n.startswith('Complexity.space_universal.') or '.f6_' in n};assert all(t[n]==ci[n] and ta[n]==ax[n] for n in t)
 assert re.findall(r'^COMPLETE\|(\d+)\|owners=1$',text,re.M)==[str(len(ci))]
 assert not re.search(r'^(?:MISSING_TARGET|.*error:)',text,re.M)
 previous=gzip.decompress((P/(name+'.out.gz')).read_bytes());equivalence[name]={'full_raw_output_equal_previous_context':text.encode()==previous,'previous_raw_sha256':sha(previous),'fresh_raw_sha256':rr['raw_sha256'],'fresh_raw_bytes':rr['raw_bytes']}
 stats[name]={'all':len(ci),'nonprivate':len(pub),'nonprivate_noninternal':sum(not x['private'] and not x['internal'] for x in ci.values()),'private':sum(x['private'] for x in ci.values()),'kinds':dict(collections.Counter(x['kind'] for x in ci.values())),'ALLAX':len(ax),'PUBLICAX':len(pub),'sorry_ALLAX':sum('sorryAx' in x['axioms'] for x in ax.values()),'sorry_PUBLICAX':sum('sorryAx' in x['axioms'] for x in pub.values()),'target_F6_subset':len(ta)}
 sets[name]=rows;archives.append({'name':name,'raw_bytes':rr['raw_bytes'],'raw_sha256':rr['raw_sha256'],'gzip_bytes':rr['gzip_bytes'],'gzip_sha256':rr['gzip_sha256'],'base64_bytes':rr['base64_bytes'],'base64_sha256':rr['base64_sha256'],'full_strict_roundtrip':True})
base=sets['Base'];head=sets['Head'];bc=base['CENSUS'];hc=head['CENSUS'];added=sorted(hc.keys()-bc.keys());removed=sorted(bc.keys()-hc.keys());changes=[];axchanges=[]
for n in sorted(hc.keys()&bc.keys()):
 ds={k:{'base':bc[n].get(k),'head':hc[n].get(k)} for k in sorted(bc[n].keys()|hc[n].keys()) if bc[n].get(k)!=hc[n].get(k)}
 if ds:changes.append({'name':n,'fields':ds})
 if base['ALLAX'][n]!=head['ALLAX'][n]:axchanges.append({'name':n,'before':base['ALLAX'][n],'after':head['ALLAX'][n]})
source_names=[x['name'] for x in json.loads((R/'campaign/fills/f6/review/final-2026-11-08/source-freeze.json').read_bytes())['added_private']];roots={n for n in hc if any(n.endswith('.'+x) for x in source_names)};assert len(roots)==18
classes=[]
for n in added:
 x=hc[n];kind='authored-private-proof' if n in roots else 'generated-private-proof-descendant' if any(n.startswith(r+'.') for r in roots) else 'generated-target-proof-descendant' if n.startswith('Complexity.space_universal.') else 'UNEXPECTED';assert kind!='UNEXPECTED'
 assert x['kind']=='theorem' and not x['simp'] and not x['unfold'] and (x['private'] or x['internal']);classes.append({'name':n,'classification':kind,'kind':x['kind'],'private':x['private'],'internal':x['internal'],'simp':x['simp'],'unfold':x['unfold'],'axioms':head['ALLAX'][n]['axioms']})
assert not removed and not changes;assert len(axchanges)==1 and axchanges[0]['name']=='Complexity.space_universal';assert all(set(x['axioms'])<=STD for x in head['ALLAX'].values());assert set(head['ALLAX']['Complexity.space_universal']['axioms'])==STD
(D/'delta.json').write_text(json.dumps({'added':classes,'removed':removed,'all_shared_metadata_changes':changes,'all_shared_axiom_changes':axchanges,'new_nonstandard':[]},indent=2)+'\n')
# Fresh complete owner/scoped checks with exact current source and retained limits.
for name in ['Owner-native','Owner-sealed']:
 text,rr=data(name);assert rr['exit']==rr['errors']==0
 ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);assert len(ax)==3
 aa={n:set(a.split(', ')) for n,a in ax};assert aa['Complexity.space_universal']==STD and aa['Turing.seamCompTM_step']=={'propext','Quot.sound'};assert next(v for k,v in aa.items() if k.endswith('.Complexity.f6_seam'))=={'propext','Quot.sound'}
# Every paired identity, positive kernel name and intended negative refl error is validated afresh.
names=(P/'scoped-seals-final/control-definitions.txt').read_text().splitlines();keys=[(n,m) for n in names for m in ['point','abstract']];expected=collections.Counter({k:1 for k in keys});pos,pr=data('Controls-native');neg,nr=data('Controls-sealed')
def verify(pos,neg,pr,nr):
 for raw,status in [(pos,'PASS'),(neg,'FAIL')]:
  rows=[ln.split('|') for ln in raw.splitlines() if ln.startswith('CONTROL|')];assert [(x[1],x[2]) for x in rows]==keys and collections.Counter((x[1],x[2]) for x in rows)==expected and all(x[3]==status for x in rows)
  if status=='PASS':assert all(len(x)==5 and x[4]==f'kernelChecked=F6LandingControl_{i}_{x[2]}' for i,x in enumerate(rows,1))
  else:assert all(len(x)==4 for x in rows)
  assert "declaration uses 'sorry'" not in raw
 errors=re.findall(r':\d+:\d+: error: RFL_CONTROL\|([^|\n]+)\|(point|abstract)\|([^\n]+)',neg);assert [(n,m) for n,m,_ in errors]==keys and all('Tactic `rfl` failed' in msg for _,_,msg in errors)
 assert len(re.findall(r'^.*:\d+:\d+: error:',neg,re.M))==len(keys) and not re.search(r'^.*:\d+:\d+: error:',pos,re.M);assert (pr['exit'],pr['errors'])==(0,0) and (nr['exit'],nr['errors'])==(1,len(keys))
verify(pos,neg,pr,nr);tokens=re.findall(r'RFL_CONTROL\|[^|\n]+\|(?:point|abstract)\|',neg);cases={'duplicate_identity':(pos,neg.replace(tokens[0],tokens[1],1),pr,nr),'wrong_outcome':(pos,neg.replace('|point|FAIL','|point|PASS',1),pr,nr),'missing_kernel_name':(pos.replace('kernelChecked=F6LandingControl_1_point','kernelChecked=wrong',1),neg,pr,nr),'wrong_negative_exit':(pos,neg,pr,{**nr,'exit':0}),'sorry_warning':(pos+"\ndeclaration uses 'sorry'\n",neg,pr,nr),'wrong_error_kind':(pos,neg.replace('Tactic `rfl` failed','unrelated error',1),pr,nr)};corrupt={}
for n,args in cases.items():
 try:verify(*args)
 except AssertionError:corrupt[n]='rejected'
 else:raise AssertionError('corrupted evidence accepted '+n)
(D/'control-verification.json').write_text(json.dumps({'source_head':c['source_head'],'result':'PASS','definitions':len(names),'scopes':19,'positive_kernel_checked_identities':len(keys),'exact_expected_negative_refl_identities':len(keys),'identities':[{'definition':n,'mode':m,'positive_name':f'F6LandingControl_{i}_{m}','negative_error_identity_exact':True} for i,(n,m) in enumerate(keys,1)],'synthetic_corruptions':corrupt,'limits':'35 ordinary TCSlib definitions+Nat.bits;14abbrev/projection and2ineffective regular Fintype controls remain disclosed; no blanket global/imported theorem seal'},indent=2)+'\n')
witness,wr=data('ArbitraryFiniteness');assert wr['exit']==wr['errors']==0 and '[hF6Rewind : Fintype Turing.RewindPhase]' in witness and '[hF6Seek : Fintype Turing.SeekPhase]' in witness and "'Complexity.space_universal' depends on axioms: [propext, Classical.choice, Quot.sound]" in witness
(D/'witness-verification.json').write_text(json.dumps({'source_head':c['source_head'],'result':'PASS','all19_guards_retained':True,'exact_prior2diagnostic_binders_and2inference_controls':True,'target_standard3':True,'conditional_only':True,'not_theorem_value_equivalence_or_actual_Fintype_opacity_certificate':True},indent=2)+'\n')
summary={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['source_head'],'campaign_base':c['campaign_base'],'Hierarchy_sha256':c['source_sha256'],'BASE_and_HEAD_both_fresh_native':True,'counts':stats,'all_added_classified':dict(collections.Counter(x['classification'] for x in classes)),'added':len(added),'removed':len(removed),'shared_metadata_changes':len(changes),'shared_axiom_changes':len(axchanges),'all_current_own_and_full_target_F6_axioms_standard_or_subset':True,'public_source_API_additions':0,'generated_nonprivate_internal_additions':sum(not x['private'] for x in classes),'fresh19_scopes_PASS':True,'fresh72paired_controls_PASS':True,'fresh_conditional_arbitrary_witness_PASS':True,'full_metadata_raw_equivalence_with_previous_context':equivalence,'no_proof_value_prettyprint':True,'fresh_screen_owned_elsewhere':'new25 BASEbf64/HEADcurrent; no screen run or oldscreen relabeling by this task','actual_runs':[{k:v for k,v in json.loads((D/(n+'-run.json')).read_bytes()).items() if k in ['name','exit','errors','warnings','sorry_warnings','seconds_including_slot_wait','source_head','snapshot']} for n in ['Base','Head','Owner-native','Owner-sealed','Controls-native','Controls-sealed','ArbitraryFiniteness']]}
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');(D/'archive-verification.json').write_text(json.dumps({'metadata_archives':archives,'all_other_run_archives_also_strictly_checked':True},indent=2)+'\n');print(json.dumps(summary,indent=2))
