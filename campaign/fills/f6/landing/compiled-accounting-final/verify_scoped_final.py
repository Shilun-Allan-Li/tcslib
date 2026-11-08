from pathlib import Path
import json,re,collections,hashlib,base64,gzip,datetime
O=Path('/private/tmp/f6-compiled-accounting-final');D=O/'scoped-seals-final';meta=json.loads((D/'source-equivalence.json').read_bytes());names=(D/'control-definitions.txt').read_text().splitlines();keys=[(n,m) for n in names for m in ['point','abstract']];expected=collections.Counter({k:1 for k in keys})
def sha(b):return hashlib.sha256(b).hexdigest()
runs={};archive=[]
for name in ['Owner-native','Owner-sealed','Controls-native','Controls-sealed']:
 r=json.loads((D/(name+'-run.json')).read_bytes());raw=(D/(name+'.out')).read_bytes();gz=(D/(name+'.out.gz')).read_bytes();enc=(D/(name+'.out.gz.base64.txt')).read_bytes();assert base64.b64decode(b''.join(enc.split()),validate=True)==gz and gzip.decompress(gz)==raw
 for b,bs,hs in [(raw,'raw_stdout_stderr_bytes','raw_stdout_stderr_sha256'),(gz,'gzip_bytes','gzip_sha256'),(enc,'utf8_base64_bytes','utf8_base64_sha256')]:assert (len(b),sha(b))==(r[bs],r[hs])
 assert sha((D/r['input']).read_bytes())==r['input_sha256'];assert r['source_unchanged'] and r['owner_olean_unchanged'];assert r['warnings']==r['sorry_warnings']==0
 runs[name]=r;archive.append({'name':name,'raw_bytes':len(raw),'raw_sha256':sha(raw),'gzip_bytes':len(gz),'gzip_sha256':sha(gz),'utf8_bytes':len(enc),'utf8_sha256':sha(enc),'complete_strict_roundtrip':True})
 if name.startswith('Owner'):
  assert r['exit']==r['errors']==0
  rows=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",raw.decode(),re.M);assert len(rows)==3,rows
  axioms={n:set(a.split(', ')) for n,a in rows};assert axioms['Complexity.space_universal']=={'propext','Classical.choice','Quot.sound'};assert axioms['Turing.seamCompTM_step']=={'propext','Quot.sound'}
  private=next(v for k,v in axioms.items() if k.endswith('.Complexity.f6_seam'));assert private=={'propext','Quot.sound'}
pos=(D/'Controls-native.out').read_text();neg=(D/'Controls-sealed.out').read_text()
def verify(pos,neg,pr,nr):
 for text,status in [(pos,'PASS'),(neg,'FAIL')]:
  rows=[ln.split('|') for ln in text.splitlines() if ln.startswith('CONTROL|')]
  assert collections.Counter((x[1],x[2]) for x in rows)==expected and [(x[1],x[2]) for x in rows]==keys
  assert all(x[3]==status for x in rows)
  if status=='PASS':assert all(len(x)==5 and x[4]==f'kernelChecked=F6LandingControl_{i}_{x[2]}' for i,x in enumerate(rows,1))
  else:assert all(len(x)==4 for x in rows)
  assert "declaration uses 'sorry'" not in text
 ds=re.findall(r':\d+:\d+: error: RFL_CONTROL\|([^|\n]+)\|(point|abstract)\|([^\n]+)',neg)
 assert [(n,m) for n,m,_ in ds]==keys
 assert all('Tactic `rfl` failed' in text for _,_,text in ds)
 assert len(re.findall(r'^.*:\d+:\d+: error:',neg,re.M))==72
 assert not re.search(r'^.*:\d+:\d+: error:',pos,re.M)
 assert (pr['exit'],pr['errors'])==(0,0) and (nr['exit'],nr['errors'])==(1,72)
pr=runs['Controls-native'];nr=runs['Controls-sealed'];verify(pos,neg,pr,nr)
ids=re.findall(r'RFL_CONTROL\|[^|\n]+\|(?:point|abstract)\|',neg)
cases={'duplicate-negative-identity':(pos,neg.replace(ids[0],ids[1],1),pr,nr),'wrong-negative-outcome':(pos,neg.replace('|point|FAIL','|point|PASS',1),pr,nr),'missing-kernel-name':(pos.replace('kernelChecked=F6LandingControl_1_point','kernelChecked=missing',1),neg,pr,nr),'wrong-negative-exit':(pos,neg,pr,{**nr,'exit':0}),'unexpected-sorry-warning':(pos+"\ndeclaration uses 'sorry'\n",neg,pr,nr),'same-count-non-rfl-error':(pos,neg.replace('Tactic `rfl` failed','unrelated failure',1),pr,nr)}
rejected={}
for name,args in cases.items():
 try:verify(*args)
 except AssertionError:rejected[name]='rejected'
 else:raise AssertionError('bad evidence accepted '+name)
res={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':json.loads((O/'context.json').read_bytes())['candidate_head'],'result':'PASS fresh current19-scoped owner and72effective paired controls','scopes':19,'guards':names,'TCSlib_effective_definitions':35,'Mathlib_extra':'Nat.bits','positive_kernel_checked_identities':72,'expected_negative_identities':72,'identities':[{'definition':n,'mode':m,'kernel_positive':f'F6LandingControl_{i}_{m}','negative_error_matches_identity':True,'negative_is_refl_failure':True} for i,(n,m) in enumerate(keys,1)],'negative_corruption_cases':rejected,'actual_exit_sequence':[runs[n]['exit'] for n in ['Owner-native','Owner-sealed','Controls-native','Controls-sealed']],'owner_native_seconds':runs['Owner-native']['seconds_including_any_slot_wait'],'owner_sealed_seconds':runs['Owner-sealed']['seconds_including_any_slot_wait'],'source_equivalence_verified':True,'default_MetaM_refl':True,'transparency_or_unsafe_override':False,'scope_limits':meta['other_limits'],'excluded_regular_Fintype_instances':meta['excluded_regular_Fintype_instances'],'not_a_global_imported_proof_seal':True}
(D/'control-verification.json').write_text(json.dumps(res,indent=2)+'\n');(D/'utf8-archive-verification.json').write_text(json.dumps({'archives':archive},indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k not in ['guards','identities']},indent=2))
