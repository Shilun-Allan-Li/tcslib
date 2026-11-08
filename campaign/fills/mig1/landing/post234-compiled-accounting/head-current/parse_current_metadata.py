from pathlib import Path
import gzip,json,hashlib,collections,datetime
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());B=Path(ctx['baseline_frozen_folder']);rows={};ax={};pub={};apis=[];complete=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
for line in gzip.open(P/'Head-inventory.out.gz','rt'):
 if '|{'in line:
  pre,payload=line.split('|',1);tag=pre.rsplit(' ',1)[-1]
  if tag not in ['CENSUS','ALLAX','PUBLICAX']:continue
  d=json.loads(payload);n=d['name'];dest={'CENSUS':rows,'ALLAX':ax,'PUBLICAX':pub}[tag];assert n not in dest
  if tag=='CENSUS':
   typ=d.pop('typeExpr').encode();d['typeExprBytes']=len(typ);d['typeExprSHA256']=sha(typ);d['typeExprArchive']='Head-inventory.out.gz.base64.txt'
  dest[n]=d
 elif 'API_PRESENT|'in line:apis.append(line.split('API_PRESENT|',1)[1].strip())
 elif 'COMPLETE|'in line:complete.append(line.strip().split('COMPLETE|',1)[1])
assert set(rows)==set(ax)and set(pub)=={n for n,d in rows.items()if not d['private']}and all(pub[n]==ax[n]for n in pub);assert len(apis)==len(set(apis))==5 and complete==[str(len(rows))+'|primaryOwners=12|contextOwners=1']
ci={};attrs={};simp=collections.defaultdict(list);marks=[]
for line in gzip.open(P/'Head-ciattrs.out.gz','rt'):
 if line.startswith(('CI|','ATTR|','SIMP_RULE|')):
  tag,n,j=line.split('|',2);d=json.loads(j)
  if tag=='SIMP_RULE':simp[n].append(d)
  else:
   dst=ci if tag=='CI'else attrs;assert n not in dst;dst[n]=d
 elif line.startswith(('CICOMPLETE|','SIMPCOMPLETE')):marks.append(line.strip())
assert set(ci)==set(attrs)==set(rows)and marks==[f'CICOMPLETE|constants={len(rows)}|simp_environment_unchanged=true','SIMPCOMPLETE']
for n,r in rows.items():
 assert ci[n]['levelParams']==r['levelParams']and ci[n]['unsafe']==r['unsafe']and ci[n]['partial']==r['partial'];a=attrs[n];assert a['simp']==r['simp']and a['simp_unfold']==r['unfold']and a['protected']==r['protected']and a['instance_priority']==r['instancePriority']and a['reducibility']==r['reducibility'];r['structural_CI']=ci[n];r['reflected_attributes']=attrs[n];r['axioms']=ax[n]['axioms']
base=json.loads((B/'map-base-complete.json').read_text());bax=json.loads((B/'allax-base.json').read_text());bpub=json.loads((B/'publicax-base.json').read_text());bsimp=json.loads((B/'effective-simp-base.json').read_text())
for n in base:base[n]['axioms']=bax[n]['axioms']
primary=set(ctx['primary_owners']);context=set(ctx['context_owners']);std={'propext','Classical.choice','Quot.sound'}
def stats(rs,owners,ss):
 ns=[n for n,r in rs.items()if r['owner']in owners];return{'all':len(ns),'private':sum(rs[n]['private']for n in ns),'nonprivate':sum(not rs[n]['private']for n in ns),'nonprivate_noninternal':sum(not rs[n]['private']and not rs[n]['internal']for n in ns),'kinds':dict(collections.Counter(rs[n]['kind']for n in ns)),'owner_counts':dict(collections.Counter(rs[n]['owner']for n in ns)),'axiom_distribution':dict(collections.Counter(','.join(rs[n]['axioms'])for n in ns)),'nonstandard':{n:rs[n]['axioms']for n in ns if not set(rs[n]['axioms'])<=std},'type_payload_utf8_bytes':sum(rs[n]['typeExprBytes']for n in ns),'effective_simp_rules':sum(len(v)for n,v in ss.items()if rs[n]['owner']in owners),'ALLAX':len(ns),'PUBLICAX':sum(not rs[n]['private']for n in ns)}
added=sorted(set(rows)-set(base));removed=sorted(set(base)-set(rows));shared=sorted(set(rows)&set(base));fields=['owner','kind','private','internal','levelParams','valuePresent','unsafe','partial','kernelHints','reducibility','simp','unfold','protected','instancePriority','typeExprBytes','typeExprSHA256','structural_CI','reflected_attributes','axioms'];changes={k:[{'name':n,'base':base[n][k],'head':rows[n][k]}for n in shared if base[n][k]!=rows[n][k]]for k in fields}
public_added=[n for n in added if not rows[n]['private']];public_removed=[n for n in removed if not base[n]['private']];public_changes={k:[r for r in v if not base[r['name']]['private']or not rows[r['name']]['private']]for k,v in changes.items()};simp_added={n:v for n,v in simp.items()if n not in bsimp};simp_removed={n:v for n,v in bsimp.items()if n not in simp};simp_changed={n:{'base':bsimp[n],'head':simp[n]}for n in set(bsimp)&set(simp)if bsimp[n]!=simp[n]}
delta={'source':ctx['source'],'base':ctx['base'],'added':{n:rows[n]for n in added},'removed':{n:base[n]for n in removed},'shared_field_changes':changes,'public_added':public_added,'public_removed':public_removed,'public_shared_field_changes':public_changes,'effective_simp_changes':{'added':simp_added,'removed':simp_removed,'shared_changed':simp_changed},'no_proof_value_equality_claim':True};save('delta-base-head.json',delta);save('map-head-complete.json',rows);save('allax-head.json',ax);save('publicax-head.json',pub);save('effective-simp-head.json',dict(simp))
summary={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ctx['source'],'base':ctx['base'],'BASE_reused_only_after_all66_frozen_hashes_and895_object_context_checks':True,'HEAD_fresh':True,'Base_primary12':stats(base,primary,bsimp),'Head_primary12':stats(rows,primary,simp),'Base_Finite_context':stats(base,context,bsimp),'Head_Finite_context':stats(rows,context,simp),'all_primary_and_context':{'Base':len(base),'Head':len(rows)},'added':len(added),'removed':len(removed),'shared':len(shared),'public_added':len(public_added),'public_removed':len(public_removed),'shared_field_change_counts':{k:len(v)for k,v in changes.items()},'public_shared_field_change_counts':{k:len(v)for k,v in public_changes.items()},'simp_added':len(simp_added),'simp_removed':len(simp_removed),'simp_changed':len(simp_changed),'all_census_CI_attrs_ALLAX_exact_coverage':True,'PUBLICAX_exact_nonprivate':True,'all5_current_APIs_present':apis,'no_theorem_proof_values_rendered':True,'selected_root_AXIOMS_pending':True};save('metadata-summary.json',summary)
print(json.dumps({k:v for k,v in summary.items()if k not in ['Base_primary12','Head_primary12','Base_Finite_context','Head_Finite_context']},indent=2));print('PRIMARY',json.dumps({s:{k:summary[s+'_primary12'][k]for k in ['all','private','nonprivate','nonstandard','effective_simp_rules']}for s in ['Base','Head']},indent=2));print('PUBLIC_ADDED',public_added);print('PUBLIC_REMOVED',public_removed)
