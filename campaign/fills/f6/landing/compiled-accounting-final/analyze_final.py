from pathlib import Path
import json,hashlib,gzip,base64,re,collections,datetime
O=Path('/private/tmp/f6-compiled-accounting-final');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/fills/f6/landing/compiled-accounting';c=json.loads((O/'context.json').read_bytes());STD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(label,folder):
 run=json.loads((folder/(label+'-run.json')).read_bytes());assert run['exit']==run['errors']==run['warnings']==0
 gz=(folder/(label+'.out.gz')).read_bytes();enc=(folder/(label+'.out.gz.base64.txt')).read_bytes();assert base64.b64decode(b''.join(enc.split()),validate=True)==gz
 raw=gzip.decompress(gz);raw.decode('utf8')
 for d,n,h in [(raw,'raw_stdout_stderr_bytes','raw_stdout_stderr_sha256'),(gz,'gzip_bytes','gzip_sha256'),(enc,'utf8_base64_bytes','utf8_base64_sha256')]:assert (len(d),sha(d))==(run[n],run[h])
 text=raw.decode();sets={}
 for prefix in ['CENSUS','ALLAX','PUBLICAX','TARGET','TARGETAX']:
  rows=[json.loads(ln[len(prefix)+1:]) for ln in text.splitlines() if ln.startswith(prefix+'|')];m={x['name']:x for x in rows};assert len(m)==len(rows);sets[prefix]=m
 C,A,U,T,TA=[sets[x] for x in ['CENSUS','ALLAX','PUBLICAX','TARGET','TARGETAX']]
 assert set(C)==set(A) and set(U)=={n for n,x in C.items() if not x['private']};assert all(U[n]==A[n] for n in U)
 assert set(T)==set(TA)=={n for n in C if n=='Complexity.space_universal' or n.startswith('Complexity.space_universal.') or '.f6_' in n}
 assert all(T[n]==C[n] and TA[n]==A[n] for n in T)
 assert re.findall(r'^COMPLETE\|(\d+)\|owners=1$',text,re.M)==[str(len(C))]
 assert not re.search(r'^(?:MISSING_TARGET|.*error:)',text,re.M)
 archive={'label':label,'source_head_of_execution':run['source_head'],'reused_baseline':folder==P or label=='Base','raw_bytes':len(raw),'raw_sha256':sha(raw),'gzip_bytes':len(gz),'gzip_sha256':sha(gz),'utf8_bytes':len(enc),'utf8_sha256':sha(enc),'full_unfiltered':True,'strict_base64_gzip_roundtrip':True}
 return sets,archive
base,bar=parse('Base',O);head,har=parse('Head',O);old,oldar=parse('Head',P)
for label,sets in [('base',base),('head',head)]:
 for key,name in [('CENSUS','census'),('ALLAX','allax'),('PUBLICAX','publicax'),('TARGET','target'),('TARGETAX','targetax')]:
  rows=list(sets[key].values())
  if label=='base':assert rows==json.loads((O/(name+'-base.json')).read_bytes())
  else:(O/(name+'-head.json')).write_text(json.dumps(rows,indent=2)+'\n')
 (O/('names-'+label+'.txt')).write_text('\n'.join(sorted(sets['CENSUS']))+'\n')
# All exact field changes, across baseline and previous-head comparisons.
def delta(a,b):
 A=a['CENSUS'];B=b['CENSUS'];shared=sorted(A.keys()&B.keys());added=sorted(B.keys()-A.keys());removed=sorted(A.keys()-B.keys());meta=[];ax=[]
 for n in shared:
  keys=sorted(A[n].keys()|B[n].keys());ds={k:{'before':A[n].get(k),'after':B[n].get(k)} for k in keys if A[n].get(k)!=B[n].get(k)}
  if ds:meta.append({'name':n,'changes':ds})
  if a['ALLAX'][n]!=b['ALLAX'][n]:ax.append({'name':n,'before':a['ALLAX'][n],'after':b['ALLAX'][n]})
 return {'added_names':added,'removed_names':removed,'shared_metadata_field_changes':meta,'shared_axiom_changes':ax}
main=delta(base,head);since=delta(old,head)
source_roots=json.loads((R/'campaign/fills/f6/review/final-2026-11-08/source-freeze.json').read_bytes())['added_private'];source_names=[x['name'] for x in source_roots]
rootnames={n for n in head['CENSUS'] if any(n.endswith('.'+s) for s in source_names)};assert len(rootnames)==len(source_names)==18
classified=[]
for n in main['added_names']:
 row=head['CENSUS'][n]
 if n in rootnames:kind='authored-private-proof'
 elif any(n.startswith(root+'.') for root in rootnames):kind='generated-private-proof-descendant'
 elif n.startswith('Complexity.space_universal.'):kind='generated-target-proof-descendant'
 else:kind='UNEXPECTED-new-owned-constant'
 classified.append({'name':n,'classification':kind,'kind':row['kind'],'private':row['private'],'internal':row['internal'],'simp':row['simp'],'unfold':row['unfold'],'typeExpr_sha256':sha(row['typeExpr'].encode()),'axioms':head['ALLAX'][n]['axioms']})
assert all(x['classification']!='UNEXPECTED-new-owned-constant' for x in classified)
assert all(x['kind']=='theorem' and not x['simp'] and not x['unfold'] and (x['private'] or x['internal']) for x in classified)
assert all(head['CENSUS'][n]['private'] for n in rootnames)
# Strict no-axiom-regression checks retain subset-of-standard definitions and exact target closures.
nonstandard=[x for x in head['ALLAX'].values() if not set(x['axioms'])<=STD];assert not nonstandard
newbad=[n for n in base['CENSUS'].keys()&head['CENSUS'].keys() if set(base['ALLAX'][n]['axioms'])<=STD and not set(head['ALLAX'][n]['axioms'])<=STD];assert not newbad
assert not main['shared_metadata_field_changes'] and not main['removed_names']
assert len(main['shared_axiom_changes'])==1 and main['shared_axiom_changes'][0]['name']=='Complexity.space_universal'
assert 'sorryAx' in base['ALLAX']['Complexity.space_universal']['axioms'] and set(head['ALLAX']['Complexity.space_universal']['axioms'])==STD
assert all(set(x['axioms'])<=STD for x in head['TARGETAX'].values())
public_new=[x for x in classified if not x['private']];assert all(x['internal'] and x['classification']=='generated-target-proof-descendant' for x in public_new)
# Save complete full type expressions plus compact type digests; no theorem values are rendered.
digests=[{'name':n,'typeExpr_utf8_bytes':len(x['typeExpr'].encode()),'typeExpr_sha256':sha(x['typeExpr'].encode()),'private':x['private'],'internal':x['internal'],'kind':x['kind']} for n,x in head['CENSUS'].items()]
(O/'head-type-digests.json').write_text(json.dumps(digests,indent=2)+'\n')
main.update({'added':classified,'authored_public_API_additions':0,'public_generated_internal_additions':public_new,'formerly_proved_acquired_nonstandard':newbad,'all_current_owned_axioms_standard_or_subset':True})
(O/'delta.json').write_text(json.dumps(main,indent=2)+'\n');(O/'delta-since-f72.json').write_text(json.dumps(since,indent=2)+'\n')
stats={}
for label,sets in [('Base',base),('PreviousHead',old),('Head',head)]:
 C=sets['CENSUS'];stats[label]={'all':len(C),'nonprivate':sum(not x['private'] for x in C.values()),'nonprivate_noninternal':sum(not x['private'] and not x['internal'] for x in C.values()),'private':sum(x['private'] for x in C.values()),'ALLAX':len(sets['ALLAX']),'PUBLICAX':len(sets['PUBLICAX']),'sorry_dependent_ALLAX':sum('sorryAx' in x['axioms'] for x in sets['ALLAX'].values()),'sorry_dependent_PUBLICAX':sum('sorryAx' in x['axioms'] for x in sets['PUBLICAX'].values()),'kind_counts':dict(collections.Counter(x['kind'] for x in C.values())),'target_F6_subset':len(sets['TARGETAX'])}
targetpub=[n for n in head['TARGETAX'] if n.startswith('Complexity.space_universal.')];assert all(set(head['ALLAX'][n]['axioms'])<=STD for n in targetpub)
summary={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate_head':c['candidate_head'],'source_sha256':c['source_sha256'],'baseline_source_pin':c['baseline_source_pin'],'BASE_reused_not_rerun':True,'HEAD_fresh_native_import':True,'endpoints':stats,'authored_private_roots':len(rootnames),'all_added_classified':dict(collections.Counter(x['classification'] for x in classified)),'added_constants':len(main['added_names']),'removed_constants_vs_BASE':len(main['removed_names']),'shared_metadata_changes_vs_BASE':len(main['shared_metadata_field_changes']),'shared_axiom_changes_vs_BASE':len(main['shared_axiom_changes']),'authored_public_API_additions':0,'generated_nonprivate_internal_additions':len(public_new),'all_current_owned_AXIOMS_standard_or_subset':not nonstandard,'all_target_F6_AXIOMS_standard_or_subset':True,'target_F6_axiom_sets':[{'axioms':list(ax),'constants':count} for ax,count in collections.Counter(tuple(x['axioms']) for x in head['TARGETAX'].values()).items()],'all_current_target_auxiliaries_individually_accounted':targetpub,'former_proved_acquired_nonstandard':len(newbad),'since_f72':{'added':since['added_names'],'removed':since['removed_names'],'shared_metadata_field_changes_count':len(since['shared_metadata_field_changes']),'shared_axiom_changes_count':len(since['shared_axiom_changes'])},'no_proof_value_prettyprint':True,'fresh_19scope_and_72paired_controls':json.loads((O/'scoped-seals-final/control-verification.json').read_bytes())['result'],'fresh_arbitrary_Fintype_diagnostic':json.loads((O/'finite-witness-diagnostic-final/verification.json').read_bytes())['result'],'Fintype_limit_preserved':'Existing ineffective two-instance controls and separate finite-witness diagnostic remain separately scoped; this run is compiled accounting, not a full-opacity certificate','scope':'Fresh import-only HEAD metadata/ALLAX/PUBLICAX; trusted BASE reused after complete authentication. Root owns MF62 replay/gate/merge.'}
(O/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');(O/'utf8-archive-verification.json').write_text(json.dumps({'archives':[bar,har],'previous_HEAD_archive_checked_as_historical':oldar,'complete_raw_no_cap':True,'no_values_printed':True},indent=2)+'\n');print(json.dumps(summary,indent=2))
