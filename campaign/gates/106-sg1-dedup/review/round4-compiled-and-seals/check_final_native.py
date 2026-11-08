from pathlib import Path
import json,gzip,hashlib,re,collections,subprocess,datetime
P=Path('/private/tmp/g106-r4-compiled-and-seals');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');ctx=json.loads((P/'context.json').read_text());std={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def raw(name,exitcode=0,errors=0):
 r=json.loads((P/(name+'-run.json')).read_text());b=gzip.decompress((P/(name+'.out.gz')).read_bytes());assert(r['exit'],r['errors'],r['warnings'],r['sorry_warnings'])==(exitcode,errors,0,0)and(len(b),sha(b))==(r['raw_bytes'],r['raw_sha256']);return b.decode()
h=json.loads((P/'map-head.json').read_text())['census'];records=json.loads((P/'current-root-native-records.json').read_text());roots=records['ROOTMAP'];descs=records['ROOTDESC'];assert len(roots)==45 and len({r['compiled_name']for r in roots})==45;selected={};desc_names=set()
for r in roots:
 root=r['compiled_name'];actual=[q for q in descs if q['root']==root];expected={n for n in h if n==root or n.startswith(root+'.')};assert{q['name']for q in actual}==expected and r['private']==h[root]['private']and r['owner']==h[root]['owner']
 for q in actual:
  n=q['name'];assert all(h[n][k]==q[k]for k in ['owner','kind','private','internal','axioms'])and set(q['axioms'])<=std;selected[n]=q
  if n!=root:desc_names.add(n)
assert len(selected)==138 and len(desc_names)==93 and sum(r['private']for r in roots)==40
controls=[];proofs=[]
for row in json.loads((P/'F4-control-identities.json').read_text()):
 label=row['context'];want={(r['definition'],r['mode']):r['kernel_name']for r in row['identities']};pos=raw('F4-'+label+'-controls-native');neg=raw('F4-'+label+'-controls-sealed',1,12);ps=re.findall(r'(?m)^CONTROL\|([^|]+)\|(point|abstract)\|PASS\|kernelChecked=(\S+)$',pos);ns=re.findall(r'(?m)^CONTROL\|([^|]+)\|(point|abstract)\|FAIL$',neg);es=re.findall(r'error: RFL_CONTROL\|([^|]+)\|(point|abstract)\|Tactic `rfl` failed',neg);assert len(ps)==len(ns)==len(es)==12 and{(n,m):k for n,m,k in ps}==want and set(ns)==set(es)==set(want)
 for mode in ['native','sealed']:
  text=raw('F4-'+label+'-'+mode);m=re.search(r'depends on axioms: (\[[\s\S]*?\])',text);assert m,text;ax=[]if m[1]=='[]'else re.split(r',\s*',m[1][1:-1].strip());assert set(ax)=={'propext','Quot.sound'};proofs.append({'context':label,'mode':mode,'axioms':ax,'native_success':True})
 controls.append({'context':label,'guards':6,'positive_kernel_checked':12,'negative_exact_refl_failures':12,'all_identities_exact':True,'negative_exit1_expected':True})
# Compare all17 earlier current repair chunks literally across their exact source generations.
def chunk(text,name):
 ls=text.splitlines(keepends=True);i=next(i for i,l in enumerate(ls)if l.startswith('private lemma '+name+' ' )or l.startswith('private lemma '+name+':')or l.startswith('private lemma '+name+' :'))
 lo=i
 while lo>0 and not ls[lo-1].startswith('/--'):lo-=1
 lo-=1;assert lo>=0;j=i+1
 while j<len(ls)and not ls[j].startswith(('/--','private lemma ','end ')):j+=1
 return ''.join(ls[lo:j]).rstrip().encode()
sets={'TCSlib/Complexity/ClassNP/SAT.lean':['sat_pt_pair_input','sat_pt_mapSnd','sat_pt_pair','sat_pt_append','sat_pt_unaryLength'],'TCSlib/Complexity/CookLevin/Hardness.lean':['clNative_linear','clNative_map','clNative_pair','clNative_append','clNative_unary','clA5_pt_const','clA5_pt_cond','clA5_pt_and','clA5Pair_sizes','clA5Le_native','clA5Drop_native'],'TCSlib/Complexity/ClassNP/Tautology.lean':['taut_comp_on_image']};unchanged=[]
for path,names in sets.items():
 old=subprocess.check_output(['git','show','79e7c63a6bfa5f002663924f5c7d4e72db705026:'+path],cwd=R).decode();now=(P/'source/Head'/(path+'.txt')).read_text()
 for name in names:
  a=chunk(old,name);b=chunk(now,name);assert a==b,(path,name);unchanged.append({'path':path,'name':name,'bytes':len(b),'sha256':sha(b),'complete_doc_header_body_unchanged':True})
assert len(unchanged)==17
save('prior17-source-byte-identity.json',{'old_source':'79e7c63a6bfa5f002663924f5c7d4e72db705026','current_source':ctx['source'],'all17':unchanged,'older_seals_keep_their_original_source_context_current2F4_scopes_fresh':True})
# Complete frozen replay provenance, not a fresh replay executed by this reviewer.
d=R/'campaign/gates/106-sg1-dedup/evidence/replay-msg8';mb=(d/'MANIFEST.json').read_bytes();assert sha(mb)=='19199930c6b65de22c7b941edd82a63654971e750aafcff43e0c3caa2a642314';mr=json.loads(mb);mr=mr if isinstance(mr,list)else mr['files']
for r in mr:
 b=(d/r['path']).read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256'])
receipt=json.loads((d/'receipt.json').read_text());assert receipt['head']==ctx['source']and receipt['snapshot_Lean_base']==ctx['base']and receipt['modules']==329 and receipt['result']=='PASS'and receipt['static_total']==66 and receipt['pipeline_exit']==receipt['failed']==receipt['error_rows']==receipt['static_mismatches']==0
order=(d/'order-msg8.txt').read_text().splitlines();log=(d/'replay-msg8.log').read_text();rs=re.findall(r'(?m)^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',log);assert len(rs)==329 and[r[0]for r in rs]==order and all(r[1:3]==('0','0')for r in rs)and sum(int(r[3])for r in rs)==66
launch=(d/'replay-msg8-launches.log').read_text().splitlines();ln=[re.search(r'(?:-j4\s+)+(\S+)\.lean(?:\s|$)',l).group(1)for l in launch];assert ln==order and len(ln)==329
snap=json.loads((d/'snapshot-objects.json').read_text());before={s:json.loads((P/('snapshot-'+s.lower()+'-before.json')).read_text())for s in ['Base','Head']};assert{k:r['sha256']for k,r in before['Base'].items()}==snap['input_MAC5']and{k:r['sha256']for k,r in before['Head'].items()}==snap['output_MSG8']
for endpoint in ctx['snapshots']:
 side=endpoint['side'];tree=Path(endpoint['path']);after={str(q.relative_to(tree)):{'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(tree.rglob('*.olean'))};assert after==before[side]and len(after)==895;save('snapshot-'+side.lower()+'-after.json',after)
D=R/'campaign/gates/106-sg1-dedup/review/round3-final-compiled';old=json.loads((P/'prior-r3-accounting-before.json').read_text());now=[{'path':str(q.relative_to(D)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(D.rglob('*'))if q.is_file()];assert old==now;save('prior-r3-accounting-after.json',now)
sourcePop=json.loads((R/'campaign/gates/106-sg1-dedup/review/round4-source-screen25/capture.json').read_text())['population'];homes=sorted({r['owner']for r in records['CITED']});missing=[o for o in homes if o.replace('.','/')+'.lean'not in sourcePop]
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':ctx['source'],'compiled_BASE':ctx['base'],'all45_roots_40private5public_and93descendants_138distinct_standard_or_subset':True,'selected_axiom_distribution':dict(collections.Counter(','.join(q['axioms'])for q in selected.values())),'actual_F4_guard_population':6,'F4_definition_projections_abbreviations_excluded_explicitly':12,'fresh_proofs':proofs,'fresh_paired_controls':controls,'all17_prior_repair_chunks_byte_identical':True,'MSG8_frozen_manifest_sha256':sha(mb),'whole895_MAC5_MSG8_linked_and_unchanged':True,'MSG8_actual329rows_329j4_static66_reconciled':True,'prior_R3_frozen_accounting_all_files_unchanged':True,'direct_citation_records':len(records['CITED']),'direct_cited_TCSlib_owners':homes,'cited_owners_outside_current25':missing,'imported_theorem_values_not_traversed_or_printed':True,'no_proof_value_equality_global_seal_or_gate_clearance_claim':True}
save('current45-selected-AX.json',{'source':ctx['source'],'roots':roots,'all138_constants':selected,'all_standard_or_subset':True});save('final-native-verification.json',report)
ms=json.loads((P/'metadata-summary.json').read_text());ms['current45_root_coverage_pending_separate_probe']=False;ms['current45_root_coverage']='45roots+93descendants=138distinct,allstandard-or-subset';ms['F4_fresh6guards_12paired_per_actual_context_PASS']=True;save('metadata-summary.json',ms)
print(json.dumps({k:v for k,v in report.items()if k not in ['direct_cited_TCSlib_owners','fresh_proofs']},indent=2))
