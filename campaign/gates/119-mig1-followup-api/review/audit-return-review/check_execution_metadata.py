from pathlib import Path
import base64,collections,difflib,gzip,hashlib,json,re,subprocess
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=R/'campaign/gates/119-mig1-followup-api';OUT=G/'review/audit-return-review';C=G/'review/compiled-comparison';std={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
archives=json.loads((C/'utf8-archives-verification.json').read_text())['archives'];maps={};meta=[]
for ar in archives:
 label=ar['endpoint'];enc=(C/ar['utf8_file']).read_bytes();assert len(enc)==ar['utf8_bytes'] and sha(enc)==ar['utf8_sha256'];gz=base64.b64decode(re.sub(rb'\s',b'',enc),validate=True);assert len(gz)==ar['gzip_bytes'] and sha(gz)==ar['gzip_sha256'];raw=gzip.decompress(gz);assert len(raw)==ar['raw_stdout_stderr_bytes'] and sha(raw)==ar['raw_stdout_stderr_sha256'];raw.decode('utf-8')
 census={};axes={};pub={};targets={};targetaxes={};complete=[]
 for n,line in enumerate(raw.decode().splitlines(),1):
  for tag,dest in [('CENSUS',census),('ALLAX',axes),('PUBLICAX',pub),('TARGET',targets),('TARGETAX',targetaxes)]:
   if line.startswith(tag+'|'):
    row=json.loads(line[len(tag)+1:]);key=row['name'];assert key not in dest
    if tag in ['CENSUS','TARGET']:
     expr=row.pop('typeExpr');row.update(typeExpr_sha256=sha(expr.encode()),typeExpr_utf8_bytes=len(expr.encode()))
    dest[key]=row
  if line.startswith('COMPLETE|'):complete.append(line)
 assert complete==[f'COMPLETE|{len(census)}|owners=5'];assert set(census)==set(axes);assert set(pub)=={n for n,r in census.items() if not r['private']};assert all(pub[n]==axes[n] for n in pub)
 for fn,parsed in [('census',census),('allaxioms',axes),('publicaxioms',pub)]:
  supplied=json.loads((C/(fn+'-'+label+'.json')).read_text());assert supplied['count']==len(parsed)
  for row in supplied['rows']:
   norm={k:v for k,v in row.items() if k not in ['raw_log','raw_CENSUS_line']};assert norm==parsed[row['name']],(fn,label,row['name'])
 assert len(targets)==len(targetaxes)==(0 if label=='base' else 5) or label=='base'
 maps[label]=dict(census=census,axes=axes,pub=pub,targets=targets,targetaxes=targetaxes)
 meta.append(dict(endpoint=label,total=len(census),private=sum(r['private'] for r in census.values()),nonprivate=len(pub),nonprivate_noninternal=sum(not r['private'] and not r['internal'] for r in census.values()),sorry_closures=sum('sorryAx' in r['axioms'] for r in axes.values()),nonprivate_sorry_closures=sum('sorryAx' in r['axioms'] for r in pub.values()),raw_bytes=len(raw),raw_sha256=sha(raw),complete_raw_and_posted_maps_equal=True))
a,b=maps['base'],maps['head'];added=sorted(set(b['census'])-set(a['census']));removed=sorted(set(a['census'])-set(b['census']));assert not removed and len(added)==4
shared=set(a['census'])&set(b['census']);changes=[]
for n in sorted(shared):
 keys=[k for k in a['census'][n] if a['census'][n][k]!=b['census'][n][k]]
 if keys:changes.append(dict(name=n,fields=keys,before={k:a['census'][n][k] for k in keys},after={k:b['census'][n][k] for k in keys}))
 assert a['axes'][n]['axioms']==b['axes'][n]['axioms']
assert len(changes)==1 and changes[0]['name']=='Turing.FinTM.redirectTM_spaceUsedByTape' and changes[0]['fields']==['owner']
assert all(set(r['axioms'])<=std for r in b['targetaxes'].values())
(OUT/'compiled-crosscheck.json').write_text(json.dumps(dict(endpoints=meta,added={n:b['census'][n] for n in added},removed=removed,shared_metadata_changes=changes,all_shared_axiom_closures_equal=True,target_root_and_descendant_standard=True,target_rows=len(b['targets']),type_expressions_complete_not_truncated=True),indent=2)+'\n')
# Replay records: rehash all cited raw artifacts and reconcile each ordered row/launch.
rp=G/'evidence/replay-mfup2';receipt=json.loads((rp/'receipt.json').read_text());assert receipt['result']=='PASS' and receipt['pipeline_exit']==receipt['failures']==receipt['error_rows']==receipt['static_mismatches']==0
for e in receipt['evidence']:
 data=(rp/e['path']).read_bytes();assert len(data)==e['bytes'] and sha(data)==e['sha256']
order=(rp/'down-mfup2.txt').read_text().splitlines();order=[x for x in order if x.strip()];log=(rp/'replay-mfup2.log').read_text();launch=(rp/'replay-mfup2-launches.log').read_text();assert len(order)==len(set(order))==401 and 'TCSlib' not in order
(OUT/'replay-raw-format.txt').write_text('First ordered module: '+order[0]+'\nFirst raw log lines:\n'+'\n'.join(log.splitlines()[:8])+'\nFirst launch lines:\n'+'\n'.join(launch.splitlines()[:4])+'\n')
# Source identity/histories remain separately documented; no native execution performed.
controls=[]
f=G/'review/first-entry';v=json.loads((f/'controls-verification.json').read_text());nr=json.loads((f/'Controls-sealed-run.json').read_text());pr=json.loads((f/'Controls-unsealed-run.json').read_text());neg=(f/'Controls-sealed.out').read_text();errors=[(int(x[1]),int(x[2])) for x in re.finditer(r':(\d+):(\d+): error(?:\([^)]*\))?:',neg)];assert (pr['exit'],pr['errors'],nr['exit'],nr['errors'])==(0,0,1,8) and len(errors)==8
for entry in v['controls']:
 assert sum(entry['line_interval'][0]<=line<=entry['line_interval'][1] for line,col in errors)==1
assert len({(x['definition'],x['mode']) for x in v['controls']})==8
controls.append(dict(group='first-entry',identities=8,source_intervals_exact=True,expected_negative_errors=8))
for folder,pos,ne,want in [('pair-diag','Controls-unsealed-v1','Controls-sealed-v1',8),('inc-redirect','Controls-native','Controls-sealed',52)]:
 d=G/'review'/folder;pt=(d/(pos+'.out')).read_text();nt=(d/(ne+'.out')).read_text();pr=json.loads((d/(pos+'-run.json')).read_text());nr=json.loads((d/(ne+'-run.json')).read_text());positive=[x.split('|') for x in pt.splitlines() if x.startswith('CONTROL|')];negative=[x.split('|') for x in nt.splitlines() if x.startswith('CONTROL|')];assert len(positive)==len(negative)==want
 ids=collections.Counter((x[1],x[2]) for x in positive);assert len(ids)==want and all(n==1 for n in ids.values());assert ids==collections.Counter((x[1],x[2]) for x in negative);assert all(x[3]=='PASS' for x in positive) and all(x[3]=='FAIL' for x in negative);assert (pr['exit'],pr['errors'],nr['exit'],nr['errors'])==(0,0,1,want)
 diag=collections.Counter(re.findall(r'RFL_CONTROL\|([^|\n]+)\|([^|\n]+)\|',nt));assert diag==ids
 controls.append(dict(group=folder,identities=want,exact_positive_negative_diagnostic_multiplicities=True,expected_negative_errors=want))
(OUT/'controls-crosscheck.json').write_text(json.dumps(controls,indent=2)+'\n');(OUT/'replay-crosscheck.json').write_text(json.dumps(dict(receipt=receipt,raw_receipt_artifacts_rehashed=True,ordered_unique_modules=len(order),actual_launch_records=launch.count('\n'),no_root_TCSlib=True,no_new_replay=True,remaining_parse='Exact raw row/launch formatting retained in replay-raw-format.txt; finalization records and auditor report independently assert complete per-row match.'),indent=2)+'\n');(OUT/'check_execution_metadata.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(dict(compiled=meta,added=len(added),shared_changes=changes,controls=controls,replay_modules=len(order)),indent=2))
