import pathlib,subprocess,json,re,hashlib,collections,zipfile,gzip
R=pathlib.Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');O=pathlib.Path(__file__).parent;G=R/'campaign/gates/118-mig1-landing';L=R/'campaign/fills/mig1/landing'
X='15dde3b91c9e6cbfefba6e11ea44545a42125068';F='arora-barak-ch3-4/outbox/gates/118-mig1-landing-gate/'
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(pathlib.Path(p).read_text())
def save(n,d):(O/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
problems=[]
def ck(n,v):
 if not v:problems.append(n)
 return v
index=json.loads(git('show',X+':'+F+'INPUT-INDEX.json'));pub=j(G/'publication.json');parts=[];json_count=0
blobs={}
for pin in set(e['pin'] for e in index['entries']):
 blobs[pin]={}
 for line in git('ls-tree','-r',pin).decode().splitlines():
  meta,p=line.split('\t',1);blobs[pin][p]=meta.split()[2]
for part in index['parts']:
 data=git('show',X+':'+F+part['file']);entries=[e for e in index['entries'] if e['part']==part['part']];off=0;bad=[]
 for e in entries:
  header=('## ===== '+e['path']+' =====\n\n').encode();raw=data[off+len(header):off+len(header)+e['raw_bytes']];section=data[off:off+len(header)+e['raw_bytes']]
  ok=data[off:off+len(header)]==header and sha(raw)==e['raw_sha256'] and sha(section)==e['section_sha256'] and blobs[e['pin']].get(e['path'])==e['blob']
  if not ok:bad.append(e['path'])
  if e['path'].endswith('.json'):
   json.loads(raw);json_count+=1
  off+=len(header)+e['raw_bytes']
  # A separator newline follows every rendered complete section.
  ck('section separator '+e['path'],data[off:off+1]==b'\n');off+=1
 row={'part':part['part'],'file':part['file'],'bytes':len(data),'sha256':sha(data),'sections':len(entries),'all_payload_hashes_section_hashes_and_Git_blobs_exact':not bad,'mismatches':bad,'entire_part_consumed':off==len(data)}
 ck('part '+str(part['part']),not bad and row['bytes']==part['bytes'] and row['sha256']==part['sha256'] and row['sections']==part['sections'] and off==len(data));parts.append(row)
# Final indices are authoritative; preparatory status/hash records are historical.
packet={'source':index['source'],'records':index['records'],'exchange':X,'parts':parts,'physical_sections':len(index['entries']),'physical_JSON_parsed':json_count,'physical_Git_pin_counts':dict(collections.Counter(e['pin'] for e in index['entries'])),'all25_root_sources_source_bound':sum(e['path'].startswith('TCSlib/') and e['pin']==index['source'] for e in index['entries'])==25,'problems':list(problems)}
ck('packet JSON1316',json_count==1316);save('packet-checks.json',packet)
print(json.dumps({'stage':'packet','parts':parts,'JSON':json_count,'problems':problems},indent=2))
# Controls: actual logs and paired source input equivalence, without rerunning Lean.
cs=L/'post234-consumer-seals';strict=j(cs/'evidence/strict-control-checks.json');control=j(cs/'evidence/control-checks.json');rows=[]
for row in control['runs'][::2]:
 label=row['label'];seal_label=control['runs'][control['runs'].index(row)+1]['label'];owner=label.split('-')[1];N=row['expected']
 nat=(cs/'evidence/runs'/(label+'.out')).read_text();seal=(cs/'evidence/runs'/(seal_label+'.out')).read_text()
 passed=re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|PASS\|kernelChecked=([^\n]+)$',nat,re.M);failed=re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|FAIL$',seal,re.M);diagnostics=re.findall(r'error: RFL_CONTROL\|([^|]+)\|([^|]+)\|',seal)
 def sourcepath(label):return cs/'evidence/project'/(label.replace('-','_')+'.lean.txt')
 ns=sourcepath(label).read_text();ss=sourcepath(seal_label).read_text();ss_unsealed=re.sub(r'^attribute \[local irreducible\][^\n]*\n','',ss,flags=re.M)
 nr=j(cs/'evidence/runs'/(label+'-run.json'));sr=j(cs/'evidence/runs'/(seal_label+'-run.json'))
 r={'owner':owner,'expected':N,'native_PASS_kernel_identities':len(passed),'sealed_FAIL_identities':len(failed),'matching_rfl_diagnostics':len(diagnostics),'ordered_pairs_exact':[(d,m) for d,m,k in passed]==failed==diagnostics,'all_kernel_names_unique':len({k for d,m,k in passed})==N,'only_guard_line_differs':ns==ss_unsealed,'recorded_native_exit':nr['exit'],'recorded_sealed_exit':sr['exit'],'native_rawhash_exact':sha(nat.encode())==nr['output_sha256'],'sealed_rawhash_exact':sha(seal.encode())==sr['output_sha256']}
 ck('controls '+owner,len(passed)==len(failed)==len(diagnostics)==N and r['ordered_pairs_exact'] and r['all_kernel_names_unique'] and r['only_guard_line_differs'] and nr['exit']==0 and sr['exit']==1 and r['native_rawhash_exact'] and r['sealed_rawhash_exact']);rows.append(r)
core=L/'post234-core-reader-repair';n=(core/'evidence/runs/Controls-Loop-native.out').read_text();s=(core/'evidence/runs/Controls-Loop-sealed.out').read_text();np=re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|PASS\|kernelChecked=([^\n]+)$',n,re.M);sf=re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|FAIL$',s,re.M);sd=re.findall(r'error: RFL_CONTROL\|([^|]+)\|([^|]+)\|',s)
corecheck={'native':len(np),'sealed':len(sf),'rfl_diagnostics':len(sd),'all_ordered_pairs_exact':[(d,m) for d,m,k in np]==sf==sd,'QA_guards':j(core/'QA.json')['guard_profiles'],'actual_Loop_source_matches_proposal':(core/'Loop.proposed.lean.txt').read_bytes()==git('show',index['source']+':TCSlib/Complexity/TuringMachine/Build/Loop.lean')}
ck('core40',len(np)==len(sf)==len(sd)==40 and corecheck['all_ordered_pairs_exact'] and corecheck['actual_Loop_source_matches_proposal'])
checks={'recorded_owner_context_guards':strict['owner_context_guard_occurrences'],'recorded_unique_ordinary_definitions':strict['unique_definitions'],'paired_rows_independently_reconciled':sum(r['expected'] for r in rows),'rows':rows,'corruption_tests_retained':strict['corruption_tests'],'final_Core_Loop_controls':corecheck,'problems':list(problems)};save('control-checks.json',checks);print(json.dumps({'stage':'controls','pairs':checks['paired_rows_independently_reconciled'],'core':corecheck,'problems':problems},indent=2))
# Reconcile every numerical screen row and classification; numerical comparison is not semantic absence.
ss=L/'post234-source-screen';b=j(ss/'base-candidates.json');h=j(ss/'head-candidates.json');cls=j(ss/'all-HEAD-candidate-classification.json');dc=j(ss/'current-delta-classification.json')
def key(d):return (d['a'],d['b'])
bm={key(d):d for d in b};hm={key(d):d for d in h};new=set(hm)-set(bm);gone=set(bm)-set(hm);changed={k for k in bm.keys()&hm.keys() if bm[k]!=hm[k]}
sc={'BASE_rows':len(b),'HEAD_rows':len(h),'BASE_shared_chars':sum(d['shared'] for d in b),'HEAD_shared_chars':sum(d['shared'] for d in h),'new':len(new),'gone':len(gone),'changed':len(changed),'classifications':len(cls['rows']),'all_HEAD_rows_exactly_classified':collections.Counter(json.dumps(x['row'],sort_keys=True) for x in cls['rows'])==collections.Counter(json.dumps(x,sort_keys=True) for x in h),'all_delta_classification_counts_exact':len(dc['new'])==len(new) and len(dc['gone'])==len(gone) and len(dc['changed'])==len(changed),'style_recorded_exit':[j(ss/'style-base-run.json')['exit'],j(ss/'style-head-run.json')['exit']],'source_semantic_limit':'No new canonical screen/lint execution or global absence/cumulative debt proof inferred.'}
ck('screen numeric/classification',sc['BASE_rows']==1702 and sc['HEAD_rows']==615 and sc['BASE_shared_chars']==658088 and sc['HEAD_shared_chars']==194067 and sc['new']==58 and sc['gone']==1145 and sc['changed']==30 and sc['all_HEAD_rows_exactly_classified'] and sc['all_delta_classification_counts_exact'] and sc['style_recorded_exit']==[1,1]);sc['problems']=list(problems);save('screen-checks.json',sc)
# Original delivery archives: read inert bytes and checksum ledgers, never extract or execute.
zips=[]
for p in sorted((R/'campaign/fills/mig1').rglob('*.zip')):
 with zipfile.ZipFile(p) as z:
  sums=[n for n in z.namelist() if n.split('/')[-1] in ['SHA256SUMS','SHA256SUMS.txt']];bad=[];count=0
  for sp in sums:
   prefix=sp.rsplit('/',1)[0]+'/'
   for ln in z.read(sp).decode().splitlines():
    if not ln:continue
    expected,rel=ln.split(maxsplit=1);rel=rel.lstrip('*');rel=rel[2:] if rel.startswith('./') else rel;data=z.read(prefix+rel);count+=1
    if sha(data)!=expected:bad.append(rel)
  ck('delivery ZIP '+p.name,not bad)
  zips.append({'path':str(p.relative_to(R)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes()),'archive_members_including_directories':len(z.infolist()),'checksummed_payload_entries':count,'mismatches':bad})
ck('seven ZIPs',len(zips)==7);save('delivery-archive-checks.json',{'archives':zips,'note':'2,152 R1 and4,028 R2 are checksummed payload entries, not directory-inclusive ZIP member counts. No files extracted/executed.','problems':list(problems)})
print(json.dumps({'stage':'screens/delivery','screen':sc,'zip_payload_counts':[(x['path'].split('/')[-1],x['checksummed_payload_entries']) for x in zips],'problems':problems},indent=2))
save('PACKET-CONTROL-SUMMARY.json',{'PASS':not problems,'problems':problems,'execution':'Own read-only isolated Python checks only; all Lean outputs are supplied historical executions.'})
