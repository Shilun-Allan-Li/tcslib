from pathlib import Path,PurePosixPath
import hashlib,json,re,difflib
B=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/cleanup-part2-prep')
O=B/'issue-release-review-r1'
sha=lambda b:hashlib.sha256(b).hexdigest()
def strict(path):
 def pairs(kv):
  d={}
  for k,v in kv:
   assert k not in d,(str(path),'duplicate key',k)
   d[k]=v
  return d
 return json.loads(path.read_text(),object_pairs_hook=pairs)
def safe(p):
 q=PurePosixPath(p)
 assert p and not q.is_absolute() and '..' not in q.parts and str(q)==p
 assert '\\' not in p and '\n' not in p and '\r' not in p
 return p
def rows(root,j):
 paths=[]
 for r in j['files']:
  n=safe(r['path']);paths.append(n);p=root/n
  assert p.is_file() and not p.is_symlink()
  b=p.read_bytes();assert (len(b),sha(b))==(r['bytes'],r['sha256']),(str(p),'hash/bytes')
 assert len(paths)==len(set(paths))==len({p.casefold() for p in paths})
 return set(paths)
def pack(name,mh,sh):
 P=B/name
 assert sha((P/'PACK-MANIFEST.json').read_bytes())==mh
 assert sha((P/'SHA256SUMS').read_bytes())==sh
 J=strict(P/'PACK-MANIFEST.json')
 assert J['ancestor']=='1aa5506f58f77c215e56d24311ec33bd931cacf1' and J['worker']=='Claude'
 actual={}
 for p in P.rglob('*'):
  assert not p.is_symlink(),str(p)
  if p.is_file():actual[safe(p.relative_to(P).as_posix())]=p.read_bytes()
 assert len(actual)==299 and len({p.casefold() for p in actual})==299
 ms=rows(P,J);assert len(ms)==297 and ms|{'PACK-MANIFEST.json','SHA256SUMS'}==set(actual)
 assert not ms&{'PACK-MANIFEST.json','SHA256SUMS'}
 sums={}
 for line in (P/'SHA256SUMS').read_text().splitlines():
  z=re.fullmatch(r'([a-f0-9]{64})  (.+)',line);assert z
  h,p=z.groups();safe(p);assert p not in sums and sha(actual[p])==h;sums[p]=h
 assert len(sums)==298 and set(sums)==set(actual)-{'SHA256SUMS'}
 return P,actual,{'manifest_sha256':mh,'sha256sums_sha256':sh,'files':299,'bytes':sum(map(len,actual.values())),'manifest_leaves':297,'checksum_rows':298,'safe_unique_contained_paths':True,'no_symlinks':True,'all_hashes_match':True}
P,a,v=pack('issue-pack-r1','f5fcea533fa3e11688c4f9944b9912dfc4e5a1ae0e1491454f0d253bb42ec70d','a289a58e622137c77554ba529424f5a9290f73658189402a348b544b1c9624c1')
assert v['bytes']==17732120
I=P/'inputs';J=strict(I/'DELIVERY-MANIFEST.json')
assert sha((I/'DELIVERY-MANIFEST.json').read_bytes())=='994c8dc040cee2d4af24f20bcbe92b371e8a716ae041ccefe0f225980f51e168'
assert sha((I/'INPUTS-MANIFEST.json').read_bytes())=='31252c0581393430bac7114751383e22ddab0cc63cbdba1af3da09b648218fb5'
ls=rows(I,J);assert len(ls)==45
actualinputs={p.relative_to(I).as_posix() for p in I.rglob('*') if p.is_file()}
assert actualinputs==ls|{'DELIVERY-MANIFEST.json'}
for n in actualinputs:assert (I/n).read_bytes()==(B/'issue-inputs-r1'/n).read_bytes()
role=strict(I/'role-manifest.json');assert role['ancestor']==J['ancestor'] and role['new_modules_permitted'] is False
sets={k:{r['path'] for r in role['roles'] if r['role']==k} for k in ['CONSUMER','PROVIDER_ONLY','CHECK_ONLY']}
assert [len(sets[k]) for k in sets]==[97,124,2]
assert sets['CONSUMER'].isdisjoint(sets['PROVIDER_ONLY']) and len(sets['CONSUMER']|sets['PROVIDER_ONLY'])==221
assert set((I/'owned-files.txt').read_text().splitlines())==sets['CONSUMER']|sets['PROVIDER_ONLY']
assert sets['CHECK_ONLY']=={'TCSlib.lean','audits/pass-shelat/Checks.lean'}
assert len(strict(I/'observations/canonical-work-units.json'))==509
named=strict(I/'scope/named-targets.json');assert len(named['baseline_named_targets'])==89 and len(named['future_move_or_promote_targets'])==4
assert len(strict(I/'public-definition-freeze.json'))==3
binding=[]
for path,manifest,pin in [('external-bootstrap-r1','DELIVERY-MANIFEST.json','70dd1a408a2c0c46af7ab2da50ff50520b26b2983e298492935008debb1a2cbd'),('environment-tools','MANIFEST.json','400064239a21121755fa5791c6d66c9776be5d13abeb2c7f99a4d327e01e6cf8'),('preship/interface','MANIFEST.json',None)]:
 root=P/path;m=root/manifest
 if pin:assert sha(m.read_bytes())==pin
 ns=rows(root,strict(m));binding.append({'manifest':path+'/'+manifest,'sha256':sha(m.read_bytes()),'verified_leaf_rows':len(ns)})
static=strict(P/'external-bootstrap-r1/DELIVERY-MANIFEST.json');assert static['native_execution'] is False
assert static['counts']=={'PFR_modules':31,'LeanAPAP_modules':0,'Mathlib_direct_roots':30,'extra_roots':14,'full_union_roots':389}
old=set((I/'mathlib/all-needed-union-roots.txt').read_text().splitlines())
bound=set((P/'external-bootstrap-r1/mathlib-direct-roots.txt').read_text().splitlines())
full=set((P/'external-bootstrap-r1/mathlib-full-union-roots.txt').read_text().splitlines())
assert len(old)==375 and len(bound)==30 and len(full)==389 and len(bound-old)==14 and full==old|bound
pfr=strict(P/'preship/pfr/STATUS.json');assert pfr['native_success_claimed'] is False and pfr['cache_get_started'] is False and pfr['pfr_native_checks_started']==0 and pfr['import_owner_probe_started'] is False
assert len(pfr['attempts'])==3 and all(x['return_code']==75 for x in pfr['attempts'])
sg=strict(P/'reviews/adapter-guards/SUMMARY.json');assert sg['cases']==sg['expectations_met']==25 and sg['no_olean_products'] is True
assert sg['portable_tool_sha256']=={n:sha((P/'environment-tools'/n).read_bytes()) for n in ['prepare_pfr.py','pfr_lean.py']}
assert sg['portable_tool_sha256']=={'prepare_pfr.py':'650edf1d270d5e130a926a5840fead75ba9888e12684f2f38451af91ad769b8f','pfr_lean.py':'41fda9565be3f77462fe6f2f7b55b798c5bf34fbbc400a648f77e000eb36636d'}
rbook=(P/'environment-tools/RUNBOOK.md').read_text()
assert sha(rbook.encode())=='4102e174171f787bbc56ec497140b6a3272937ff1fc0ad23a25f5c2783fc6f55'
assert 'never export\nthe adapter PATH globally' in rbook and 'namespace/owner probe must **not** use the adapter' in rbook
meta=strict(P/'reviews/adapter-guards/REVIEW-METADATA.json');assert meta['runbook_sha256_at_review']==sha(rbook.encode()) and meta['simulation_only'] is True
interface1=strict(P/'preship/interface/attempt-1/InterfaceProbe.json');interface2=strict(P/'preship/interface/attempt-2/InterfaceProbe.json')
assert interface1['return_code']!=0 and interface1['fresh_nonempty_object'] is False
assert interface2['return_code']==0 and interface2['error_diagnostics']==0 and interface2['fresh_nonempty_object'] is True
assert interface2['source_sha256']==sha((P/'preship/interface/attempt-2/InterfaceProbe.source.txt').read_bytes())
b=(P/'brief.md').read_text();e=(P/'public-exceptions.md').read_text();db=(B/'issue-draft-r2/brief.md').read_text();de=(B/'issue-draft-r2/public-exceptions.md').read_text()
assert b.split('## Work packages',1)[1].split('## Environment and serial checking',1)[0]==db.split('## Work packages',1)[1].split('## Environment and serial checking',1)[0]
assert e.split('## General freeze and representation discipline',1)[1].rsplit('**Ready to dispatch',1)[0]==de.split('## General freeze and representation discipline',1)[1].rsplit('**Not yet clear to merge',1)[0]
assert re.findall(r'```lean\n.*?\n```',e,re.S)==re.findall(r'```lean\n.*?\n```',de,re.S)
assert 'PENDING_ROOT' not in b and 'ISSUE CANDIDATE' not in b
for phrase in ['No worker subagents','inbox/fills/cleanup-part2/','Do not fill baseline sorries','Complete final delivery requires both full final aggregate roots','SimulatorMachine must not import ColZKMachine.','even if PR #232 has a counterpart','no maintainer native PFR/owner-identity pass']:
 assert phrase in b,phrase
assert 'only for the 31 PFR module checks' in b
keys=['ANCESTOR.txt','README.md','brief.md','public-exceptions.md','fill-environment-addendum.md','inputs/DELIVERY-MANIFEST.json','inputs/INPUTS-MANIFEST.json','environment-tools/MANIFEST.json','environment-tools/RUNBOOK.md','environment-tools/prepare_pfr.py','environment-tools/pfr_lean.py','environment-tools/PFRIdentityProbe.source.txt','external-bootstrap-r1/DELIVERY-MANIFEST.json','preship/pfr/STATUS.json','preship/interface/MANIFEST.json','reviews/adapter-guards/SUMMARY.json']
validation={'status':'INDEPENDENT_BOUNDED_RELEASE_BYTE_VALIDATION_R1','own_validator_sha256':sha(Path(__file__).read_bytes()),'pack':v,'key_files':{n:{'bytes':len(a[n]),'sha256':sha(a[n])} for n in keys},'frozen_inputs':{'leaf_files':45,'actual_files_with_delivery_manifest':46,'all_bytes_equal_originals':True},'binding_manifests':binding,'scope':{'ancestor':J['ancestor'],'editable':221,'consumers':97,'providers_reader_only':124,'check_only':2,'observations':509,'named_rows':89,'future_targets':4,'special_definition_baselines':3,'work_package_text_equal_r2':True,'exception_permission_body_equal_r2':True,'all5_Lean_headers_equal_r2':True},'environment':{'PFR_native_status':'DEFERRED/NOT_RUN','worker_checkpoint0_required':True,'ordinary_PATH_for_local_and_probes':True,'static_PFR_sources':31,'Mathlib_boundary':30,'old_local_roots':375,'extra_roots':14,'full_union':389,'read_historical_guard_expectations_met':25,'guard_tests_rerun_by_this_reviewer':False,'selected_interface_historical_rc':0},'limits':['No supplied program, Lean/native/cache/build/app executed. Own file/hash/data checks only.','Frozen26-group source/input validation was not rerun; exact immutable input bytes and prior review pins preserved.','Control fixtures contain intentional invalid manifests as data; operative manifests verified separately.','No source/pack/main/exchange/Git mutation.']}
findings=[{'id':'R1-01','severity':'minor','path':'brief.md','line':91,'text':'Sampling.two_pow_size_le_two_mul should use exact TCSlib.Cryptography.two_pow_size_le_two_mul plus file label.'},{'id':'R1-02','severity':'minor','path':'brief.md','line':101,'text':'Sampling.abs_uexp_sub_le should use exact TCSlib.Cryptography.abs_uexp_sub_le plus file label.'}]
assert '`Sampling.two_pow_size_le_two_mul`' in b and 'public Sampling.abs_uexp_sub_le.' in b
review={'status':'INITIAL_R1_REVIEW_FROZEN','severity_counts':{'blockers':0,'majors':0,'minors':2},'verdict':'Correct two namespace wording minors before release; no other material release defect identified.','findings':findings,'source_ancestor':J['ancestor'],'pack':v,'key_files':validation['key_files'],'PFR_native_status':'NOT_RUN/host-deferred; worker checkpoint0 required','validation_sha256_pending':'external review checksums bind final outputs','limitations':validation['limits']}
for name,obj in [('validation.json',validation),('review.json',review)]:
 p=O/name;assert not p.exists(),str(p);p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
# Lightweight companion: same299 paths, only brief/two packaging hashes differ.
Q,c,w=pack('issue-pack-r2','d92d26e52991013640d36646678557178fe20362cd676be44f45af091dd5d91a','078baef661c1152179603b7f1495000fc7287c47164f6fc06baf7b7c855c3e37')
assert set(a)==set(c)
changed=sorted(n for n in a if a[n]!=c[n]);assert changed==['PACK-MANIFEST.json','SHA256SUMS','brief.md']
expected=b.replace('`Sampling.two_pow_size_le_two_mul`','`TCSlib.Cryptography.two_pow_size_le_two_mul` (in `Asymptotic/Sampling.lean`)').replace('public Sampling.abs_uexp_sub_le.','public `TCSlib.Cryptography.abs_uexp_sub_le` in `Asymptotic/Sampling.lean`.')
assert c['brief.md']==expected.encode() and sha(c['brief.md'])=='143dd9500fc79bc00ed6d5adbbcffe1cc009ae9064ecf2664bd73b182e4bc61d'
changedlines=[i+1 for i,(x,y) in enumerate(zip(b.splitlines(),expected.splitlines())) if x!=y];assert changedlines==[91,101]
companion={'status':'FINAL_INTERNAL_PACK_R2_REVIEW_COMPLETE','severity_counts':{'blockers':0,'majors':0,'minors':0},'verdict':'Ready for records/exchange release and user dispatch; not worker completion or merge clearance.','canonical_external_issue':'issued-r1; internal packet revision2 only','source_ancestor':J['ancestor'],'pack':w,'original_r1_pack':v,'initial_review_sha256':sha((O/'review.json').read_bytes()),'final_brief_sha256':sha(c['brief.md']),'changed_paths':changed,'changed_brief_lines':changedlines,'other296_files_byte_identical':True,'same299_paths':True,'both_r1_findings_resolved_by_exact_replacement':True,'data_tool_guard_native_work_repeated':False,'PFR_native_status':'NOT_RUN/host-deferred; worker checkpoint0 mandatory','limitations':validation['limits']}
for name,obj in [('revision2-validation.json',companion),('finalrelease.json',companion)]:
 p=O/name;assert not p.exists(),str(p);p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
assert all((P/n).read_bytes()==bb for n,bb in a.items()) and all((Q/n).read_bytes()==bb for n,bb in c.items())
print(json.dumps({'r1_files':v['files'],'r1_bytes':v['bytes'],'r2_files':w['files'],'r2_bytes':w['bytes'],'r1_findings':'0B/0M/2wording minors','r2_findings':'0B/0M/0minor','changed_paths':changed,'unchanged_files':296,'frozen_input_files':46,'no_supplied_or_native_execution':True}))
