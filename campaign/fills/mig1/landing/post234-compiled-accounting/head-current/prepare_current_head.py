from pathlib import Path
import json,hashlib,subprocess,tempfile,os,datetime
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch');P=Path('/private/tmp/mig-post234-final-head-accounting');B=R/'campaign/fills/mig1/landing/post234-compiled-accounting/baseline-current';N=R/'campaign/fills/mig1/landing/post234-native3';Q=R/'campaign/fills/mig1/landing/post234-source-QA-final'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
base='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c';head='eaecd6b2afd992ead0844fa5f351eaf143fd1d1c'
for rev in [base,head]:assert git('rev-parse',rev).decode().strip()==rev;subprocess.run(['git','cat-file','-e',rev+'^{commit}'],cwd=R,check=True)
mb=(B/'BASELINE-MANIFEST.json').read_bytes();assert sha(mb)=='3c1a508ba5f2d62d8f45a27b86bcfa285bf748b0fdaf725a256994506f23f84f'
for r in json.loads(mb)['files']:
 b=(B/r['path']).read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256'])
save('baseline-frozen-inputs.json',[{'path':str(q.relative_to(B)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(B.rglob('*'))if q.is_file()])
nb=(N/'MANIFEST.json').read_bytes();nm=json.loads(nb)
for r in nm:
 b=(N/r['path']).read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256'])
nr=json.loads((N/'receipt.json').read_text());assert nr['result']=='PASS'and nr['head']==head and nr['modules']==12 and nr['errors']==0 and nr['sorries']==3 and nr['objects']==895 and nr['whole_MAC5_input']and nr['input_unchanged']and nr['all_outside_owner_scope_exact']and nr['effective_j4_launches']==12
ns=json.loads((N/'snapshot-objects.json').read_text());maps={}
for side,tree in [('Base',S/'oleans-mac5'),('Head',S/'oleans-mig-post234-native3')]:
 m={str(q.relative_to(tree)):{'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(tree.rglob('*.olean'))};assert len(m)==895 and m==ns['input'if side=='Base'else'output'];save('snapshot-'+side.lower()+'-before.json',m);maps[side]=m
assert maps['Base']==json.loads((B/'snapshot-base-before.json').read_text())
oldctx=json.loads((B/'preparation.json').read_text());primary=oldctx['primary_owners'];context=oldctx['context_owners'];assert len(primary)==12 and context==['TCSlib.Complexity.TuringMachine.Finite'];pins=[]
for owner in primary+context:
 path=owner.replace('.','/')+'.lean';b=git('show',head+':'+path);d=P/'source-captures/Head'/(path+'.txt');d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b);pins.append({'path':path,'owner':owner,'source':head,'git_blob':git('rev-parse',head+':'+path).decode().strip(),'bytes':len(b),'sha256':sha(b)})
for r in nr['rows']:
 assert r['source_sha256']==next(q['sha256']for q in pins if q['path']==r['file']);raw=(N/r['log']).read_bytes();assert len(raw)==r['bytes']and sha(raw)==r['sha256']and r['exit']==r['errors']==0
project=Path(tempfile.mkdtemp(prefix='tcslib-mig-final-head-'));(project/'lean-toolchain').write_text('leanprover/lean4:v4.25.0\n');(project/'.lake').mkdir();os.symlink(oldctx['packages'],project/'.lake/packages');probes=[]
for src,name in [('Inventory.lean.txt','Head-inventory'),('Metadata-ciattrs.lean.txt','Head-ciattrs')]:
 b=(B/src).read_bytes();(P/src).write_bytes(b);(project/(name+'.lean')).write_bytes(b);probes.append({'name':name,'side':'Head','project_file':name+'.lean','evidence_file':src})
ctx={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':base,'source':head,'primary_owners':primary,'context_owners':context,'project':str(project),'toolchain':'leanprover/lean4:v4.25.0','packages':oldctx['packages'],'wrapper':oldctx['wrapper'],'wrapper_sha256':oldctx['wrapper_sha256'],'snapshots':[{'side':'Base','path':str(S/'oleans-mac5'),'object_count':895},{'side':'Head','path':str(S/'oleans-mig-post234-native3'),'object_count':895}],'baseline_frozen_folder':str(B),'baseline_manifest_sha256':sha(mb),'native3_frozen_folder':str(N),'native3_manifest_sha256':sha(nb),'native3_actual12_not_full_replay':True,'root_authorized_actual_NATIVE3_PASS_relay_received':True,'no_unfinished_MMIG3_snapshot_read':True,'all_source12_native_receipt_hashes_exact_Git_HEAD':True,'all_baseline66_files_verified_before_reuse':True,'fresh_HEAD_trusted_probes_byte_exact_frozen_BASE':True,'no_theorem_proof_value_rendering':True,'one_Lean_at_a_time':True,'local_slots':3,'machine_cap':5}
assert sha(Path(ctx['wrapper']).read_bytes())==ctx['wrapper_sha256'];save('context.json',ctx);save('source-pins.json',pins);save('metadata-jobs.json',probes)
runner=Path('/private/tmp/g106-r4-compiled-and-seals/run_jobs.py').read_text();assert runner.count("P=Path('/private/tmp/g106-r4-compiled-and-seals')")==1;runner=runner.replace("P=Path('/private/tmp/g106-r4-compiled-and-seals')","P=Path('/private/tmp/mig-post234-final-head-accounting')");(P/'run_jobs.py').write_text(runner)
qfiles=['proof-roots-current.json','proof-root-progression.json','B1-to-HEAD.json','approved-private-header-exceptions.json','current-derived-public-private-counts.json','runtime-import-admission-freeze.json']
for n in qfiles:
 d=P/'source-QA-data'/n;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes((Q/n).read_bytes())
save('source-QA-data-pins.json',[{'path':str((Q/n).relative_to(R)),'bytes':(Q/n).stat().st_size,'sha256':sha((Q/n).read_bytes()),'used_as_data_not_executed':True}for n in qfiles])
print(json.dumps({k:v for k,v in ctx.items()if k not in ['primary_owners','snapshots']},indent=2))
