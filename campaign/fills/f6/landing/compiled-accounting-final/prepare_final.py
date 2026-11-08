from pathlib import Path
import os,json,hashlib,base64,gzip,subprocess,tempfile,datetime,difflib
O=Path('/private/tmp/f6-compiled-accounting-final');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/fills/f6/landing/compiled-accounting';S=Path(os.environ['TCSLIB_SCRATCH']);WT=S/'wt-f6';REL='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean';H='0d0950caeb39300b5cc9bf41e5f07392fb26d3e5';OLD='f72a807e2376a2b986675c992745d6affc23b96f';B='3023dc1408c3d216fc07a7cbba9ae30135b861ed'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(WT),*a])
pins={}
for pin in [H,OLD,B]:
 full=git('rev-parse',pin+'^{commit}').decode().strip();git('cat-file','-e',full+'^{commit}');assert full==pin;pins[pin]=full
assert git('rev-parse','HEAD').decode().strip()==H
assert git('rev-parse','@{upstream}').decode().strip()==H
assert git('status','--porcelain=v1','--untracked-files=no')==b''
source=(WT/REL).read_bytes();assert sha(source)=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3';assert source==git('show',H+':'+REL)
changed=git('diff','--name-only',OLD,H,'--','*.lean').decode().splitlines();assert changed==[REL]
previous=git('show',OLD+':'+REL);base=git('show',B+':'+REL)
assert sha(previous)=='8a44b4b35010ac116e34880269b80d1121d2fdd86166e62da75efeffc984c031'
assert sha(base)=='1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f'
assert previous==(R/'campaign/fills/f6/landing/native1/Hierarchy.lean.txt').read_bytes()
assert source==(R/'campaign/fills/f6/landing/seam-step-repoint-preflight/proposed-Hierarchy.lean.txt').read_bytes()
(O/'Hierarchy-head.lean.txt').write_bytes(source);(O/'Hierarchy-base.lean.txt').write_bytes(base);(O/'source-since-f72.diff').write_bytes(git('diff','--no-ext-diff',OLD,H,'--',REL))
# Hash every frozen original artifact; retain the whole inventory for a before/after immutability check.
freeze=[]
for p in sorted(P.iterdir()):
 assert p.is_file();raw=p.read_bytes();freeze.append({'path':p.name,'bytes':len(raw),'sha256':sha(raw)})
manifest=json.loads((P/'MANIFEST.json').read_bytes())
for f in manifest['files']:
 b=(P/f['path']).read_bytes();assert (len(b),sha(b))==(f['bytes'],f['sha256'])
for ln in (P/'SHA256SUMS').read_text().splitlines():
 h,n=ln.split(None,1);assert sha((P/n.lstrip('* ')).read_bytes())==h
(O/'frozen-original-before.json').write_text(json.dumps(freeze,indent=2)+'\n')
# The reviewed exact inventory probe prints types and metadata only, never theorem proof values.
probe=(P/'Inventory.lean.txt').read_bytes();assert sha(probe)=='327bd85f3af968914729d13f6efd121af9eaf4208a53027e44492d523d3237d8';assert probe==(P/'Inventory-base.lean.txt').read_bytes()==(P/'Inventory-head.lean.txt').read_bytes()
assert b'reprStr ci.type' in probe and b'reprStr ci.value' not in probe and b'valueExpr' not in probe and b'allowUnsafeReducibility' not in probe
for name in ['Inventory.lean.txt','Inventory-head.lean.txt','Inventory-base.lean.txt']:(O/name).write_bytes(probe)
ctx=json.loads((P/'context.json').read_bytes());basepin=next(x for x in ctx['snapshots_read_only'] if x['endpoint']=='base');br=json.loads((P/'Base-run.json').read_bytes());assert br['exit']==br['errors']==br['warnings']==0;assert br['input_sha256']==sha(probe)
assert basepin['snapshot']==str(S/'oleans-mac4') and sha(Path(basepin['owner_olean']).read_bytes())==basepin['owner_olean_sha256']==br['snapshot_owner_olean_before_sha256']
assert sha(Path(basepin['source_path']).read_bytes())==sha(base)
enc=(P/'Base.out.gz.base64.txt').read_bytes();gz=(P/'Base.out.gz').read_bytes();raw=gzip.decompress(gz);assert base64.b64decode(b''.join(enc.split()),validate=True)==gz
for dat,bs,hs in [(enc,'utf8_base64_bytes','utf8_base64_sha256'),(gz,'gzip_bytes','gzip_sha256'),(raw,'raw_stdout_stderr_bytes','raw_stdout_stderr_sha256')]:assert len(dat)==br[bs] and sha(dat)==br[hs]
# Preserve baseline bytes exactly, clearly identified as reused execution, not a second native run.
reused=[]
for name in ['Base-request.json','Base-run.json','Base.out.gz','Base.out.gz.base64.txt','census-base.json','allax-base.json','publicax-base.json','target-base.json','targetax-base.json','names-base.txt']:
 b=(P/name).read_bytes();(O/name).write_bytes(b);reused.append({'original':str((P/name).relative_to(R)),'new_copy':name,'bytes':len(b),'sha256':sha(b),'reused_not_rerun':True})
(O/'baseline-reuse.json').write_text(json.dumps({'source_pin':B,'original_context':ctx,'baseline_execution_reused_after_full_hash_source_context_checks':True,'same_exact_reviewed_probe':sha(probe),'files':reused},indent=2)+'\n')
# Authenticate the completed actual source compile that produced native2.
N=R/'campaign/fills/f6/landing/seam-step-repoint-applied';nr=json.loads((N/'native-result.json').read_bytes());assert nr['head']==H and nr['source_sha256']==sha(source) and nr['exit']==nr['errors']==nr['sorry_warnings']==0;assert nr['out_sha256']==sha((N/'native.out').read_bytes())
(O/'native2-owner-result.received.json').write_bytes((N/'native-result.json').read_bytes())
project=Path(tempfile.mkdtemp(prefix='tcslib-f6-final-accounting-',dir='/private/tmp'));os.chmod(project,0o700)
tc=(WT/'lean-toolchain').read_bytes();assert tc.strip()==b'leanprover/lean4:v4.25.0';(project/'lean-toolchain').write_bytes(tc);(project/'.lake').mkdir();(project/'.lake/packages').symlink_to(WT/'.lake/packages',target_is_directory=True);assert (project/'.lake/packages').resolve()==(WT/'.lake/packages').resolve()
# Complete input inventory, both endpoints read-only; hash native2 fully to establish unchanged artifacts.
def inventory(tree):
 return [{'path':str(p.relative_to(tree)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(tree.rglob('*.olean'))]
headtree=S/'oleans-f6-native2';hi=inventory(headtree);assert len(hi)==895;assert sum(1 for _ in (S/'oleans-mac4').rglob('*.olean'))==895
(O/'snapshot-head-before.json').write_text(json.dumps(hi,indent=2)+'\n')
owner=headtree/REL.replace('.lean','.olean');assert owner.is_file()
wrapper=R/'devtools/seyoon/leanelab.sh';assert 'nice -n 10 lean -j4 "$F"' in wrapper.read_text()
result={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate_head':H,'previous_head':OLD,'baseline_source_pin':B,'pins_verified':pins,'actual_worktree':str(WT),'actual_worktree_resolved':str(WT.resolve()),'source_path':REL,'source_sha256':sha(source),'source_clean_and_pushed':True,'probe_project':str(project),'toolchain':tc.decode().strip(),'packages_resolved':str((project/'.lake/packages').resolve()),'exact_probe_SHA256':sha(probe),'reviewed_code':['compiled-accounting/Inventory.lean.txt','compiled-accounting/analyze.py','compiled-accounting/prepare.py','compiled-accounting/run.py','devtools/seyoon/leanelab.sh'],'wrapper':str(wrapper),'wrapper_sha256':sha(wrapper.read_bytes()),'snapshot':str(headtree),'snapshot_complete_olean_count':len(hi),'owner_olean':str(owner),'owner_olean_sha256':sha(owner.read_bytes()),'BASE_owner_olean':basepin['owner_olean'],'BASE_owner_olean_sha256':basepin['owner_olean_sha256'],'native2_receipt_sha256':sha((N/'native-result.json').read_bytes()),'frozen_original_artifact_count':len(freeze),'local_slots':3,'machine_cap':5,'one_Lean_at_a_time':True,'no_snapshot_output':True,'no_theorem_proof_value_prettyprint':True}
(O/'context.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
