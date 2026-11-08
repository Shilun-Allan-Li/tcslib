"""Prepare fresh post234 probes only after root supplies the actual pushed head/snapshot."""
from pathlib import Path
import json,hashlib,subprocess,sys,os,tempfile,datetime
O=Path('/private/tmp/f6-post234-context-review');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/fills/f6/landing/compiled-accounting-final';S=Path(os.environ['TCSLIB_SCRATCH']);W=S/'wt-f6';REL='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean';C='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c';OLD='0d0950caeb39300b5cc9bf41e5f07392fb26d3e5'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(W),*a])
head=sys.argv[1];tree=Path(sys.argv[2]);receipt=Path(sys.argv[3]);assert len(head)==40
for pin in [head,C,OLD]:assert git('rev-parse',pin+'^{commit}').decode().strip()==pin;git('cat-file','-e',pin+'^{commit}')
assert git('rev-parse','HEAD').decode().strip()==head==git('rev-parse','@{upstream}').decode().strip();assert git('status','--porcelain=v1','--untracked-files=no')==b''
for pin in [C,OLD]:assert subprocess.run(['git','-C',str(W),'merge-base','--is-ancestor',pin,head]).returncode==0
source=(W/REL).read_bytes();assert sha(source)=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3' and source==git('show',head+':'+REL)==git('show',OLD+':'+REL)
changed=git('diff','--name-only',C,head,'--','*.lean').decode().splitlines();assert changed==[REL]
for x in json.loads((O/'API-context-check.json').read_bytes())['five_API_sources']:assert git('show',head+':'+x['path'])==git('show',C+':'+x['path'])
rr=json.loads(receipt.read_bytes());assert rr['head']==head and rr.get('pipeline_exit',rr.get('exit'))==0 and rr.get('failed',rr.get('errors',0))==0
before=[]
for p in sorted(P.rglob('*')):
 if p.is_file():b=p.read_bytes();before.append({'path':str(p.relative_to(P)),'bytes':len(b),'sha256':sha(b)})
assert sha((P/'MANIFEST.json').read_bytes())=='0c8d3487e95c62731d750f2b91f1a93314b64861bffced766d5389885e2faad9'
for row in json.loads((P/'MANIFEST.json').read_bytes())['files']:
 b=(P/row['path']).read_bytes();assert (len(b),sha(b))==(row['bytes'],row['sha256'])
(O/'previous-final-before.json').write_text(json.dumps(before,indent=2)+'\n')
project=Path(tempfile.mkdtemp(prefix='tcslib-f6-post234-',dir='/private/tmp'));os.chmod(project,0o700);tc=(W/'lean-toolchain').read_bytes();assert tc.strip()==b'leanprover/lean4:v4.25.0';(project/'lean-toolchain').write_bytes(tc);(project/'.lake').mkdir();(project/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True)
D=O/'fresh-validation';assert not D.exists();D.mkdir()
inputs=[('Inventory.lean.txt',P/'Inventory.lean.txt'),('Owner-native.lean.txt',P/'scoped-seals-final/Owner-native.lean.txt'),('Owner-sealed.lean.txt',P/'scoped-seals-final/Owner-sealed.lean.txt'),('Controls-native.lean.txt',P/'scoped-seals-final/Controls-native.lean.txt'),('Controls-sealed.lean.txt',P/'scoped-seals-final/Controls-sealed.lean.txt'),('ArbitraryFiniteness.lean.txt',P/'finite-witness-diagnostic-final/ArbitraryFiniteness.lean.txt')]
assert (inputs[1][1]).read_bytes().startswith(source)
inputrows=[]
for name,p in inputs:
 b=p.read_bytes();(D/name).write_bytes(b);inputrows.append({'name':name,'exact_prior_source':str(p.relative_to(R)),'bytes':len(b),'sha256':sha(b)})
base=S/'oleans-mac5';snapshots=[]
for label,t in [('Base',base),('Head',tree)]:
 rows=[{'path':str(p.relative_to(t)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(t.rglob('*.olean'))];assert len(rows)==895
 (O/('snapshot-'+label.lower()+'-before.json')).write_text(json.dumps(rows,indent=2)+'\n');owner=t/REL.replace('.lean','.olean');snapshots.append({'endpoint':label,'path':str(t),'olean_count':895,'owner_olean':str(owner),'owner_sha256':sha(owner.read_bytes())})
(O/'Hierarchy-current.lean.txt').write_bytes(source);(O/'root-replay-receipt.received.json').write_bytes(receipt.read_bytes())
ctx={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':head,'campaign_base':C,'proof_component':OLD,'source_sha256':sha(source),'Hierarchy_bytes_exact_old_component':True,'source_worktree':str(W),'project':str(project),'packages_resolved':str((project/'.lake/packages').resolve()),'toolchain':tc.decode().strip(),'wrapper':str(R/'devtools/seyoon/leanelab.sh'),'wrapper_sha256':sha((R/'devtools/seyoon/leanelab.sh').read_bytes()),'snapshots':snapshots,'root_replay_receipt_source':str(receipt),'root_replay_receipt_sha256':sha(receipt.read_bytes()),'inputs':inputrows,'input_sources_reviewed_and_byte_identical':True,'one_Lean_at_a_time':True,'local_slots':3,'machine_cap':5,'no_compiled_snapshot_output':True,'no_theorem_proof_value_prettyprint':True}
(O/'refresh-context.json').write_text(json.dumps(ctx,indent=2)+'\n');print(json.dumps(ctx,indent=2))
