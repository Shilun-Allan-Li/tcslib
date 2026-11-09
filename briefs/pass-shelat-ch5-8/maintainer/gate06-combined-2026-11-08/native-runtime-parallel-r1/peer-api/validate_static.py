"""Own AST/data-only peer check; no import/execution of reviewed code."""
from pathlib import Path
import ast
import copy
import difflib
import hashlib
import json

W=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
A=W/'.lake/ps-maintainer/gate06-combined-20261108'
P=A/'native-runtime-parallel-r1'
OUT=P/'peer-api'
OLD=A/'native-runtime-resume-r1/continue_native.py'
PINS={
 'continue_native.py':'24731171b60eb8da0ce731b633f60bc175c424d877e45fa357a0883d02ce83c5',
 'from-9219.diff':'260c7b113d4d003f90ef4910cf84853dcfa882e55f0824783782b7a1a6e5a707',
 'R1-FINGERPRINTS.json':'47c3740c7e5abaf68fe9a82cdb0eba405ea9acdf51a7c14248a16b5817e7beaa',
 'user-rulings-20261108-r1.json':'3f0730086b324c2773bcf5239eadfdb86f7c026bbbb5bf2f344283372fa7f9fa',
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def need(t,label):
 if not t:raise AssertionError(label)
def dump(n):return ast.dump(n,include_attributes=False)
def methods(t):
 f=next(n for n in t.body if isinstance(n,ast.FunctionDef) and n.name=='coordinator_class')
 c=next(n for n in f.body if isinstance(n,ast.ClassDef))
 return {n.name:n for n in c.body if isinstance(n,ast.FunctionDef)}
def main():
 for f,h in PINS.items():need(sha(P/f)==h,'proposal pin '+f)
 need(sha(OLD)=='921959c0d81c4ffb7e2cedd38e540be69e19e8d62ec8f3743b7bd0ad6117369c','old coordinator')
 old=OLD.read_text();new=(P/'continue_native.py').read_text()
 need(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='native-runtime-resume-r1/continue_native.py',tofile='native-runtime-parallel-r1/continue_native.py'))==(P/'from-9219.diff').read_text(),'exact delta')
 ot,nt=ast.parse(old),ast.parse(new);om,nm=methods(ot),methods(nt)
 need(set(om)==set(nm),'method set unchanged')
 changed={k for k in om if dump(om[k])!=dump(nm[k])}
 need(changed=={'__init__','quick_pins','adaptive_idle','perform','local_continuation','finish_continuation'},'only six expected method deltas')
 # In perform, only its COORDINATOR metadata expression changes.
 op,np=copy.deepcopy(om['perform']),copy.deepcopy(nm['perform'])
 def remove_metadata(t):
  loop=t.body[0]
  matches=[i for i,n in enumerate(loop.body) if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and ast.unparse(n.value.func)=='save' and 'COORDINATOR.json' in ast.unparse(n)]
  need(len(matches)==1,'one call metadata statement');del loop.body[matches[0]]
 remove_metadata(op);remove_metadata(np);need(dump(op)==dump(np),'perform runtime logic identical')
 need([dump(n) for n in om['local_continuation'].body[2:]]==[dump(n) for n in nm['local_continuation'].body[3:]],'post-adoption local logic unchanged')
 calls=[ast.unparse(n.func) for n in ast.walk(nt) if isinstance(n,ast.Call)]
 need(not any(x in {'subprocess.Popen','os.kill','os.killpg'} for x in calls),'no new native launch/signalling')
 need(calls.count('subprocess.check_output')==1 and calls.count('E.Run.check')==1,'one ps query and one native delegation')
 need('E.native_processes = own_tree_processes' in new and 'E.wait_idle = run.adaptive_idle' in new,'explicit two overrides')
 need("sys.argv[1] == 'local'" in new and 'run.bootstrap_continuation()' not in new,'local-only main')
 need(sha(P/'user-rulings-20261108-r1.json')==sha(A/'user-rulings-20261108-r1.json'),'approval copy canonical')
 approval=load(P/'user-rulings-20261108-r1.json')
 need(approval['parallel_verification']['decision']=='APPROVED' and approval['six_global_simp_attributes']['decision']=='APPROVED_EXACT_SIX' and len(approval['six_global_simp_attributes']['declarations'])==6,'exact two approvals')
 need(sha(W/'scripts/lean_check_tree.sh')=='366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335','checker fixed')
 need('lean "$rel.lean" -o "$OL/$rel.olean"' in (W/'scripts/lean_check_tree.sh').read_text(),'absolute own-tree argv contract')
 B=A/'native-bootstrap-resume-r1';result=load(B/'RESULT.json');manifest=load(B/'FILE-MANIFEST.json')
 need(sha(B/'RESULT.json')=='e1fa6d0282b1e683f971a3e4088ec5e36228615b279634745e1ff4ea1ace8cca','completed BOOT result')
 need(sha(B/'FILE-MANIFEST.json')==result['file_manifest_sha256']=='f26e727bea498ad3287c5d928ccb09dce11b3e36bec1574b13f10d36880bc70c','completed BOOT manifest')
 need(result['passed'] is True and result['phase']=='bootstrap-continuation' and result['coordinator_sha256']==sha(OLD),'old coordinator receipt, not new self')
 need({str(p.relative_to(B)) for p in B.rglob('*') if p.is_file()}=={r['path'] for r in manifest}|{'FILE-MANIFEST.json','RESULT.json'},'BOOT artifact set')
 for r in manifest:
  p=B/r['path'];need(p.resolve(strict=True).is_relative_to(B) and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'BOOT leaf')
 success=load(B/'successes.json');history=[json.loads(x) for x in (B/'attempt-ledger.jsonl').read_text().splitlines()]
 need(len(success)==36 and len(history)==len({x['id'] for x in history})==37,'BOOT exact identities')
 need({x['key'] for x in history if x['status'] in {'PASSED_REUSED','PASSED_NEW'}}==set(success),'BOOT success key set')
 for r in history:
  p=Path(r['record_path']);row=load(p);need(sha(p)==r['record_sha256'] and sha(Path(row['log']))==row['log_sha256']==r['log_sha256'],'BOOT raw record/log link')
 data={'status':'STATIC_AST_DATA_PASS_NO_REVIEWED_EXECUTION','pins':PINS,'old_coordinator_sha256':sha(OLD),'changed_methods':sorted(changed),'unchanged_methods':sorted(set(om)-changed),'BOOT_result_sha256':sha(B/'RESULT.json'),'BOOT_manifest_sha256':sha(B/'FILE-MANIFEST.json'),'BOOT_manifest_files':len(manifest),'BOOT_success_identity_count':len(success),'BOOT_history_count':len(history),'BOOT_status_counts':result['history_status_counts'],'BOOT_local_record_count':len(load(B/'local-records.json')),'BOOT_external_record_count':len(load(B/'external-final.json')),'source_head':result['head'],'programs_imported_or_executed':False,'processes_or_native_simulated':False}
 with (OUT/'validation.json').open('x') as f:json.dump(data,f,indent=2);f.write('\n')
 print(json.dumps({'status':data['status'],'validation_sha256':sha(OUT/'validation.json')}))
if __name__=='__main__':main()
