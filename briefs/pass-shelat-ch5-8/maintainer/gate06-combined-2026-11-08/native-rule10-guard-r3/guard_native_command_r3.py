"""UNEXECUTED Root/peer review proposal: guard one pinned Rule10/probe command.

CLI: LABEL REVIEWED_LOCAL_RESULT_SHA256 ABSOLUTE_PINNED_TOOL TOOL_ARGS...
Other trees may run in parallel. This guard interprets environment integrity,
never Lean outcomes; ordinary tool rc0/1 is returned unchanged. No whole-command
retry, cache/source operation, proof option change or evidence overwrite.
"""
from pathlib import Path
import datetime as dt
import hashlib
import importlib.util
import json
import os
import re
import signal
import subprocess
import sys
import time

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
AREA = ROOT/'.lake/ps-maintainer/gate06-combined-20261108'
HERE = AREA/'native-rule10-guard-r3'
SELF = HERE/'guard_native_command_r3.py'
TREE = AREA/'oleans-r1'
LOCAL = AREA/'native-local-resume-r1'
TOOLS = AREA/'rule10-prep/proposed-tools'
HEAD = 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
ENGINE = AREA/'native-runtime-proposal/run_combined_native.py'
ENGINE_SHA = '64b5b2ff2260a48eef55dcf77bdb5c4125459170b28c30499f60a93de7da3c95'
PARALLEL = AREA/'native-runtime-parallel-r1/continue_native.py'
PARALLEL_SHA = '24731171b60eb8da0ce731b633f60bc175c424d877e45fa357a0883d02ce83c5'
APPROVAL = AREA/'user-rulings-20261108-r1.json'
APPROVAL_SHA = '3f0730086b324c2773bcf5239eadfdb86f7c026bbbb5bf2f344283372fa7f9fa'
SOURCE_SHA = '7f606ceb1c33a018ef833ee779457f0e447d334b442acab746b4a8899f82191c'
SETUP_SHA = '8a9a6db13d4b6b9af51e7ea1d9e108a5c59d89a7bbcd5326a2576723789ec3e7'
ALLOWED = {
    str(TOOLS/'check_probe_v2.py'):'c685d6aa01b1b7e44115e88781d1634b3b3cdda512acc702eeba5e810f767179',
    str(TOOLS/'run_gate06_final_native.py'):'0a8b5ebc13d5b2cd4f613fbecb83a357daad285ef84e29774180378f3430a52b',
}
LEASE = AREA/'native-runner.lease.json'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def now(): return dt.datetime.now(dt.timezone.utc).isoformat()
def need(test, reason):
    if not test: raise RuntimeError(reason)
def save(p, value):
    with p.open('x') as stream: stream.write(json.dumps(value,indent=2)+'\n')
def append(p, value):
    with p.open('a') as stream: stream.write(json.dumps(value)+'\n')


def import_pinned(path, digest, name):
    need(sha(path) == digest,'Pinned helper changed: '+str(path))
    spec = importlib.util.spec_from_file_location(name,path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def main():
    need(len(sys.argv) >= 5,'usage: LABEL REVIEWED_LOCAL_RESULT_SHA256 ABSOLUTE_PINNED_TOOL TOOL_ARGS...')
    label, reviewed, tool = sys.argv[1],sys.argv[2],Path(sys.argv[3])
    need(label.replace('-','').replace('_','').isalnum() and re.fullmatch(r'[0-9a-f]{64}',reviewed),'Unsafe label or missing reviewed receipt SHA256')
    need(Path.cwd().resolve() == ROOT and Path(__file__).resolve() == SELF,'Wrong guard worktree/location')
    need(str(tool) in ALLOWED and tool.is_file() and not tool.is_symlink(),'Not an allowed pinned tool')
    expected, self_sha = ALLOWED[str(tool)],sha(SELF)
    need(sha(LOCAL/'RESULT.json') == reviewed,'Completed local receipt absent or differs from reviewed SHA')
    result = load(LOCAL/'RESULT.json')
    expected_fields = {'passed':True,'phase':'local-continuation','head':HEAD,'tree':str(TREE),
                       'coordinator_sha256':PARALLEL_SHA,'engine_sha256':ENGINE_SHA,
                       'required_bootstrap_successes':36,'required_fresh_local_successes':638,
                       'validated_local_objects':1075,'external_package_objects':3637,
                       'toolchain_object_leaves':173,'warm_G06_objects':437,'S2_objects_borrowed':0}
    need(all(result.get(k) == v for k,v in expected_fields.items()),'Incomplete/wrong-source/wrong-producer local receipt')
    need(result['successful_native_attempts_in_history'] == 674 and result['native_attempts_in_history'] >= 675,'Local attempt history counts incomplete')
    need(sha(APPROVAL) == APPROVAL_SHA,'Canonical user approval changed')
    sys.dont_write_bytecode = True
    E = import_pinned(ENGINE,ENGINE_SHA,'g06_guard_r3_engine64')
    scope = import_pinned(PARALLEL,PARALLEL_SHA,'g06_guard_r3_parallel_policy')
    need(sha(scope.APPROVAL) == APPROVAL_SHA and scope.scope_metadata() == result['execution_scope'],'Local receipt lacks the approved exact own-tree policy')
    E.native_processes = scope.own_tree_processes  # Explicit parallel policy, not global host exclusion.
    out = AREA/'guarded-native-r3'/label
    need(not out.exists(),'Fresh guard output required; no whole-phase retry or overwrite')
    out.mkdir(parents=True)
    own = {'pid':os.getpid(),'utc':now(),'guard_sha256':self_sha,'label':label,
           'reviewed_local_result_sha256':reviewed,'execution_scope':scope.scope_metadata()}
    proc, owned = None,False
    def stop_signal(signum,_frame):raise InterruptedError('R3 guard received signal '+str(signum))
    previous = {s:signal.signal(s,stop_signal) for s in (signal.SIGTERM,signal.SIGHUP)}
    def quick_pins():
        need(sha(SELF) == self_sha and sha(tool) == expected and sha(ENGINE) == ENGINE_SHA and sha(PARALLEL) == PARALLEL_SHA,'Guard/tool/helper changed')
        need(sha(APPROVAL) == APPROVAL_SHA and sha(scope.APPROVAL) == APPROVAL_SHA and sha(LOCAL/'RESULT.json') == reviewed,'Approval/local receipt changed')
        need(sha(TOOLS/'setup-summary.json') == SETUP_SHA and load(TOOLS/'setup-summary.json')['olean_tree'] == str(TREE),'Generic checker tree setup changed')
        need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip() == HEAD,'Source HEAD changed')
        need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=ROOT).strip(),'Tracked source dirty')
    try:
        save(LEASE,own); owned = True
        run = E.Run('guard-r3',out)
        ext = load(LOCAL/'external-final.json'); records = load(LOCAL/'local-records.json')
        manifest = load(LOCAL/'FILE-MANIFEST.json')
        def validate_all(stage):
            quick_pins()
            need(sha(LOCAL/'FILE-MANIFEST.json') == result['file_manifest_sha256'],'Local artifact manifest changed')
            actual = {p.relative_to(LOCAL).as_posix() for p in LOCAL.rglob('*') if p.is_file()}
            need(actual == {r['path'] for r in manifest}|{'FILE-MANIFEST.json','RESULT.json'},'Local evidence file set changed')
            for r in manifest:
                p = LOCAL/r['path']
                need(p.resolve(strict=True).is_relative_to(LOCAL) and p.stat().st_size == r['bytes'] and sha(p) == r['sha256'],'Local native artifact changed: '+r['path'])
            need(sha(LOCAL/'source-start.json') == SOURCE_SHA,'Local source inventory is not the frozen1109 snapshot')
            run.validate_frozen_inputs(); run.validate_sources()
            need(run.frozen_source == load(LOCAL/'source-start.json'),'Current full source snapshot differs')
            need(len(records) == 1075 and set(records) == set(run.local) and len(ext) == 3810,'Final local/external record scope differs')
            run.records,run.ext = records,ext
            run.local_set(); run.historical_hashes()
            need(run.ext_snapshot() == ext,'Current3637 package+173 core objects differ')
            for s in run.modules:
                name = s['module']; r = records[name]
                need(r['source_sha256'] == s['source_sha256'] and set(r['direct_local_object_sha256']) == set(s['local_imports']),'Local source/direct contract changed')
                need(r['direct_external_object_sha256'] == {d:ext[d]['object_sha256'] for d in s['external_imports']},'Local external contract changed')
                run.dependencies(s['local_imports'],s['external_imports'])
            quick_pins()
            save(out/('validation-'+stage+'.json'),{'utc':now(),'reviewed_local_result_sha256':reviewed,
                 'file_manifest_sha256':result['file_manifest_sha256'],'source_inventory_sha256':SOURCE_SHA,
                 'local_records_sha256':sha(LOCAL/'local-records.json'),'external_records_sha256':sha(LOCAL/'external-final.json'),
                 'source_files':1109,'local_sources_objects_direct_dependencies':1075,'package_objects':3637,'toolchain_leaves':173,
                 'helper_sha256':ENGINE_SHA,'coordinator_scope_sha256':PARALLEL_SHA,'tool_sha256':expected,'guard_sha256':self_sha,
                 'execution_scope':scope.scope_metadata(),'environment_reconciled':True,'native_outcome_interpreted':False})
        validate_all('initial')
        # Only own-tree native activity is relevant. Other host jobs are approved.
        stable,notice,idle_since,saw_own_activity = 0,0.0,None,False
        while True:
            active = scope.own_tree_processes()
            if active:
                append(out/'own-tree-waits.jsonl',{'utc':now(),'active':active,'native_started':False,'execution_scope':scope.scope_metadata()})
                if time.monotonic()-notice >= 30:
                    print('OWN_TREE_WAIT: another operation uses this olean tree; no new native started',flush=True);notice = time.monotonic()
                stable = 0;idle_since = None;saw_own_activity = True;time.sleep(5)
            else:
                if saw_own_activity:
                    idle_since = time.monotonic() if idle_since is None else idle_since
                    if time.monotonic()-idle_since >= 30:break
                    time.sleep(1)
                else:
                    stable += 1
                    if stable == 3:break
                    time.sleep(0.25)
        resources = E.resources()
        command = [sys.executable,'-I',str(tool),*sys.argv[4:]]
        save(out/'start.json',dict(own,command=command,tool_sha256=expected,engine_sha256=ENGINE_SHA,
             parallel_policy_sha256=PARALLEL_SHA,resources=resources,PATH=run.ordinary_env()['PATH'],TCSLIB_OLEANS=str(TREE)))
        interrupted = None
        with (out/'launcher.log').open('xb') as stream:
            try:
                validate_all('after-idle-prelaunch')
                E.resources();quick_pins()
                need(not scope.own_tree_processes(),'Own tree became busy immediately before launch')
                proc = subprocess.Popen(command,cwd=ROOT,env=run.ordinary_env(),stdin=subprocess.DEVNULL,
                                        stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                save(out/'child.json',{'pid':proc.pid,'pgid':proc.pid,'utc':now()})
                watch = 0.0
                while proc.poll() is None:
                    if time.monotonic()-watch >= 1:
                        foreign = [r for r in scope.own_tree_processes() if r['pgid'] != proc.pid]
                        need(not foreign,'OWN_TREE_COLLISION: '+json.dumps(foreign));watch = time.monotonic()
                    time.sleep(0.1)
                need(not E.group_members(proc.pid),'Live descendant after tool exit')
            except BaseException as exc:
                interrupted = repr(exc)
                if proc is not None:E.Run.stop_own_group(None,proc)
        rc = proc.returncode if proc is not None else None
        save(out/'child-terminal.json',{'utc':now(),'command_rc':rc,'interrupted':interrupted,
             'launcher_log_sha256':sha(out/'launcher.log'),'native_outcome_interpreted':False})
        validate_all('after-child')
        save(out/'RESULT.json',{'utc':now(),'command_rc':rc,'interrupted':interrupted,
             'reviewed_local_result_sha256':reviewed,'head':HEAD,'tree':str(TREE),'guard_sha256':self_sha,
             'tool_sha256':expected,'engine_sha256':ENGINE_SHA,'parallel_policy_sha256':PARALLEL_SHA,
             'execution_scope':scope.scope_metadata(),'environment_reconciled':True,'outcome_interpreted':False,
             'other_processes_signalled':False,'whole_command_retry':False})
        print(json.dumps({'guard_output':str(out),'command_rc':rc,'interrupted':interrupted,'outcome_interpreted':False}),flush=True)
        return 2 if interrupted is not None else rc
    except BaseException as exc:
        if proc is not None and (proc.poll() is None or E.group_members(proc.pid)):E.Run.stop_own_group(None,proc)
        save(out/'STOP.json',{'utc':now(),'error':repr(exc),'own_child_pid':proc.pid if proc else None,
             'actual_command_rc':proc.returncode if proc else None,'native_outcome_interpreted':False,'retry':False})
        return 2
    finally:
        if owned:
            need(load(LEASE) == own,'Own lease changed; never remove another lease');LEASE.unlink()
        for s,handler in previous.items():signal.signal(s,handler)


if __name__ == '__main__':
    try:sys.exit(main())
    except Exception as exc:
        print('G06-R3-GUARD-REFUSED: '+repr(exc),file=sys.stderr,flush=True)
        sys.exit(2)
