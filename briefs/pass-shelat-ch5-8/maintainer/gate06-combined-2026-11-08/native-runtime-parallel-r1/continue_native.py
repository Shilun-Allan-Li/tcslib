"""UNEXECUTED local-only parallel-policy successor; python3 -I continue_native.py local.

Explicit user ruling supersedes global one-host exclusion. Retain one Lean per
own actual output tree, global resource floors and own-child-only signaling.
Accept only completed BOOT coordinator9219; never compare it to this new self.
Retain the failed R1. Adopt only its two validated successes. Delegate each new
check to pinned64b in a fresh call directory; retry only audited host collisions
or the exact prelaunch host-deferred case. No source/cache/copy operations.
"""
from pathlib import Path
import ast
import collections
import hashlib
import importlib.util
import json
import os
import re
import signal
import subprocess
import sys
import time

W = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
A = W/'.lake/ps-maintainer/gate06-combined-20261108'
HERE = A/'native-runtime-parallel-r1'
SELF = HERE/'continue_native.py'
ENGINE = A/'native-runtime-proposal/run_combined_native.py'
ENGINE_SHA = '64b5b2ff2260a48eef55dcf77bdb5c4125459170b28c30499f60a93de7da3c95'
R1 = A/'native-bootstrap-r1'
R1_PINS = HERE/'R1-FINGERPRINTS.json'
R1_PINS_SHA = '47c3740c7e5abaf68fe9a82cdb0eba405ea9acdf51a7c14248a16b5817e7beaa'
BOOT = A/'native-bootstrap-resume-r1'
LOCAL = A/'native-local-resume-r1'
HEAD = 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
BOOT_COORDINATOR_SHA = '921959c0d81c4ffb7e2cedd38e540be69e19e8d62ec8f3743b7bd0ad6117369c'
BOOT_RESULT_SHA = 'e1fa6d0282b1e683f971a3e4088ec5e36228615b279634745e1ff4ea1ace8cca'
BOOT_MANIFEST_SHA = 'f26e727bea498ad3287c5d928ccb09dce11b3e36bec1574b13f10d36880bc70c'
APPROVAL = HERE/'user-rulings-20261108-r1.json'
APPROVAL_SHA = '3f0730086b324c2773bcf5239eadfdb86f7c026bbbb5bf2f344283372fa7f9fa'
COLLISION = 'HOST_COLLISION: another native operation started: '


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def need(test, reason):
    if not test: raise RuntimeError(reason)
def save(p, value):
    with p.open('x') as stream: stream.write(json.dumps(value, indent=2)+'\n')
def append(p, value):
    with p.open('a') as stream: stream.write(json.dumps(value)+'\n')


def own_tree_rows(text):
    # Read actual argv, never process environments. Return only PID/PGID/executable.
    rows = []; tree = str(A/'oleans-r1')
    boundary = re.compile(r'(?<![A-Za-z0-9_./-])'+re.escape(tree)+r'(?=/|\s|$)')
    for line in text.splitlines():
        fields = line.strip().split(None,3)
        if len(fields) != 4: continue
        name = Path(fields[2]).name
        native = name in {'lean','lake','leantar'} or (name == 'cache' and '/mathlib/' in fields[2])
        if native and boundary.search(fields[3]):
            rows.append({'pid':int(fields[0]),'pgid':int(fields[1]),'command':fields[2]})
    return rows


def own_tree_processes():
    return own_tree_rows(subprocess.check_output(['ps','-axo','pid=,pgid=,comm=,args='],text=True))


def scope_metadata():
    return {'policy':'OWN_OLEAN_TREE_PARALLEL_HOST_APPROVED','TCSLIB_OLEANS':str(A/'oleans-r1'),
            'parallel_other_trees_allowed':True,'one_native_per_own_tree':True,
            'process_match':'actual ps argv contains own absolute tree path; record PID/PGID/executable only; no environment dump',
            'approval_file':str(APPROVAL),'approval_sha256':APPROVAL_SHA,
            'user_answer_verbatim':load(APPROVAL)['parallel_verification']['user_answer_verbatim'],
            'resource_floor_bytes':4*1024**3,'own_process_only_signalling':True}


def collision_message(value):
    """Parse only the engine's exact RuntimeError representation, never eval it."""
    try:
        node = ast.parse(value, mode='eval').body
        need(isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'RuntimeError' and len(node.args) == 1 and not node.keywords, 'not engine RuntimeError')
        message = ast.literal_eval(node.args[0])
        need(isinstance(message, str) and message.startswith(COLLISION), 'not host collision')
        rows = json.loads(message[len(COLLISION):])
        need(isinstance(rows, list) and rows and all(isinstance(r, dict) and set(r) == {'pid','pgid','command'} and type(r['pid']) is int and r['pid'] > 0 and type(r['pgid']) is int and r['pgid'] > 0 and isinstance(r['command'], str) for r in rows), 'bad foreign process rows')
        need(all(Path(r['command']).name in {'lean','lake','leantar'} or (Path(r['command']).name == 'cache' and '/mathlib/' in r['command']) for r in rows), 'not an engine-recognized native process')
        return rows
    except (ValueError, SyntaxError, TypeError, RuntimeError): return None


def owner_markers(text):
    pairs = re.findall(r'PFR-MODULE ([A-Za-z0-9_.]+): ([A-Za-z0-9_.]+)', text)
    expected = {r['module'] for r in load(A/'native-prep/external-r1/pfr-modules.json')}
    need(len(pairs) == 31 and {x for x,_ in pairs} == expected and all(x == y for x,y in pairs), 'PFR module headers invalid')
    owners = re.findall(r'PFR-OWNER ([A-Za-z0-9_.]+): ([A-Za-z0-9_.]+)', text)
    need(len(owners) == 3 and dict(owners) == {'KLDiv':'PFR.Kullback','ProbabilityTheory.entropy':'PFR.ForMathlib.Entropy.Basic','ProbabilityTheory.uniformOn_apply_singleton_of_mem':'PFR.Mathlib.Probability.UniformOn'}, 'PFR owner markers invalid')
    need(len(re.findall(r'PFR-MODULES 31; PFR-PRIVATE \d+; EOF', text)) == 1, 'PFR identity EOF invalid')


def coordinator_class(E):
    class Coordinator(E.Run):
        def __init__(self, phase, out):
            self.coordinator_sha, self.root_out = sha(SELF), out
            self.long_idle, self.call_number, self.history, self.success = False, 0, [], {}
            super().__init__(phase, out)

        def quick_pins(self):
            super().quick_pins()
            need(sha(SELF) == self.coordinator_sha and sha(R1_PINS) == R1_PINS_SHA, 'Coordinator/R1 inventory changed')
            need(sha(APPROVAL) == APPROVAL_SHA and sha(A/APPROVAL.name) == APPROVAL_SHA, 'User ruling changed')

        def r1_files(self):
            pins = load(R1_PINS)
            need({str(p.relative_to(R1)) for p in R1.rglob('*') if p.is_file()} == {r['path'] for r in pins['files']}, 'R1 evidence set changed')
            for r in pins['files']:
                p = R1/r['path']; need(p.stat().st_size == r['bytes'] and sha(p) == r['sha256'], 'R1 evidence bytes changed')
            need(not (R1/'RESULT.json').exists(), 'Never turn failed R1 into a success aggregate')

        def adaptive_idle(self, out):
            """Own-tree wait only:0.5s normally,30s after same-tree conflict;64b unchanged."""
            beginning, short, notice = None, 0, 0.0
            while True:
                active = E.native_processes()
                if active:
                    self.long_idle = True; beginning = None; short = 0
                    append(out/'host-waits.jsonl', {'utc':E.now(),'active':active,'native_started':False,'idle_policy':'own tree only;30s after same-tree activity'})
                    if time.monotonic()-notice >= 30:
                        print('OWN_TREE_WAIT:30s stable idle after same-tree activity', flush=True); notice = time.monotonic()
                    time.sleep(5); continue
                if self.long_idle:
                    beginning = time.monotonic() if beginning is None else beginning
                    if time.monotonic()-beginning >= 30:
                        self.long_idle = False; return
                    time.sleep(1)
                else:
                    short += 1
                    if short == 3: return
                    time.sleep(0.25)

        def spec(self, key, label, rel, digest, local, external, pfr=False, expected=None, marker=None):
            return dict(key=key,label=label,rel=rel,digest=digest,local=local,external=external,pfr=pfr,expected=expected,marker=marker)

        def pfr_spec(self, r):
            return self.spec(r['module'],r['module'].replace('.','_'),'.lake/packages/PFR/'+r['package_relative_source'][:-5],r['source_sha256'],[],r['imports'],True)

        def cache_spec(self):
            roots = (E.P/'external-r1/mathlib-full-union-roots.txt').read_text().splitlines()+['Std.Sat.CNF','Batteries.Data.Nat.Lemmas']
            expected = (''.join('import '+x+'\n' for x in roots)+'\n#eval IO.println "G06-COMBINED-CACHE-383 EOF"\n').encode()
            need((R1/'CacheProbe.lean').read_bytes() == expected and len(roots) == 385, 'R1 cache probe recipe differs')
            return self.spec('CacheProbe','CacheProbe',str((R1/'CacheProbe').relative_to(W)),hashlib.sha256(expected).hexdigest(),[],roots,marker=lambda text:need(text.splitlines().count('G06-COMBINED-CACHE-383 EOF') == 1,'Cache EOF invalid'))

        def receipt(self, row, spec, success):
            """Raw start/child/footer/end, current source/deps, and native outcome."""
            d = Path(row['log']).parent; text = (d/'native.log').read_text(); start = load(d/'start.json'); child = load(d/'child.json')
            need(load(d/'end.json') == row and sha(d/'native.log') == row['log_sha256'], 'Native raw receipt/log differs')
            need(json.loads(text.splitlines()[0]) == start, 'Native header differs')
            need(json.loads(text.splitlines()[-1]) == {'event':'END','utc':row['end_utc'],'rc':row['rc'],'interrupted':row['interrupted']}, 'Native footer differs')
            need(row['head'] == start['head'] == HEAD and row['module'] == start['module'] == spec['rel'] and row['label'] == start['label'] == spec['label'], 'Wrong native source identity')
            need(start['utc'] == row['start_utc'] and row['object_before_sha256'] == start['object_before_sha256'] and child['command'] == ['/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',spec['rel']], 'Native start/command differs')
            need(row['source_sha256'] == row['source_sha256_before'] == row['source_sha256_after'] == spec['digest'] == sha(W/(spec['rel']+'.lean')) and row['source_unchanged'], 'Native source changed')
            need(row['checker_sha256'] == row['checker_sha256_after'] == start['checker_sha256'] == E.CHECKER_SHA and row['runner_sha256'] == row['runner_sha256_after'] == start['runner_sha256'] == ENGINE_SHA and row['pfr_config_sha256_after'] == start['pfr_config_sha256'] == E.CFG_SHA, 'Native tool/config identity differs')
            need(start['TCSLIB_OLEANS'] == str(E.TREE) and start['pfr_only_PATH'] is spec['pfr'], 'Wrong native tree/PFR PATH')
            path = self.ordinary_env()['PATH']; path = str(A/'pfr-runtime-r1/bin')+':'+path if spec['pfr'] else path
            need(start['PATH'] == path and child['pgid'] == child['pid'] and child['runner_pid'] > 0, 'Native child/session/PATH differs')
            current = self.dependencies(spec['local'],spec['external'])
            need(row['dependencies_before'] == row['dependencies_after'] == start['dependencies_before'] == current, 'Native prerequisite context differs')
            errors = len(re.findall(r'\berror(?:\([^)]*\))?:',text)); rss = re.search(r'^\s*(\d+)\s+maximum resident set size\s*$',text,re.M)
            need(row['error_diagnostics'] == errors == 0 and row['passed'] is success, 'Source diagnostic/failure cannot be retried')
            if success:
                obj = E.TREE/(spec['rel']+'.olean')
                need(row['rc'] == 0 and row['interrupted'] is None and row['post_validation_error'] is None and row['fresh_nonempty_object'] and obj.is_file() and obj.stat().st_size > 0 and sha(obj) == row['object_sha256'] and rss is not None and int(rss[1]) == row['max_rss_bytes_macos'], 'Native success/object/RSS invalid')
                if spec['expected']: need(row['object_sha256'] == row['expected_reproduction_sha256'] == spec['expected'], 'Reproduction bytes differ')
                if spec['marker']: spec['marker'](text)
            else:
                foreign = collision_message(row['interrupted'])
                need(foreign and all(r['pgid'] != child['pgid'] for r in foreign) and row['rc'] in {-15,-9} and row['post_validation_error'] == "RuntimeError('Native checker failed')", 'Not the exact isolated host-collision failure')
            return d

        def prefix(self, pending=None):
            """Never adopt a failed target; allow only that target to await rerun."""
            actual = {str(p.relative_to(E.TREE))[:-6] for p in (E.TREE/'TCSlib').rglob('*.olean')}
            for name in ['TCSlib','audits/pass-shelat/Checks']:
                if (E.TREE/(name+'.olean')).is_file(): actual.add(name)
            need(actual-set(self.records) <= ({pending} if pending else set()), 'Unexpected local output beyond validated prefix')
            for name,r in self.records.items():
                need(sha(W/(name+'.lean')) == r['source_sha256'], 'Prefix source drift')
                if name != pending: need((E.TREE/(name+'.olean')).is_file() and sha(E.TREE/(name+'.olean')) == r['object_sha256'], 'Prefix object drift')
                need(all(d in self.records and self.records[d]['object_sha256'] == value for d,value in r['direct_local_object_sha256'].items()), 'Prefix local prerequisite drift')
            base = self.ext_snapshot(allow_pending_pfr=True)
            need(base == {k:v for k,v in self.ext.items() if not k.startswith('PFR.')}, 'Package/core objects changed')
            for name in self.ext:
                if name.startswith('PFR.'): self.dependencies([],[name])

        def ledger(self, value):
            self.history.append(value); append(self.root_out/'attempt-ledger.jsonl',value)

        def perform(self, spec):
            while True:
                self.call_number += 1; call = self.root_out/'calls'/f'{self.call_number:06d}'
                call.mkdir(parents=True,exist_ok=False); self.out = call; self.attempts = []
                save(call/'COORDINATOR.json',{'coordinator_sha256':self.coordinator_sha,'engine_sha256':ENGINE_SHA,'key':spec['key'],'phase':self.phase,'idle_policy':'own tree only;0.5s initial/between own successes;30s after same-tree activity','execution_scope':scope_metadata()})
                error, row, status = None, None, None
                try:
                    row = E.Run.check(self,spec['label'],spec['rel'],spec['digest'],spec['local'],spec['external'],pfr=spec['pfr'],expected_object=spec['expected'],markers=spec['marker'])
                    self.receipt(row,spec,True); status = 'PASSED_NEW'
                except BaseException as exc:
                    error = repr(exc); row = self.attempts[-1] if self.attempts else None
                    if row is not None:
                        try: self.receipt(row,spec,False); status = 'HOST_COLLISION_RETAINED'
                        except BaseException: status = 'STOP_NONRETRYABLE'
                    elif type(exc) is RuntimeError and str(exc) == 'Host became busy after stable-idle check':
                        starts = list((call/'checks').glob('*/start.json'))
                        need(len(starts) == 1 and not list(call.rglob('child.json')) and not list(call.rglob('native.log')), 'Host-deferred call unexpectedly started native')
                        header = load(starts[0]); self.quick_pins()
                        need(header['source_sha256'] == spec['digest'] == sha(W/(spec['rel']+'.lean')) and header['dependencies_before'] == self.dependencies(spec['local'],spec['external']), 'Deferred source/context changed')
                        status = 'HOST_DEFERRED_NO_NATIVE'
                    else: status = 'STOP_NONRETRYABLE'
                finally: self.out = self.root_out
                item = {'id':self.phase+':'+f'{self.call_number:06d}','origin':self.phase,'key':spec['key'],'status':status,'native_started':bool(list(call.rglob('child.json'))),'call_directory':str(call),'exception':error,'coordinator_sha256':self.coordinator_sha}
                if row is not None: item.update(record_path=str(Path(row['log']).with_name('end.json')),record_sha256=sha(Path(row['log']).with_name('end.json')),log_sha256=row['log_sha256'],rc=row['rc'])
                save(call/'DISPOSITION.json',item); self.ledger(item)
                if status == 'PASSED_NEW':
                    self.success[spec['key']] = item; return row
                need(status in {'HOST_COLLISION_RETAINED','HOST_DEFERRED_NO_NATIVE'}, 'STOP: source/setup/resource/signal/marker/pin failure is never automatically retried')
                self.long_idle = True
                self.validate_sources(); self.prefix(pending=spec['rel']); self.r1_files()

        def add_pfr(self, source, row):
            self.ext[source['module']] = {'object_path':str(self.object_path(source['module'])),'object_sha256':row['object_sha256'],'object_bytes':self.object_path(source['module']).stat().st_size,'source_sha256':source['source_sha256'],'kind':'PFR_OWN_TREE'}

        def required_specs(self):
            owner = self.spec('PFRIdentityProbe','PFRIdentityProbe',str((BOOT/'PFRIdentityProbe').relative_to(W)),E.OWNER_PROBE_SHA,[],['PFR.Mathlib.Probability.UniformOn','PFR.ForMathlib.Entropy.Basic','PFR.Kullback'],marker=owner_markers)
            reps = [self.spec('reproduce:'+r['module'],'Reproduce_'+r['module'].replace('/','_'),r['module'],r['source_sha256'],self.local[r['module']]['local_imports'],self.local[r['module']]['external_imports'],expected=r['expected_object_sha256']) for r in load(E.P/'recommended-reproductions.json')['modules']]
            return [self.cache_spec()]+[self.pfr_spec(r) for r in self.pfr]+[owner]+reps

        def adopt_r1(self):
            self.r1_files(); need(not E.LEASE.exists() or load(E.LEASE)['runner_pid'] == os.getpid(), 'Other lease present')
            need(load(R1/'START.json')['runner_sha256'] == ENGINE_SHA and load(R1/'START.json')['head'] == HEAD and load(R1/'STOP.json')['phase'] == 'bootstrap', 'Wrong interrupted R1')
            self.ext = self.ext_snapshot(allow_pending_pfr=True)
            need(self.ext == load(R1/'external-before.json'), 'R1 full external context changed')
            self.records = {k:{'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'direct_local_object_sha256':r['direct_local_object_sha256'],'origin':'VALIDATED_G06_COPY_PENDING_THREE_REPRODUCTIONS'} for k,r in self.copy.items()}
            self.local_set(); self.historical_hashes()
            rows = [json.loads(s) for s in (R1/'attempts.jsonl').read_text().splitlines()]; need(len(rows) == 3,'R1 attempt count changed')
            specs = self.required_specs()
            self.receipt(rows[0],specs[0],True); self.receipt(rows[1],specs[1],True); self.add_pfr(self.pfr[0],rows[1])
            self.receipt(rows[2],specs[2],False)
            need(not (E.TREE/(specs[2]['rel']+'.olean')).exists(),'Failed R1 Kernel object must not be reused')
            actual = {p.resolve() for p in (E.TREE/'.lake/packages/PFR/PFR').rglob('*.olean')}
            need(actual == {self.object_path(self.pfr[0]['module']).resolve()},'Unexpected PFR prefix')
            for i,row in enumerate(rows):
                item = {'id':'R1:'+str(i),'origin':'native-bootstrap-r1','key':specs[i]['key'],'status':'PASSED_REUSED' if i<2 else 'HOST_COLLISION_RETAINED','native_started':True,'record_path':str(Path(row['log']).with_name('end.json')),'record_sha256':sha(Path(row['log']).with_name('end.json')),'log_sha256':row['log_sha256'],'rc':row['rc']}
                self.ledger(item)
                if i<2:self.success[specs[i]['key']] = item
            (self.root_out/'R1-attempts.verbatim.jsonl').write_bytes((R1/'attempts.jsonl').read_bytes())
            save(self.root_out/'R1-validated.json',{'input_manifest_sha256':R1_PINS_SHA,'adopted_successes':2,'retained_failures':1,'failed_output_adopted':False})

        def bootstrap_continuation(self):
            self.adopt_r1(); specs = self.required_specs()
            for r in self.pfr[1:]: self.add_pfr(r,self.perform(self.pfr_spec(r)))
            with (BOOT/'PFRIdentityProbe.lean').open('xb') as stream: stream.write(E.OWNER_PROBE.read_bytes())
            for spec in specs[32:]:
                row = self.perform(spec)
                if spec['key'].startswith('reproduce:'): self.records[spec['rel']]['reproduced_current_phase'] = True
            need(set(self.success) == {s['key'] for s in specs} and len(self.success) == 36,'Incomplete bootstrap aggregate')
            for r in self.records.values():r['origin'] = 'G06_COPY_SUPPORTED_BY_THREE_EXACT_FRESH_REPRODUCTIONS'

        def local_continuation(self):
            need(sha(BOOT/'RESULT.json') == BOOT_RESULT_SHA and sha(BOOT/'FILE-MANIFEST.json') == BOOT_MANIFEST_SHA,'Only the completed reviewed BOOT aggregate is accepted')
            result = load(BOOT/'RESULT.json'); need(result['passed'] is True and result['phase'] == 'bootstrap-continuation' and result['head'] == HEAD and result['coordinator_sha256'] == BOOT_COORDINATOR_SHA,'Completed original9219 bootstrap required; not new self')
            manifest = load(BOOT/'FILE-MANIFEST.json'); need(sha(BOOT/'FILE-MANIFEST.json') == result['file_manifest_sha256'],'Bootstrap continuation manifest changed')
            for r in manifest:
                p = BOOT/r['path']; need(p.resolve(strict=True).is_relative_to(BOOT) and p.stat().st_size == r['bytes'] and sha(p) == r['sha256'],'Bootstrap continuation artifact changed')
            need({str(p.relative_to(BOOT)) for p in BOOT.rglob('*') if p.is_file()} == {r['path'] for r in manifest}|{'FILE-MANIFEST.json','RESULT.json'},'Bootstrap continuation artifact set changed')
            self.ext,self.records,self.success = load(BOOT/'external-final.json'),load(BOOT/'local-records.json'),load(BOOT/'successes.json')
            self.history = [json.loads(s) for s in (BOOT/'attempt-ledger.jsonl').read_text().splitlines()]
            (self.root_out/'attempt-ledger.jsonl').write_bytes((BOOT/'attempt-ledger.jsonl').read_bytes())
            need(self.ext_snapshot() == self.ext,'Bootstrap external objects changed'); self.local_set(); self.r1_files(); self.historical_hashes()
            need(set(self.success) == {s['key'] for s in self.required_specs()} and len(self.success) == 36,'Bootstrap36 required success identities differ')
            for spec in self.required_specs():
                item = self.success[spec['key']]; need(sha(Path(item['record_path'])) == item['record_sha256'],'Bootstrap success receipt changed'); self.receipt(load(Path(item['record_path'])),spec,True)
            order = (E.P/'plan-r1/rebuild-order.txt').read_text().splitlines()
            need(len(order) == len(set(order)) == 638 and set(order).isdisjoint(self.records) and set(order)|set(self.records) == set(self.local),'Local638 partition differs')
            for name in order:
                s = self.local[name]; spec = self.spec('local:'+name,name.replace('/','_'),name,s['source_sha256'],s['local_imports'],s['external_imports']); row = self.perform(spec)
                self.records[name] = {'source_sha256':s['source_sha256'],'object_sha256':row['object_sha256'],'direct_local_object_sha256':{d:self.records[d]['object_sha256'] for d in s['local_imports']},'origin':'FRESH_LOCAL_CONTINUATION'}
            need(len(self.records) == 1075 and all(self.records[k]['origin'] == 'FRESH_LOCAL_CONTINUATION' for k in ['TCSlib','audits/pass-shelat/Checks']),'Fresh root/PSChecks missing')

        def finish_continuation(self):
            old_cache = self.cache_sha; self.validate_frozen_inputs(); need(self.cache_sha == old_cache,'Cache receipt changed')
            self.validate_sources(); self.local_set(); self.historical_hashes(); self.r1_files()
            need(self.ext_snapshot() == self.ext and len(self.ext) == 3810,'All3637 package+173 core objects must reconcile')
            specs = {s['key']:s for s in self.required_specs()}
            if self.phase == 'local-continuation':
                for name in (E.P/'plan-r1/rebuild-order.txt').read_text().splitlines():
                    s = self.local[name]; specs['local:'+name] = self.spec('local:'+name,name.replace('/','_'),name,s['source_sha256'],s['local_imports'],s['external_imports'])
            need(set(self.success) == set(specs),'Final unique required success set differs')
            need(len({r['id'] for r in self.history}) == len(self.history),'Duplicate history identity')
            passes = [r for r in self.history if r['status'] in {'PASSED_REUSED','PASSED_NEW'}]
            need(len(passes) == len(self.success) and {r['key'] for r in passes} == set(self.success),'History does not preserve exactly the required successes')
            for item in self.history:
                need(item['status'] in {'PASSED_REUSED','PASSED_NEW','HOST_COLLISION_RETAINED','HOST_DEFERRED_NO_NATIVE'},'Nonretryable failure cannot produce aggregate success')
                if item['native_started']:
                    need(sha(Path(item['record_path'])) == item['record_sha256'],'Historical native receipt changed')
                    self.receipt(load(Path(item['record_path'])),specs[item['key']],item['status'] in {'PASSED_REUSED','PASSED_NEW'})
                else:need(item['status'] == 'HOST_DEFERRED_NO_NATIVE' and not list(Path(item['call_directory']).rglob('child.json')),'Deferred call was actually native')
            for name,r in self.records.items():
                s = self.local[name]; self.dependencies(s['local_imports'],s['external_imports'])
                need(set(r['direct_local_object_sha256']) == set(s['local_imports']),'Final local prerequisite contract differs')
                r['direct_external_object_sha256'] = {d:self.ext[d]['object_sha256'] for d in s['external_imports']}
            for path,value in [('external-final.json',self.ext),('local-records.json',self.records),('successes.json',self.success),('source-final.json',self.frozen_source)]:save(self.root_out/path,value)
            counts = collections.Counter(r['status'] for r in self.history)
            files = [{'path':str(p.relative_to(self.root_out)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(self.root_out.rglob('*')) if p.is_file()]
            save(self.root_out/'FILE-MANIFEST.json',files)
            result = {'passed':True,'phase':self.phase,'head':HEAD,'tree':str(E.TREE),'coordinator_sha256':self.coordinator_sha,'engine_sha256':ENGINE_SHA,'finished_utc':E.now(),'file_manifest_sha256':sha(self.root_out/'FILE-MANIFEST.json'),'R1_input_manifest_sha256':R1_PINS_SHA,'R1_successes_reused':2,'R1_failed_attempts_retained':1,'history_status_counts':dict(counts),'native_attempts_in_history':sum(r['native_started'] for r in self.history),'successful_native_attempts_in_history':counts['PASSED_REUSED']+counts['PASSED_NEW'],'required_bootstrap_successes':36,'required_fresh_local_successes':638 if self.phase=='local-continuation' else 0,'validated_local_objects':len(self.records),'external_package_objects':3637,'toolchain_object_leaves':173,'warm_G06_objects':437,'S2_objects_borrowed':0,'cold_full_library_run':False,'not_an_old_R1_RESULT':True,'execution_scope':scope_metadata(),'bootstrap_coordinator_sha256':BOOT_COORDINATOR_SHA,'host_only_retry_policy':'exact HOST_COLLISION or exact prelaunch HOST_DEFERRED; never source/setup/resource/pin/marker/signal errors'}
            if self.phase == 'local-continuation':result['bootstrap_aggregate_sha256'] = sha(BOOT/'RESULT.json')
            save(self.root_out/'RESULT.json',result); print(json.dumps(result,indent=2),flush=True)
    return Coordinator


def main():
    need(len(sys.argv) == 2 and sys.argv[1] == 'local','This reviewed parallel successor is local-only')
    need(Path.cwd().resolve() == W and Path(__file__).resolve() == SELF and sha(ENGINE) == ENGINE_SHA and sha(R1_PINS) == R1_PINS_SHA,'Wrong coordinator/engine/inputs')
    need(sha(APPROVAL) == APPROVAL_SHA and sha(A/APPROVAL.name) == APPROVAL_SHA,'Missing exact user parallel ruling')
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('pinned_g06_engine64b',ENGINE); E = importlib.util.module_from_spec(spec); spec.loader.exec_module(E)
    phase = 'local-continuation'; out = LOCAL
    need(not out.exists(),'Fresh continuation output required; no reuse of a stopped phase')
    out.mkdir(); lease = {'runner_pid':os.getpid(),'phase':phase,'head':HEAD,'coordinator_sha256':sha(SELF),'utc':E.now(),'execution_scope':scope_metadata()}; owned = False
    def stop_signal(signum,_frame):raise InterruptedError('Coordinator received signal '+str(signum))
    previous = {s:signal.signal(s,stop_signal) for s in (signal.SIGTERM,signal.SIGHUP)}
    try:
        save(E.LEASE,lease); owned = True; save(out/'START.json',lease)
        run = coordinator_class(E)(phase,out); run.validate_frozen_inputs(); run.validate_sources(); run.r1_files()
        save(out/'source-start.json',run.frozen_source); save(out/'resources-start.json',E.resources())
        E.native_processes = own_tree_processes  # Explicit approved scope override, not global host exclusion.
        E.wait_idle = run.adaptive_idle
        run.local_continuation()
        run.finish_continuation()
    except BaseException as exc:
        save(out/'STOP.json',{'utc':E.now(),'phase':phase,'error':repr(exc),'all_prior_attempts_retained':True,'automatic_retry_of_this_error':False}); raise
    finally:
        if owned:
            need(load(E.LEASE) == lease,'Own lease changed; never remove another lease'); E.LEASE.unlink()
        for s,handler in previous.items():signal.signal(s,handler)


if __name__ == '__main__':main()
