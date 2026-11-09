"""Own static/data-only guard review; no reviewed imports/process execution."""
from pathlib import Path
import ast,hashlib,json

W=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
A=W/'.lake/ps-maintainer/gate06-combined-20261108';P=A/'native-rule10-guard-r3';OUT=P/'peer-api'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def need(t,m):
 if not t:raise AssertionError(m)
def main():
 need(sha(P/'PROPOSAL-MANIFEST.json')=='18a9859d3cbca4da2b4e79643c2f641ae2434221c42123ea9608a9f0c3116011','proposal manifest')
 manifest=load(P/'PROPOSAL-MANIFEST.json')
 for r in manifest['files']:
  p=P/r['path'];need(p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'frozen proposal leaf')
 raw=(P/'guard_native_command_r3.py').read_text();t=ast.parse(raw)
 need(sha(P/'guard_native_command_r3.py')=='6775ba1b6f7480d94930c18e036b23611dc84e5e7fbf9f55092b4f2560d5fabb','final guard hash')
 constants={n.targets[0].id:ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and isinstance(n.value,ast.Constant)}
 pinpaths={'ENGINE':A/'native-runtime-proposal/run_combined_native.py','PARALLEL':A/'native-runtime-parallel-r1/continue_native.py','APPROVAL':A/'user-rulings-20261108-r1.json','SETUP':A/'rule10-prep/proposed-tools/setup-summary.json'}
 for k,p in pinpaths.items():need(sha(p)==constants[k+'_SHA'],'pinned '+k)
 allowed=next(n.value for n in t.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='ALLOWED')
 need(len(allowed.keys)==2,'only two allowed tools')
 toolnames=['check_probe_v2.py','run_gate06_final_native.py']
 for name,d in zip(toolnames,allowed.values):need(sha(A/'rule10-prep/proposed-tools'/name)==ast.literal_eval(d),'allowed tool bytes')
 need(sha(A/'native-bootstrap-r1/source-start.json')==constants['SOURCE_SHA'],'full frozen source inventory pin')
 nodes=[n for n in ast.walk(t) if isinstance(n,ast.Call)]
 pops=[n for n in nodes if ast.unparse(n.func)=='subprocess.Popen'];need(len(pops)==1,'one child launch')
 need(any(k.arg=='start_new_session' and isinstance(k.value,ast.Constant) and k.value.value is True for k in pops[0].keywords),'separate child session')
 need(not any(ast.unparse(n.func) in {'os.kill','os.killpg'} for n in nodes),'no direct/inventory signal sites')
 cleanup=[n for n in nodes if ast.unparse(n.func)=='E.Run.stop_own_group']
 need(len(cleanup)==2 and all([ast.unparse(x) for x in n.args]==['None','proc'] for n in cleanup),'cleanup only own child object')
 stages=[ast.literal_eval(n.args[0]) for n in nodes if ast.unparse(n.func)=='validate_all' and n.args]
 need(set(stages)=={'initial','after-idle-prelaunch','after-child'} and len(stages)==3,'three full integrity stages')
 terminal=next(n for n in nodes if ast.unparse(n.func)=='save' and n.args and 'child-terminal.json' in ast.unparse(n.args[0]))
 after=next(n for n in nodes if ast.unparse(n.func)=='validate_all' and n.args and ast.literal_eval(n.args[0])=='after-child')
 result=next(n for n in nodes if ast.unparse(n.func)=='save' and n.args and 'RESULT.json' in ast.unparse(n.args[0]))
 need(terminal.lineno<after.lineno<result.lineno,'terminal preserved before postvalidation/result')
 need('return 2 if interrupted is not None else rc' in raw,'ordinary child rc not interpreted')
 # These two reviewed child tools retain the outer guard process group.
 child_launches=[]
 for name in toolnames:
  tt=ast.parse((A/'rule10-prep/proposed-tools'/name).read_text())
  for n in ast.walk(tt):
   if isinstance(n,ast.Call) and ast.unparse(n.func) in {'subprocess.Popen','subprocess.run'}:
    need(not any(k.arg in {'start_new_session','process_group'} for k in n.keywords),'child tool does not split PGID')
    child_launches.append({'tool':name,'line':n.lineno,'call':ast.unparse(n.func)})
 data={'status':'STATIC_AST_AND_PIN_CHECK_PASS_NO_GUARD_EXECUTION','guard_sha256':sha(P/'guard_native_command_r3.py'),'proposal_manifest_sha256':sha(P/'PROPOSAL-MANIFEST.json'),'source_head':constants['HEAD'],'input_pins':{k:sha(p) for k,p in pinpaths.items()},'source_inventory_sha256':constants['SOURCE_SHA'],'allowed_tools':toolnames,'full_validation_stages':stages,'child_session_inheritance':child_launches,'future_LOCAL_receipt_not_consumed':True,'programs_imported_or_executed':False,'native_or_process_simulation':False}
 with (OUT/'validation.json').open('x') as f:json.dump(data,f,indent=2);f.write('\n')
 print(json.dumps({'status':data['status'],'validation_sha256':sha(OUT/'validation.json')}))
if __name__=='__main__':main()
