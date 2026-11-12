from pathlib import Path
import json,re,subprocess,hashlib
O=Path(__file__).parent;C=json.loads((O/'CONTEXT.json').read_text());W=Path(C['private_source_tree']);R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest();body=(O/'MetadataBody.lean.txt').read_text();(O/'probes').mkdir(exist_ok=True)
roots=['Turing.Action.apply_workTapes','Turing.FinTM.controlAction_apply']
for tag,module,selected in [('BASE-metadata','Simulation',roots),('OWNER-metadata','Configuration',roots[:1]),('SIMULATION-metadata','Simulation',roots)]:
 s='import Lean\nimport TCSlib.Complexity.TuringMachine.'+module+'\n'+body.replace('ROOTS','['+', '.join('`'+x for x in selected)+']');(O/'probes'/(tag+'.lean.txt')).write_text(s)
explicit='''import TCSlib.Complexity.TuringMachine.Configuration
set_option maxHeartbeats 0
#check @Turing.Action.apply_workTapes
#print axioms Turing.Action.apply_workTapes
example {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (a : Turing.Action k Symbol State) (c : Turing.Cfg k Symbol State input) (i : Fin k) :
    (a.apply c).workTapes i =
      Function.update (c.workTapes i) (c.workTapePos i)
        ((a.workTapes i).1.getD (c.workTapeSymbols i)) :=
  @Turing.Action.apply_workTapes k Symbol State input a c i
'''
(O/'probes'/'OWNER-explicit-arguments.lean.txt').write_text(explicit)
# Exact current-source TCSlib import closure and unchanged MAC8 imported source bindings.
base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';g('cat-file','-e',base+'^{commit}');todo=['TCSlib.Complexity.TuringMachine.Simulation'];seen=set();rows=[]
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);path=m.replace('.','/')+'.lean';data=(W/path).read_bytes();imps=re.findall(r'^import\s+(\S+)',data.decode(),re.M);tc=[x for x in imps if x.startswith('TCSlib.')];todo.extend(tc);old=g('show',base+':'+path);rows.append({'module':m,'path':path,'source_SHA256':H(data),'MAC8_SHA256':H(old),'source_exact_MAC8':data==old,'imports':imps})
assert all(r['source_exact_MAC8'] for r in rows if not r['module'].endswith('.Simulation'))
(O/'IMPORT-CONTEXT.json').write_text(json.dumps({'source':C['source'],'MAC8_source':base,'current_Simulation_TCSlib_import_closure':sorted(rows,key=lambda r:r['module']),'all_imported_TCSlib_sources_other_than_Simulation_exact_MAC8':True,'Configuration_has_no_TCSlib_imports':not any(x.startswith('TCSlib.') for x in next(r for r in rows if r['module'].endswith('.Configuration'))['imports']),'no_new_import_proposed':True},indent=2)+'\n')
# Retain every source occurrence of the selected name in the actual #251 source tree.
hits=[]
for p in sorted((W/'TCSlib').rglob('*.lean')):
 for i,l in enumerate(p.read_text().splitlines()):
  if 'apply_workTapes' in l:hits.append({'path':str(p.relative_to(W)),'line':i+1,'text':l})
(O/'EXISTING-NAME-HITS.json').write_text(json.dumps(hits,ensure_ascii=False,indent=2)+'\n');print('Prepared probes and current source closure:',len(rows),'modules;',len(hits),'uncapped name hits')
