from pathlib import Path
import json,ast,re,hashlib,difflib
O=Path(__file__).parent;helper=O/'helpers/declfreeze.py';t=ast.parse(helper.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(helper),'exec'),ns);path='TCSlib/Complexity/TuringMachine/Simulation.lean';p=O/'source/CANDIDATE'/(path+'.txt');s=p.read_text();name='Turing.FinTM.controlAction_apply';n,priv,c=next(x for x in ns['chunks'](s) if x[0]==name);at=c.index(':= by')+len(':= by');new=c[:at]+'''
  apply Cfg.ext
  · rw [Action.apply_state, controlAction_def]
  · rw [Action.apply_inputPos, controlAction_def]
  · funext i
    rw [Action.apply_workTapes, controlAction_def, Option.getD_none,
      Cfg.workTapeSymbols_eq, Function.update_eq_self]
  · funext i
    simp only [Action.apply_workTapePos, controlAction_def, SignType.coe_zero, add_zero]
  · simp only [Action.apply_output, controlAction_def, Option.toList_none, List.append_nil]''';assert s.count(c)==1;out=s.replace(c,new,1);assert out.replace(new,c,1)==s;p.write_text(out);(O/'runtime/project-CANDIDATE'/path).write_text(out);d=O/'targets/controlAction_apply';d.mkdir(parents=True,exist_ok=True);(d/'BASE.lean.txt').write_text(c+'\n');(d/'CANDIDATE.lean.txt').write_text(new+'\n');(d/'body-only.patch').write_text(''.join(difflib.unified_diff(s.splitlines(keepends=True),out.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path)));print('Prepared one mechanical private controlAction_apply body; literal doc/header and all other bytes exact.')
