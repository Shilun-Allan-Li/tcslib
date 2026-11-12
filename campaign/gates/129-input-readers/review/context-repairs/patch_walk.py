from pathlib import Path
import ast,re
O=Path(__file__).parent;h=O/'helpers/declfreeze.py';t=ast.parse(h.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(h),'exec'),ns);path='TCSlib/Complexity/TuringMachine/Build/Catalog.lean';p=O/'source/CANDIDATE'/(path+'.txt');s=p.read_text();n,priv,c=next(x for x in ns['chunks'](s) if x[0]=='Turing.walkTM_run_ofCfg');new=c.replace('simp only [MultiTapeTM.step, hst, htr]','rw [MultiTapeTM.step_of_some hst, htr]',1)
old='''    apply Cfg.ext
    · rfl
    · simp [Action.apply, F, moveInputPos_zero]
    · funext j
      by_cases hj : moved j <;> simp [Action.apply, F, hj]
    · funext j
      by_cases hj : moved j
      · simp only [Action.apply, F, hj, if_true]
        push_cast
        ring
      · simp [Action.apply, F, hj]
    · simp [Action.apply, F]'''
repl='''    apply Cfg.ext
    · simp only [Action.apply_state]
    · simp only [Action.apply_inputPos, F, moveInputPos_zero]
    · funext j
      rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
      by_cases hj : moved j
      · simp only [F, hj, if_true, Option.getD_none, Function.update_eq_self]
      · simp only [F, hj, if_false, Option.getD_none, Function.update_eq_self]
    · funext j
      by_cases hj : moved j
      · simp only [Action.apply_workTapePos, F, hj, if_true]
        push_cast
        ring
      · simp only [Action.apply_workTapePos, F, hj, if_false, SignType.coe_zero, add_zero]
    · simp only [Action.apply_output, F, Option.toList_none, List.append_nil]'''
assert new.count(old)==1;new=new.replace(old,repl,1).replace('simp [F, Cfg.workTapeSymbols, hsrc]','simp [F, Cfg.workTapeSymbols_eq, hsrc]',1).replace('simp [FinTM.bufferTape, List.getElem?_eq_getElem hr]','simp [FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]',1).replace('simp [FinTM.bufferTape]','simp [FinTM.bufferTape_nat]',1);assert s.count(c)==1;out=s.replace(c,new,1);p.write_text(out);(O/'runtime/project-CANDIDATE'/path).write_text(out);d=O/'targets/walkTM_run_ofCfg';d.mkdir(parents=True,exist_ok=True);(d/'BASE.lean.txt').write_text(c+'\n');(d/'CANDIDATE.lean.txt').write_text(new+'\n');print('Prepared one complete walk target: same live-step inline prefix plus existing action/work-symbol/buffer readers; arithmetic unchanged.')
