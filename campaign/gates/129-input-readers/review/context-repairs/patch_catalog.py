from pathlib import Path
import re,ast,json,difflib
O=Path(__file__).parent;h=O/'helpers/declfreeze.py';t=ast.parse(h.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(h),'exec'),ns);path='TCSlib/Complexity/TuringMachine/Build/Catalog.lean';f=O/'source/CANDIDATE'/(path+'.txt');s=f.read_text();original=s
bodies={
'Turing.step_of_inputMoveAction': '''
  rw [MultiTapeTM.step_of_some hq, htr]
  apply Cfg.ext
  · simp only [Action.apply_state, inputMoveAction_eq]
  · simp only [Action.apply_inputPos, inputMoveAction_eq]
  · funext j
    rw [Action.apply_workTapes, inputMoveAction_eq, Option.getD_none,
      Cfg.workTapeSymbols_eq, Function.update_eq_self]
  · funext j
    simp only [Action.apply_workTapePos, inputMoveAction_eq, SignType.coe_zero, add_zero]
  · simp only [Action.apply_output, inputMoveAction_eq, Option.toList_none, List.append_nil]''',
'Turing.step_of_tapeAction_move': '''
  rw [MultiTapeTM.step_of_some hq, htr]
  apply Cfg.ext
  · simp only [Action.apply_state, tapeAction]
  · simp only [Action.apply_inputPos, tapeAction]
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    by_cases hj : j = i
    · subst j
      simp only [tapeAction, ↓reduceIte, Option.getD_none, Function.update_eq_self]
    · simp only [tapeAction, hj, ↓reduceIte, Option.getD_none, Function.update_eq_self]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [Action.apply_workTapePos, tapeAction, ↓reduceIte, Function.update_self]
    · simp only [Action.apply_workTapePos, tapeAction, hj, ↓reduceIte, SignType.coe_zero,
        add_zero, Function.update_of_ne hj]
  · simp only [Action.apply_output, tapeAction, Option.toList_none, List.append_nil]''',
'Turing.step_of_tapeAction_write': '''
  rw [MultiTapeTM.step_of_some hq, htr]
  apply Cfg.ext
  · simp only [Action.apply_state, tapeAction]
  · simp only [Action.apply_inputPos, tapeAction]
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    by_cases hj : j = i
    · subst j
      simp only [tapeAction, ↓reduceIte, Option.getD_some, Function.update_self]
    · simp only [tapeAction, hj, ↓reduceIte, Option.getD_none, Function.update_eq_self,
        Function.update_of_ne hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [Action.apply_workTapePos, tapeAction, ↓reduceIte, Function.update_self]
    · simp only [Action.apply_workTapePos, tapeAction, hj, ↓reduceIte, SignType.coe_zero,
        add_zero, Function.update_of_ne hj]
  · simp only [Action.apply_output, tapeAction, Option.toList_none, List.append_nil]'''}
for name,body in bodies.items():
 n,pr,c=next(x for x in ns['chunks'](s) if x[0]==name);idx=c.index(':= by')+len(':= by');new=c[:idx]+body;assert s.count(c)==1;s=s.replace(c,new,1);d=O/'targets'/name.rsplit('.',1)[-1];d.mkdir(parents=True,exist_ok=True);(d/'BASE.lean.txt').write_text(c+'\n');(d/'CANDIDATE.lean.txt').write_text(new+'\n')
f.write_text(s);(O/'runtime/project-CANDIDATE'/path).write_text(s);(O/'Catalog-three-readers.patch').write_text(''.join(difflib.unified_diff(original.splitlines(keepends=True),s.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path)));print('Prepared exact3 Catalog step-reader bodies, preserving every header and all outside bytes.')
