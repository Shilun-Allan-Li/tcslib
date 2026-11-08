from pathlib import Path
import ast,re
O=Path(__file__).parent;h=O/'helpers/declfreeze.py';t=ast.parse(h.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(h),'exec'),ns);path='TCSlib/Complexity/TuringMachine/Build/Scan.lean';p=O/'source/CANDIDATE'/(path+'.txt');s=p.read_text();n,pr,c=next(x for x in ns['chunks'](s) if x[0]=='Turing.scan_fold_trace');new=c.replace('''  · have hs : (scanFoldF δ a₀ d x.length).inputSymbol = none := by
      simp [Cfg.inputSymbol, scanFoldF]''','''  · have hs : (scanFoldF δ a₀ d x.length).inputSymbol = none := by
      apply Cfg.inputSymbol_of_end
      simp [scanFoldF]''',1).replace('''  · have hs : (scanFoldR δ a₀ d 0).inputSymbol = none := by
      simp [Cfg.inputSymbol, scanFoldR]''','''  · have hs : (scanFoldR δ a₀ d 0).inputSymbol = none := by
      apply Cfg.inputSymbol_of_zero
      simp [scanFoldR]''',1);assert new!=c and 'simp [Cfg.inputSymbol,' not in new;out=s.replace(c,new,1);p.write_text(out);(O/'runtime/project-CANDIDATE'/path).write_text(out);d=O/'targets/scan_fold_trace';d.mkdir(parents=True,exist_ok=True);(d/'BASE.lean.txt').write_text(c+'\n');(d/'CANDIDATE.lean.txt').write_text(new+'\n');print('Prepared one complete Scan proof with exact boundary-input readers; all other bytes preserved.')
