#!/usr/bin/env python3
"""Collect all explicit rewrite/unfold arguments, including Core and Mathlib names."""
import importlib.util
import json
from pathlib import Path
import re
spec=importlib.util.spec_from_file_location('headers','evidence/tools/check_headers.py')
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
spec2=importlib.util.spec_from_file_location('unfold_args','evidence/tools/unfold_arguments.py')
u=importlib.util.module_from_spec(spec2);spec2.loader.exec_module(u)
rows=[]
for file in Path('evidence/source-files.txt').read_text().splitlines():
 code,_=h.lex(Path(file).read_text())
 for offset,tactic,token in u.arguments(code):
  rows.append(dict(file=file,line=code[:offset].count('\n')+1,
                   tactic=tactic,argument=token))
root=Path('evidence/unfold');root.mkdir(parents=True,exist_ok=True)
(root/'all-explicit-arguments.json').write_text(json.dumps(rows,indent=2)+'\n')
names=sorted({r['argument'].split('.')[-1]for r in rows})
# JSON strings have the same escaping needed for these simple Lean identifier strings.
wanted=', '.join(json.dumps(s,ensure_ascii=False)for s in names)
probe='''import TCSlib.Cryptography.SecureComputation
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : Array String := #[WANTED]
  for (name, ci) in env.constants.toList do
    if let .defnInfo _ := ci then
      let short := (name.toString.splitOn ".").getLast!
      if wanted.contains short then
        let home := match env.getModuleIdxFor? name with
          | some idx => env.header.moduleNames[idx.toNat]!.toString
          | none => "<current>"
        logInfo m!"DEFINITION\\t{home}\\t{name}"
'''.replace('WANTED',wanted)
Path('evidence/probes/ExplicitUnfoldMeta.lean').write_text(probe)
print('Prepared Core/Mathlib/TCSlib probe for',len(names),'argument suffixes')
