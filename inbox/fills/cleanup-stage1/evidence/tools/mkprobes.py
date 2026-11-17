#!/usr/bin/env python3
"""mkprobes.py <targets.tsv> <outdir-in-clone>   (cleanup-stage1)

Writes two probe modules for the 69 new constants (checks 3 and 4):
  * Probes/StmtDump.lean: imports the 19 homes (17 changed owners and 2 new modules) and prints, for
    every new constant, `STMT <full name> | <kind> | <type>` (pp.fullNames, pp.universes off,
    width 1000) from the environment, failing if a constant is missing;
  * Probes/Axioms.lean: the same imports and `#print axioms <full name>` for every new constant.
"""
import os, sys

tsv, outdir = sys.argv[1:3]
T = [l.rstrip('\n').split('\t') for l in open(tsv) if l.strip()]
homes = sorted({t[4][:-5].replace('/', '.') for t in T})
imports = ''.join(f'import {h}\n' for h in homes)
names = [t[1] for t in T]
os.makedirs(outdir, exist_ok=True)
lst = ',\n    '.join('`' + n for n in names)
open(os.path.join(outdir, 'StmtDump.lean'), 'w').write(f"""import Lean
{imports}
/-! cleanup-stage1 StmtDump: every new constant with its full name, kind and type. -/

open Lean Elab Command Meta

set_option pp.fullNames true
set_option pp.universes false

run_cmd do
  let env ← getEnv
  let names : List Name := [
    {lst}]
  for n in names do
    let some c := env.find? n | throwError "missing constant {{n}}"
    let kind := match c with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | _ => "other"
    let fmt ← liftTermElabM <| withOptions (fun o => o.setNat `format.width 1000) <| ppExpr c.type
    IO.println s!"STMT {{n}} | {{kind}} | {{isProtected env n}} | {{fmt.pretty 1000}}"
  IO.println s!"STMT-COUNT {{names.length}}"
""")
open(os.path.join(outdir, 'Axioms.lean'), 'w').write(
    'import Lean\n' + imports + '\n/-! cleanup-stage1 axioms of every new constant. -/\n\n' +
    ''.join(f'#print axioms {n}\n' for n in names))
print(len(names), 'constants;', len(homes), 'homes')
