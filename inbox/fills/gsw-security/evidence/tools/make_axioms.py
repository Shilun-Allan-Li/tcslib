"""Axiom prints and a dependency trace for the gsw-security targets (python3 -I).

Usage (from the fill checkout root): make_axioms.py <phase> <module> [<module> ...] -- <target> ...
Writes probes/axioms/<phase>/Axioms.lean, which imports the modules and
  * `#print axioms` each target;
  * prints `AXIOMS <name> <axioms>` (Lean.collectAxioms) for every stored constant whose home
    module is one of the given (changed) modules, auxiliary constants included;
  * for each target walks the constant closure (types and values, theorems included) and prints
    `TRACE <target> visited=<n> sorried=[...]`: every reached constant whose type or value
    mentions `sorryAx` directly, so a `sorry` anywhere upstream is named.
"""
from pathlib import Path
import sys

args = sys.argv[1:]
phase = args[0]
sep = args.index('--')
mods, targets = args[1:sep], args[sep + 1:]
imports = ''.join(f'import {m.replace("/", ".")}\n' for m in mods)
modnames = ', '.join(f'`{m.replace("/", ".")}' for m in mods)
tnames = ', '.join(f'`{t}' for t in targets)
prints = ''.join(f'#print axioms {t}\n' for t in targets)
src = f'''{imports}import Lean

set_option maxHeartbeats 0

{prints}
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[{modnames}]
  let targets : Array Name := #[{tnames}]
  let mut stored : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if mods.contains env.header.moduleNames[idx.toNat]! then stored := stored.push n
  stored := stored.qsort Name.lt
  logInfo m!"STORED {{stored.size}}"
  for n in stored do
    let axs ← liftCoreM <| collectAxioms n
    logInfo m!"AXIOMS {{n}} {{(axs.qsort Name.lt).toList}}"
  for t in targets do
    unless env.contains t do throwError "unknown target {{t}}"
    let mut visited : NameSet := {{}}
    let mut stack : Array Name := #[t]
    let mut sorried : Array Name := #[]
    while !stack.isEmpty do
      let n := stack.back!
      stack := stack.pop
      if visited.contains n then continue
      visited := visited.insert n
      let some ci := env.find? n | continue
      let uses := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      if uses.contains ``sorryAx then sorried := sorried.push n
      for u in uses do
        unless visited.contains u do stack := stack.push u
    logInfo m!"TRACE {{t}} visited={{visited.size}} sorried={{(sorried.qsort Name.lt).toList}}"
'''
out = Path('probes/axioms') / phase
out.mkdir(parents=True, exist_ok=True)
(out / 'Axioms.lean').write_text(src)
print(out / 'Axioms.lean')
