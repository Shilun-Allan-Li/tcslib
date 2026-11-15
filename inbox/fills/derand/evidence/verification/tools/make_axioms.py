"""Prepare actual-name and axiom census of all stored constants in changed files."""
import sys
from pathlib import Path

phase = sys.argv[1]
modules = sys.argv[2:] or [
    'TCSlib.Complexity.ClassP.DTIME',
    'TCSlib.Complexity.Randomized.Classes',
    'TCSlib.Complexity.Randomized.Build.IterateFind',
    'TCSlib.Complexity.Randomized.SeedMajority',
    'TCSlib.Cryptography.Randomness.Derandomization',
]
mods = modules + ['TCSlib.Complexity.Randomized.Repetition']
src = 'import Lean\n' + ''.join('import ' + m + '\n' for m in mods)
src += '\nset_option maxHeartbeats 0\nset_option maxRecDepth 65536\n\n'
src += 'run_cmd do\n  let env ← Lean.getEnv\n  let modules : List String := ['
src += ', '.join('"' + m + '"' for m in modules) + ']\n'
src += '''  let mut count : Nat := 0
  for (name, ci) in env.constants.toList.toArray.qsort (fun a b => Lean.Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let home := env.header.moduleNames[idx.toNat]!
    unless modules.contains home.toString ||
      name == `Complexity.polyTimeComputable_iterateFind do continue
    let axioms ← Lean.collectAxioms name
    let printed ← Lean.Elab.Command.liftTermElabM <| Lean.PrettyPrinter.ppExpr ci.type
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("home", Lean.toJson home.toString),
      ("type", Lean.toJson (toString printed)),
      ("axioms", Lean.toJson (axioms.toList.map Lean.Name.toString))]
    Lean.logInfo m!"DERAND-AXIOMS {row.compress}"
    count := count + 1
  Lean.logInfo m!"DERAND-AXIOM-COUNT {count}"

#print axioms Complexity.exists_seedMajorityTM
#print axioms Complexity.seedMajority_mem_DTIME
#print axioms TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp
#print axioms Complexity.IterateFind.polyTimeComputable_find
#print axioms Complexity.polyTimeComputable_iterateFind
'''
if phase != 'base':
    src += '''#print axioms Complexity.IterateFind.computesFunInTime_find
#print axioms Complexity.mem_DTIME_iff
#print axioms Turing.FinTM.decidesInTime_iff
#check @Complexity.IterateFind.computesFunInTime_find
#check @Complexity.mem_DTIME_iff
#check @Turing.FinTM.decidesInTime_iff
'''
if 'TCSlib.Cryptography.Randomness.Derandomization' not in modules:
    src = src.replace('#print axioms TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp\n', '')
folder = Path('evidence/axioms') / phase
folder.mkdir(parents=True, exist_ok=True)
(folder / 'Census.lean').write_text(src)
(folder / 'order.txt').write_text(str(folder / 'Census') + '\n')
print(f'Prepared {folder / "Census.lean"}')
