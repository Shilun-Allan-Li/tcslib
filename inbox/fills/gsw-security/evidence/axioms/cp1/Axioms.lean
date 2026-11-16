import TCSlib.Cryptography.Hashing.SIS.Columns
import Lean

set_option maxHeartbeats 0

#print axioms TCSlib.Cryptography.Hashing.SIS.hashColumns_eq_mul
#print axioms TCSlib.Cryptography.Hashing.SIS.distAdv_hashColumns_uniform_le
#print axioms TCSlib.Cryptography.Hashing.SIS.hashColumns
#print axioms TCSlib.Cryptography.Hashing.SIS.hashColumns_apply

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[`TCSlib.Cryptography.Hashing.SIS.Columns]
  let targets : Array Name := #[`TCSlib.Cryptography.Hashing.SIS.hashColumns_eq_mul, `TCSlib.Cryptography.Hashing.SIS.distAdv_hashColumns_uniform_le, `TCSlib.Cryptography.Hashing.SIS.hashColumns, `TCSlib.Cryptography.Hashing.SIS.hashColumns_apply]
  let mut stored : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if mods.contains env.header.moduleNames[idx.toNat]! then stored := stored.push n
  stored := stored.qsort Name.lt
  logInfo m!"STORED {stored.size}"
  for n in stored do
    let axs ← liftCoreM <| collectAxioms n
    logInfo m!"AXIOMS {n} {(axs.qsort Name.lt).toList}"
  for t in targets do
    unless env.contains t do throwError "unknown target {t}"
    let mut visited : NameSet := {}
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
    logInfo m!"TRACE {t} visited={visited.size} sorried={(sorried.qsort Name.lt).toList}"
