import evidence.subagents.a12.probes.CompleteSimulators
import Lean

open Lean Elab Command

partial def completeAssemblyClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then completeAssemblyClosure env rest seen else
      let deps := match env.find? name with
        | none => []
        | some ci => ci.getUsedConstantsAsSet.toList
      completeAssemblyClosure env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let name := `TCSlib.Cryptography.SecureComputation.YaoCompleteSimulatorProbe.simulators_complete
  let axioms ← collectAxioms name
  logInfo m!"AXIOMS\t{name}\t{axioms.qsort Name.lt}"
  let closure := completeAssemblyClosure env [name] {}
  let mut admissions : Array Name := #[]
  for dependency in closure.toList do
    if let some ci := env.find? dependency then
      if ci.getUsedConstantsAsSet.contains ``sorryAx then
        admissions := admissions.push dependency
  logInfo m!"SORRY_CLOSURE\t{name}\t{admissions.qsort Name.lt}"
  logInfo m!"DEPENDENCY_COUNT {closure.toList.length}"
  logInfo m!"USES_OLD_TARGET {closure.contains `TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators}"
