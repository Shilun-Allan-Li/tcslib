import evidence.subagents.c.simulator_assembly.probes.FullSimulators
import Lean

open Lean Elab Command

partial def assemblyClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then assemblyClosure env rest seen else
      let deps := match env.find? name with
        | none => []
        | some ci => ci.getUsedConstantsAsSet.toList
      assemblyClosure env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let name := `TCSlib.Cryptography.SecureComputation.YaoFullSimulatorProbe.simulators_skeleton
  let axioms ← collectAxioms name
  logInfo m!"AXIOMS\t{name}\t{axioms.qsort Name.lt}"
  let closure := assemblyClosure env [name] {}
  let mut admissions : Array Name := #[]
  for dependency in closure.toList do
    if let some ci := env.find? dependency then
      if ci.getUsedConstantsAsSet.contains ``sorryAx then
        admissions := admissions.push dependency
  logInfo m!"SORRY_CLOSURE\t{name}\t{admissions.qsort Name.lt}"
  logInfo m!"DEPENDENCY_COUNT {closure.toList.length}"

  let expected := [
    `TCSlib.Cryptography.SecureComputation.yaoSeed_good_whp,
    `TCSlib.Cryptography.SecureComputation.YaoFullSimulatorProbe.simulators_skeleton]
  unless admissions.toList.qsort Name.lt == expected.qsort Name.lt do
    throwError "Unexpected admission closure: {admissions}"
  if closure.contains `TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators then
    throwError "Forbidden dependency on the old simulator theorem"
  logInfo "EXPECTED_ADMISSIONS_ONLY; OLD_SIMULATOR_ABSENT"
