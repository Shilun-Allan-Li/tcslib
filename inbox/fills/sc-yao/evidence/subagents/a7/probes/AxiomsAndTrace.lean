import evidence.subagents.a7.probes.ConcreteData
import Lean

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Lean Elab Command

partial def scYaoA7Closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then scYaoA7Closure env rest seen else
      let deps := match env.find? name with
        | none => []
        | some ci => ci.getUsedConstantsAsSet.toList
      scYaoA7Closure env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let modules := #[`evidence.subagents.a7.probes.ConcreteData]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        count := count + 1
        logInfo m!"SIGNATURE\t{name}\t{ci.type}"
        let axioms ← collectAxioms name
        logInfo m!"AXIOMS\t{name}\t{axioms.qsort Name.lt}"
        let closure := scYaoA7Closure env [name] {}
        let mut sorried : Array Name := #[]
        for dependency in closure.toList do
          if let some dependencyInfo := env.find? dependency then
            if dependencyInfo.getUsedConstantsAsSet.contains ``sorryAx then
              sorried := sorried.push dependency
        logInfo m!"SORRY_CLOSURE\t{name}\t{sorried.qsort Name.lt}"
  logInfo m!"STORED_CONSTANTS {count}"
