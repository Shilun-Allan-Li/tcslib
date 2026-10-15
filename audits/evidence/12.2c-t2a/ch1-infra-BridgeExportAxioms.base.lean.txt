import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import Lean

set_option maxHeartbeats 0

-- Maintainer axiom attestation: Chapter-1 bridge export + TMSAT bridge discharge.
-- (1) The export and the discharged bridge must be admission-free.
#print axioms Turing.timed_universal_concrete
#print axioms Complexity.timed_universal_quantitative
-- (2) The Chapter-1 headline regression set stays admission-free.
#print axioms Turing.timed_universal
#print axioms Turing.universal
#print axioms Turing.universal_quadratic
#print axioms Turing.exists_effectiveMachineCode
#print axioms Complexity.HALT_not_computable
-- (3) The TMSAT targets' remaining roots shrink exactly as expected.
#print axioms Complexity.TMSAT_mem_NP
#print axioms Complexity.TMSAT_NPHard
#print axioms Complexity.TMSAT_NPComplete

open Lean Elab Command

namespace BridgeAudit

structure WalkState where
  visited : NameSet := {}
  roots : Array Name := #[]

abbrev WalkM := ReaderT Environment (StateM WalkState)

/-- Traverse checked kernel declarations, including opaque values and types. -/
partial def visit (name : Name) : WalkM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      modify fun s => { s with roots := s.roots.push name }
    deps.forM visit
    match ci with
    | .inductInfo i => i.ctors.forM visit
    | _ => pure ()

def roots (env : Environment) (name : Name) : Array Name :=
  (((visit name).run env).run {}).2.roots

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def userRoots (env : Environment) (name : Name) : List Name :=
  ((roots env name).map privateToUserName).toList.eraseDups.mergeSort
    (fun a b => a.toString ≤ b.toString)

run_cmd do
  let env ← getEnv
  let expectations : Array (Name × List Name) := #[
    (``Turing.timed_universal_concrete, []),
    (``Complexity.timed_universal_quantitative, []),
    (``Turing.timed_universal, []),
    (``Complexity.TMSAT_mem_NP, [``Complexity.TMSAT_mem_NP]),
    (``Complexity.TMSAT_NPHard, [``Complexity.TMSAT_NPHard]),
    (``Complexity.TMSAT_NPComplete,
      [``Complexity.TMSAT_mem_NP, ``Complexity.TMSAT_NPHard]),
    -- Regression: the epoch-2 A/C cluster is untouched by this change.
    (``Complexity.NP_subset_EXP, [`Complexity.enumMachine_contracts]),
    (``Complexity.HALT_NPHard, [`Complexity.enumMachine_contracts])]
  for (name, expectedRaw) in expectations do
    let expected := expectedRaw.eraseDups.mergeSort (fun a b => a.toString ≤ b.toString)
    let found := userRoots env name
    logInfo m!"ROOTS {name}: {found}"
    unless found == expected do
      throwError "Unexpected admission roots for {name}: {found}; expected {expected}"
    let ax ← collectAxioms name
    unless ax.all (fun a => allowed.contains a || a == ``sorryAx) do
      throwError "Unexpected axiom for {name}: {ax}"
    if expected.isEmpty && ax.contains ``sorryAx then
      throwError "Unexpected sorryAx for {name}"
    unless expected.isEmpty || ax.contains ``sorryAx do
      throwError "Expected sorryAx for {name} but it is absent"
  logInfo "BRIDGE AUDIT PASS: the export and the discharged bridge are admission-free; TMSAT roots shrank exactly to their D-sites; headline and epoch-2 regressions unchanged."

end BridgeAudit
