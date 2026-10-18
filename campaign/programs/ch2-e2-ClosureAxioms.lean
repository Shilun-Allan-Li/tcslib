import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import Lean

set_option maxHeartbeats 0

-- Maintainer attestation: B2 integration — epoch-2 closure.
-- Expected: ALL TEN epoch-2 targets (12 printed names: the campaign table's 11
-- plus timed_universal_quantitative) admission-free; Chapter-1 headline and
-- library regressions unchanged; the E3 statement layer untouched at its own
-- roots.

open Lean Elab Command

namespace B2ClosureAudit

structure WalkState where
  visited : NameSet := {}
  roots : Array Name := #[]

abbrev WalkM := ReaderT Environment (StateM WalkState)

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
    -- Epoch-2 targets, all ten closed (12 printed names).
    (``Complexity.NP_subset_EXP, []),
    (``Complexity.HALT_NPHard, []),
    (``Complexity.HALT_not_mem_NP, []),
    (``Complexity.ntime_poly_subset_NP, []),
    (``Complexity.NP_subset_iUnion_NTIME, []),
    (``Complexity.NP_eq_iUnion_NTIME, []),
    (``Complexity.mem_NP_iff_exists_length_le, []),
    (``Complexity.timeConstructible_poly, []),
    (``Complexity.timed_universal_quantitative, []),
    (``Complexity.TMSAT_mem_NP, []),
    (``Complexity.TMSAT_NPHard, []),
    (``Complexity.TMSAT_NPComplete, []),
    -- Chapter-1 headline and library regressions.
    (``Turing.timed_universal, []),
    (``Turing.timed_universal_concrete, []),
    (``Turing.FinTM.exists_loopCfgTM, []),
    (``Turing.FinTM.computesFunInTime_splitSolve, []),
    (``Turing.capture_run, []),
    -- E3 statement layer, untouched.
    (``Complexity.EXP_subset_NEXP, [``Complexity.EXP_subset_NEXP])]
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
  logInfo "B2 CLOSURE AUDIT PASS: all ten epoch-2 targets admission-free; Chapter-1 and library regressions unchanged; E3 statement layer at its own roots."

end B2ClosureAudit
