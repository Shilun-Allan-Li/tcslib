import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import Lean

set_option maxHeartbeats 0

-- Maintainer axiom attestation: machine-library closure (fill-audit minor 2's
-- scope correction applied). This program checks the dependency CLOSURES of the
-- 23 library contracts and the regression targets; whole-module coverage of
-- every Build declaration (unused helpers, generated descendants) is the
-- separate whole-Build traversal instrument of the P4 delivery.

open Lean Elab Command

namespace LibFillAudit

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

def hostC : Name := `Turing.FinTM.loopHost_contracts

run_cmd do
  let env ← getEnv
  let expectations : Array (Name × List Name) := #[
    -- W: complete, clean.
    (``Turing.capture_run, []),
    (``Turing.FinTM.redirectTM_computes, []),
    (``Turing.FinTM.redirectTM_live, []),
    (``Turing.FinTM.computesFunInTime_cond, []),
    -- L: complete after L2 - every loop theorem admission-free.
    (``Turing.loop_run, []),
    (``Turing.FinTM.exists_loopCfgTM, []),
    (``Turing.FinTM.exists_loopTM, []),
    (``Turing.FinTM.exists_loopFindTM, []),
    -- P: the eleven filled targets, clean.
    (``Turing.FinTM.computesFunInTime_prepend, []),
    (``Turing.FinTM.computesFunInTime_pairEncodeFixed, []),
    (``Turing.FinTM.computesFunInTime_pairDup, []),
    (``Turing.FinTM.computesFunInTime_incFixed, []),
    (``Turing.FinTM.computesFunInTime_pairValid, []),
    (``Turing.FinTM.computesFunInTime_pairFst, []),
    (``Turing.FinTM.computesFunInTime_pairSnd, []),
    (``Turing.FinTM.computesFunInTime_pairConcat, []),
    (``Turing.FinTM.computesFunInTime_lengthBits, []),
    (``Turing.FinTM.computesFunInTime_polyUnary, []),
    (``Turing.FinTM.computesFunInTime_polyBits, []),
    -- P: targets 12-13 now filled and clean.
    (``Turing.FinTM.computesFunInTime_pairLenCheck, []),
    (``Turing.FinTM.computesFunInTime_stripLast, []),
    (``Turing.FinTM.computesFunInTime_pairMapSnd, []),
    (``Turing.FinTM.computesFunInTime_splitSolve, []),
    -- Headline and campaign regressions.
    (``Turing.timed_universal, []),
    (``Turing.timed_universal_concrete, []),
    (``Complexity.timed_universal_quantitative, []),
    (``Complexity.NP_subset_EXP, [`Complexity.enumMachine_contracts]),
    (``Complexity.TMSAT_mem_NP, [``Complexity.TMSAT_mem_NP])]
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
  logInfo "LIBRARY CLOSURE AUDIT PASS: all 23 contract dependency closures are admission-free with at most the standard axiom triple; headline and campaign regression roots unchanged. (Whole-Build coverage is the separate P4 traversal.)"

end LibFillAudit
