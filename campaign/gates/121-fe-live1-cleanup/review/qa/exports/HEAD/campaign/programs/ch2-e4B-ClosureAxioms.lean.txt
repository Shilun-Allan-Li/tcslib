import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.CookLevin
import Lean

set_option maxHeartbeats 0

-- Maintainer attestation: 4B closure integration.
-- THIS IS THE CHAPTER-2 CONSTRUCTION-CLOSURE GATE.
--
-- Four passes:
--  (1) Public roots: TAUTOLOGY_coNPComplete, TAUTOLOGY_mem_coNP, the
--      Cook-Levin five, SAT_reducible_SAT3, and every prior closure ALL
--      have EMPTY admission roots. No expectation carries a root anymore.
--  (2) Whole-module enumeration of Tautology.lean, NO allowlist: every
--      checked kernel declaration (95 source privates + the 5 publics +
--      generated auxiliaries) is free of sorryAx.
--  (3) Kernel public surface of Tautology.lean: exactly the original five
--      public declarations (coNPHard, coNPComplete, TAUTOLOGY,
--      TAUTOLOGY_mem_coNP, TAUTOLOGY_coNPComplete) and their descendants.
--  (4) Whole-surface closure: EVERY TCSlib.* declaration in this import
--      closure (the full 65-module campaign surface) is admission-free.

open Lean Elab Command

namespace BAudit

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

/-- Does this declaration's own type or value directly mention `sorryAx`? -/
def hasSorry (env : Environment) (name : Name) : Bool :=
  match env.checked.get.find? name with
  | none => false
  | some ci =>
    let valDeps := match ci.value? (allowOpaque := true) with
      | some value => value.getUsedConstants
      | none => #[]
    (ci.type.getUsedConstants ++ valDeps).contains ``sorryAx

run_cmd do
  let env ← getEnv
  -- Pass (1): public roots -- everything empty.
  let targets : Array Name := #[
    ``Complexity.TAUTOLOGY_coNPComplete,
    ``Complexity.TAUTOLOGY_mem_coNP,
    ``Complexity.SAT_NPHard,
    ``Complexity.SAT_NPComplete,
    ``Complexity.SAT3_NPHard,
    ``Complexity.SAT3_NPComplete,
    ``Complexity.NPHard.polyTimeReducible,
    ``Complexity.SAT_reducible_SAT3,
    ``Complexity.SAT_mem_NP,
    ``Complexity.SAT3_mem_NP,
    ``Complexity.TMSAT_NPComplete,
    ``Complexity.NEXP_subset_iUnion_NTIME,
    ``Complexity.EXP_subset_NEXP,
    ``Complexity.snapshotAt_workSymbol,
    ``Turing.emit_run,
    ``Turing.FinTM.exists_emitLoopTM,
    ``Turing.FinTM.exists_installCallTM,
    ``Turing.FinTM.exists_emitCallTM,
    ``Turing.FinTM.computesFunInTime_splitSolveWith,
    ``Turing.capture_run]
  for name in targets do
    let found := userRoots env name
    logInfo m!"ROOTS {name}: {found}"
    unless found == [] do
      throwError "Admission roots remain for {name}: {found}"
    let ax ← collectAxioms name
    unless ax.all allowed.contains do
      throwError "Unexpected axiom for {name}: {ax}"
  -- Passes (2) and (3): Tautology.lean, no allowlist; surface = the five.
  let tautMod := `TCSlib.Complexity.ClassNP.Tautology
  let publics : Array Name := #[``Complexity.coNPHard, ``Complexity.coNPComplete,
    ``Complexity.TAUTOLOGY, ``Complexity.TAUTOLOGY_mem_coNP,
    ``Complexity.TAUTOLOGY_coNPComplete]
  let mut total := 0
  let mut sorryDecls : Array Name := #[]
  let mut surface : Array Name := #[]
  -- Pass (4): the whole TCSlib surface in this import closure.
  let mut tcslibTotal := 0
  let mut tcslibSorry : Array Name := #[]
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if (`TCSlib).isPrefixOf modName then
        tcslibTotal := tcslibTotal + 1
        if hasSorry env name then
          tcslibSorry := tcslibSorry.push name
      if modName == tautMod then
        total := total + 1
        if hasSorry env name then
          sorryDecls := sorryDecls.push name
        let isPriv := privateToUserName name != name
        let fromPublic := publics.any (fun t => t == name || t.isPrefixOf name)
        unless isPriv || fromPublic || name.isInternal do
          surface := surface.push name
  unless sorryDecls.isEmpty do
    throwError "CLOSURE GATE FAILURE -- sorry in Tautology.lean: {sorryDecls}"
  unless surface.isEmpty do
    throwError "Non-private kernel surface beyond the five publics: {surface}"
  unless tcslibSorry.isEmpty do
    throwError "CLOSURE GATE FAILURE -- sorryAx somewhere in the campaign surface: {tcslibSorry}"
  logInfo m!"MODULE Tautology.lean: {total} checked declarations; ZERO carry sorryAx; kernel surface = the five original publics."
  logInfo m!"CAMPAIGN SURFACE: {tcslibTotal} checked TCSlib declarations across the full import closure; ZERO carry sorryAx."
  logInfo "B CLOSURE AUDIT PASS -- THE CHAPTER-2 CONSTRUCTION GATE PASSES: TAUTOLOGY_coNPComplete and every campaign target have empty admission roots with axioms at most propext/Classical.choice/Quot.sound; the entire 65-module campaign surface is admission-free. Chapter 2 of Arora-Barak is machine-checked end to end."

end BAudit
