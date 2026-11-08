import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.CookLevin
import Lean

set_option maxHeartbeats 0

-- Maintainer attestation: 4A-5 closure integration.
-- THIS IS THE FIVE-TARGET COMPLETION GATE.
--
-- Three passes:
--  (1) Public roots: ALL FIVE Cook-Levin targets have EMPTY admission
--      roots; SAT_reducible_SAT3 and every prior closure clean; the only
--      remaining campaign admission is TAUTOLOGY_coNPComplete (4B).
--  (2) Whole-module enumeration, NO allowlist: every checked kernel
--      declaration in TCSlib.Complexity.CookLevin.Hardness (618 source
--      privates + the five theorems + generated auxiliaries) must be
--      free of sorryAx.
--  (3) Kernel-level public surface: every declaration in the module is
--      private or descends from one of the five public theorems.

open Lean Elab Command

namespace A5Audit

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
  -- Pass (1): public roots -- the completion gate.
  let expectations : Array (Name × List Name) := #[
    -- THE FIVE TARGETS: all empty.
    (``Complexity.NPHard.polyTimeReducible, []),
    (``Complexity.SAT_NPHard, []),
    (``Complexity.SAT_NPComplete, []),
    (``Complexity.SAT3_NPHard, []),
    (``Complexity.SAT3_NPComplete, []),
    (``Complexity.SAT_reducible_SAT3, []),
    -- The one remaining campaign admission (4B), unchanged.
    (``Complexity.TAUTOLOGY_coNPComplete, [``Complexity.TAUTOLOGY_coNPComplete]),
    -- Prior closures and the library layers, unchanged.
    (``Turing.emit_run, []),
    (``Turing.FinTM.exists_emitLoopTM, []),
    (``Turing.FinTM.exists_installCallTM, []),
    (``Turing.FinTM.exists_emitCallTM, []),
    (``Turing.FinTM.computesFunInTime_splitSolveWith, []),
    (``Complexity.NEXP_subset_iUnion_NTIME, []),
    (``Complexity.EXP_subset_NEXP, []),
    (``Complexity.SAT_mem_NP, []),
    (``Complexity.SAT3_mem_NP, []),
    (``Complexity.TMSAT_NPComplete, []),
    (``Complexity.snapshotAt_workSymbol, []),
    (``Turing.capture_run, [])]
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
  -- Passes (2) and (3): whole-module enumeration, NO allowlist.
  let hardMod := `TCSlib.Complexity.CookLevin.Hardness
  let publics : Array Name := #[``Complexity.NPHard.polyTimeReducible,
    ``Complexity.SAT_NPHard, ``Complexity.SAT_NPComplete,
    ``Complexity.SAT3_NPHard, ``Complexity.SAT3_NPComplete]
  let mut total := 0
  let mut sorryDecls : Array Name := #[]
  let mut surface : Array Name := #[]
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      if env.header.moduleNames[idx.toNat]! == hardMod then
        total := total + 1
        if hasSorry env name then
          sorryDecls := sorryDecls.push name
        let isPriv := privateToUserName name != name
        let fromPublic := publics.any (fun t => t == name || t.isPrefixOf name)
        unless isPriv || fromPublic || name.isInternal do
          surface := surface.push name
  unless sorryDecls.isEmpty do
    throwError "COMPLETION GATE FAILURE -- sorry-bearing declarations remain in Hardness.lean: {sorryDecls}"
  unless surface.isEmpty do
    throwError "Non-private kernel surface beyond the five public theorems: {surface}"
  logInfo m!"MODULE Hardness.lean: {total} checked declarations; ZERO carry sorryAx; kernel public surface = the five theorems only."
  logInfo "A5 CLOSURE AUDIT PASS -- THE FIVE-TARGET COMPLETION GATE PASSES: SAT_NPHard, SAT_NPComplete, SAT3_NPHard, SAT3_NPComplete, and NPHard.polyTimeReducible all have empty admission roots with axioms at most propext/Classical.choice/Quot.sound; every declaration in Hardness.lean is admission-free; the campaign's sole remaining construction admission is TAUTOLOGY_coNPComplete. Cook-Levin is machine-checked end to end."

end A5Audit
