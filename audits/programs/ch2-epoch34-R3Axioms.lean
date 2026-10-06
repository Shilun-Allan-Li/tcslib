import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassP
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.CookLevin
import TCSlib.Complexity.Formulas
import TCSlib.Complexity.Uncomputability
import Lean
import Std.Data.HashMap

set_option maxHeartbeats 0

/- Round-2 closure program for the epoch-3/4 fill gate, per finding 1 of
`audits/ch2-epoch34-findings.md`:
 (1) all 21 frozen targets explicitly, roots AND permitted axioms;
 (2) every checked declaration of the six owned modules, rejecting missing
     entries, with the FULL permitted-axiom bound on each transitive
     closure (a bare non-permitted axiom -- sorryAx included -- anywhere in
     any closure fails the run; this strengthens the direct-sorryAx test
     the auditor's probe defeated);
 (3) kernel public surface of each owned module against its source-derived
     public list (no anonymous instances exist in these files);
 (4) the same full axiom bound over every TCSlib declaration in the import
     closure;
 (5) explicit inclusion of all 65 modules of the committed order. -/

open Lean Elab Command

namespace R3Audit

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

abbrev AxM := ReaderT Environment (StateM (Std.HashMap Name Bool))

/-- `true` iff every axiom in the transitive closure is permitted.
Panics on a missing checked declaration. -/
partial def clean (name : Name) : AxM Bool := do
  if let some r := (← get).get? name then return r
  modify fun m => m.insert name true
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut ok := true
    if let .axiomInfo _ := ci then
      unless allowed.contains name do ok := false
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      deps := deps ++ v.getUsedConstants
    if let .inductInfo i := ci then
      deps := deps ++ i.ctors.toArray
    for d in deps do
      unless (← clean d) do ok := false
    modify fun m => m.insert name ok
    return ok

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

def userRoots (env : Environment) (name : Name) : List Name :=
  ((((visit name).run env).run {}).2.roots.map privateToUserName).toList.eraseDups

def publicsNondeterminism : Array Name := #[`Complexity.EXP_eq_NEXP_of_P_eq_NP, `Complexity.NEXP_eq_iUnion_NTIME, `Complexity.NEXP_subset_iUnion_NTIME, `Complexity.NP_eq_iUnion_NTIME, `Complexity.NP_subset_iUnion_NTIME, `Complexity.P_ne_NP_of_EXP_ne_NEXP, `Complexity.ntime_expPow_subset_NEXP, `Complexity.ntime_poly_subset_NP]
def publicsEXP : Array Name := #[`Complexity.EXP, `Complexity.EXP_subset_NEXP, `Complexity.ExpBound, `Complexity.NEXP, `Complexity.NP_subset_EXP, `Complexity.P_subset_EXP, `Complexity.enumWord, `Complexity.exists_proj_decider]
def publicsSAT : Array Name := #[`Complexity.SAT, `Complexity.SAT3, `Complexity.SAT3_mem_NP, `Complexity.SAT_mem_NP, `Complexity.SAT_reducible_SAT3]
def publicsSnapshot : Array Name := #[`Complexity.Snapshot, `Complexity.emitted, `Complexity.inputBitAt, `Complexity.inputPosAt, `Complexity.oblivious_schedule_eq, `Complexity.prevVisit, `Complexity.snapshotAt, `Complexity.snapshotAt_inputSymbol, `Complexity.snapshotAt_state_succ, `Complexity.snapshotAt_workSymbol, `Complexity.snapshotAt_zero, `Complexity.stepState, `Complexity.workPosAt, `Complexity.writtenOrKept]
def publicsTautology : Array Name := #[`Complexity.TAUTOLOGY, `Complexity.TAUTOLOGY_coNPComplete, `Complexity.TAUTOLOGY_mem_coNP, `Complexity.coNPComplete, `Complexity.coNPHard]
def publicsHardness : Array Name := #[`Complexity.NPHard.polyTimeReducible, `Complexity.SAT3_NPComplete, `Complexity.SAT3_NPHard, `Complexity.SAT_NPComplete, `Complexity.SAT_NPHard]

def inventoryNondeterminism : Array Name := #[`Complexity.EXP_eq_NEXP_of_P_eq_NP, `Complexity.NEXP_eq_iUnion_NTIME, `Complexity.NEXP_subset_iUnion_NTIME, `Complexity.NP_eq_iUnion_NTIME, `Complexity.NP_subset_iUnion_NTIME, `Complexity.P_ne_NP_of_EXP_ne_NEXP, `Complexity.ntime_expPow_subset_NEXP, `Complexity.ntime_expPow_subset_NEXP._proof_1_2, `Complexity.ntime_expPow_subset_NEXP._proof_1_3, `Complexity.ntime_expPow_subset_NEXP._proof_1_4, `Complexity.ntime_poly_subset_NP, `Turing.NDTM.runWith.eq_1, `Turing.NDTM.runWith.eq_2, `Turing.NDTM.runWith.eq_def, `Turing.NDTM.stepWith.eq_1]

def inventoryEXP : Array Name := #[`Complexity.EXP, `Complexity.EXP_subset_NEXP, `Complexity.ExpBound, `Complexity.NEXP, `Complexity.NP_subset_EXP, `Complexity.NP_subset_EXP._proof_1_1, `Complexity.NP_subset_EXP._proof_1_2, `Complexity.NP_subset_EXP._proof_1_3, `Complexity.NP_subset_EXP._proof_1_4, `Complexity.NP_subset_EXP._proof_1_5, `Complexity.P_subset_EXP, `Complexity.P_subset_EXP._proof_1_1, `Complexity.enumWord, `Complexity.enumWord._sunfold, `Complexity.enumWord._unsafe_rec, `Complexity.enumWord.eq_1, `Complexity.enumWord.eq_2, `Complexity.enumWord.eq_def, `Complexity.enumWord.match_1, `Complexity.exists_proj_decider, `Complexity.exists_proj_decider._proof_1_1, `Turing.solveSplitWith.eq_1]

def inventorySAT : Array Name := #[`Complexity.SAT, `Complexity.SAT3, `Complexity.SAT3_mem_NP, `Complexity.SAT_mem_NP, `Complexity.SAT_reducible_SAT3, `Complexity.instDecidableEqSatStreamState, `Complexity.instDecidableEqSatStreamState.decEq, `Complexity.instDecidableEqSatStreamState.decEq._proof_1, `Complexity.instDecidableEqSatStreamState.decEq._proof_2, `Complexity.instDecidableEqSatStreamState.decEq._proof_3, `Complexity.instDecidableEqSatStreamState.decEq._proof_4, `Complexity.instDecidableEqSatStreamState.decEq.match_1, `Std.Sat.CNF.WidthAtMost.eq_1, `Std.Sat.CNF.fallback.eq_1, `Std.Sat.CNF.numVars.eq_1]

def inventorySnapshot : Array Name := #[`Complexity.Snapshot, `Complexity.emitted, `Complexity.inputBitAt, `Complexity.inputBitAt.eq_1, `Complexity.inputPosAt, `Complexity.oblivious_schedule_eq, `Complexity.prevVisit, `Complexity.snapshotAt, `Complexity.snapshotAt.eq_1, `Complexity.snapshotAt_inputSymbol, `Complexity.snapshotAt_inputSymbol._proof_1_2, `Complexity.snapshotAt_inputSymbol._proof_1_3, `Complexity.snapshotAt_state_succ, `Complexity.snapshotAt_workSymbol, `Complexity.snapshotAt_workSymbol._proof_1_1, `Complexity.snapshotAt_workSymbol._proof_1_2, `Complexity.snapshotAt_workSymbol.match_1, `Complexity.snapshotAt_zero, `Complexity.stepState, `Complexity.stepState.eq_1, `Complexity.stepState.match_1, `Complexity.workPosAt, `Complexity.writtenOrKept, `Complexity.writtenOrKept.eq_1]

def inventoryTautology : Array Name := #[`Complexity.TAUTOLOGY, `Complexity.TAUTOLOGY_coNPComplete, `Complexity.TAUTOLOGY_coNPComplete._simp_1_1, `Complexity.TAUTOLOGY_mem_coNP, `Complexity.coNPComplete, `Complexity.coNPHard]

def inventoryHardness : Array Name := #[`Complexity.NPHard.polyTimeReducible, `Complexity.SAT3_NPComplete, `Complexity.SAT3_NPHard, `Complexity.SAT_NPComplete, `Complexity.SAT_NPHard]

def ownedModules : Array (Name × Array Name × Array Name) := #[
  (`TCSlib.Complexity.ClassNP.Nondeterminism, publicsNondeterminism, inventoryNondeterminism),
  (`TCSlib.Complexity.ClassNP.EXP, publicsEXP, inventoryEXP),
  (`TCSlib.Complexity.ClassNP.SAT, publicsSAT, inventorySAT),
  (`TCSlib.Complexity.CookLevin.Snapshot, publicsSnapshot, inventorySnapshot),
  (`TCSlib.Complexity.ClassNP.Tautology, publicsTautology, inventoryTautology),
  (`TCSlib.Complexity.CookLevin.Hardness, publicsHardness, inventoryHardness)]

def orderModules : Array Name := #[`TCSlib.Complexity.TuringMachine.Configuration, `TCSlib.Complexity.TuringMachine.Deterministic, `TCSlib.Complexity.TuringMachine.StateRenaming, `TCSlib.Complexity.TuringMachine.Finite, `TCSlib.Complexity.TuringMachine.Oracle, `TCSlib.Complexity.TuringMachine.Simulation, `TCSlib.Complexity.TuringMachine.Sweep, `TCSlib.Complexity.TuringMachine.Composition, `TCSlib.Complexity.TuringMachine.Build.Convention, `TCSlib.Complexity.TuringMachine.Build.Wrappers, `TCSlib.Complexity.TuringMachine.Build.Loop, `TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, `TCSlib.Complexity.TuringMachine.Robustness.SingleTape, `TCSlib.Complexity.TuringMachine.Robustness.Bidirectional, `TCSlib.Complexity.ClassP.DTIME, `TCSlib.Complexity.TuringMachine.Encoding, `TCSlib.Complexity.ClassP.TimeConstructible, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger, `TCSlib.Complexity.TuringMachine.Robustness.Oblivious, `TCSlib.Complexity.ClassP.P, `TCSlib.Complexity.ClassP.ModelInvariance, `TCSlib.Complexity.ClassP.Examples, `TCSlib.Complexity.TuringMachine.Build.Primitives, `TCSlib.Complexity.TuringMachine.CodeParser, `TCSlib.Complexity.TuringMachine.MathlibBridge, `TCSlib.Complexity.TuringMachine.UniversalStartup, `TCSlib.Complexity.TuringMachine.UniversalInterpreter, `TCSlib.Complexity.TuringMachine.UniversalBlock, `TCSlib.Complexity.TuringMachine.Universal, `TCSlib.Complexity.Uncomputability.Computable, `TCSlib.Complexity.Uncomputability.Diagonalization, `TCSlib.Complexity.Uncomputability.Halting, `TCSlib.Complexity.TuringMachine.Nondeterministic, `TCSlib.Complexity.Formulas.CNF, `TCSlib.Complexity.Formulas.CNFEncoding, `TCSlib.Complexity.Formulas.DNF, `TCSlib.Complexity.ClassNP.PolyTime, `TCSlib.Complexity.ClassNP.PolyTimePairing, `TCSlib.Complexity.ClassNP.NP, `TCSlib.Complexity.ClassNP.CoNP, `TCSlib.Complexity.ClassNP.EXP, `TCSlib.Complexity.ClassNP.Reductions, `TCSlib.Complexity.ClassNP.NTIME, `TCSlib.Complexity.ClassNP.Nondeterminism, `TCSlib.Complexity.ClassNP.SAT, `TCSlib.Complexity.ClassNP.TMSAT, `TCSlib.Complexity.CookLevin.Snapshot, `TCSlib.Complexity.CookLevin.Hardness, `TCSlib.Complexity.ClassNP.Tautology, `TCSlib.Complexity.TuringMachine.UnaryTape, `TCSlib.Complexity.TuringMachine.CounterProg, `TCSlib.Complexity.TuringMachine.CounterProgRun, `TCSlib.Complexity.TuringMachine, `TCSlib.Complexity.ClassP, `TCSlib.Complexity.Uncomputability, `TCSlib.Complexity.Formulas, `TCSlib.Complexity.CookLevin, `TCSlib.Complexity.ClassNP.Transducer, `TCSlib.Complexity.ClassNP.CounterProgPolyTime, `TCSlib.Complexity.ClassNP.PClosure, `TCSlib.Complexity.ClassNP.ExpPoly, `TCSlib.Complexity.ClassNP]

def targets : Array Name := #[
  ``Complexity.ntime_expPow_subset_NEXP, ``Complexity.NEXP_eq_iUnion_NTIME,
  ``Complexity.NEXP_subset_iUnion_NTIME, ``Complexity.EXP_eq_NEXP_of_P_eq_NP,
  ``Complexity.P_ne_NP_of_EXP_ne_NEXP, ``Complexity.EXP_subset_NEXP,
  ``Complexity.SAT_mem_NP, ``Complexity.SAT3_mem_NP, ``Complexity.SAT_reducible_SAT3,
  ``Complexity.snapshotAt_zero, ``Complexity.snapshotAt_state_succ,
  ``Complexity.snapshotAt_inputSymbol, ``Complexity.snapshotAt_workSymbol,
  ``Complexity.oblivious_schedule_eq, ``Complexity.TAUTOLOGY_mem_coNP,
  ``Complexity.NPHard.polyTimeReducible, ``Complexity.SAT_NPHard,
  ``Complexity.SAT_NPComplete, ``Complexity.SAT3_NPHard,
  ``Complexity.SAT3_NPComplete, ``Complexity.TAUTOLOGY_coNPComplete]

run_cmd do
  let env ← getEnv
  -- Pass 5 first: module inclusion.
  let present : NameSet := env.header.moduleNames.foldl (fun s m => s.insert m) {}
  for m in orderModules do
    unless present.contains m do
      throwError "Order module not imported: {m}"
  logInfo m!"PASS 5: all {orderModules.size} order modules are in the import closure."
  -- Pass 1: the 21 targets, roots and axioms.
  for name in targets do
    let found := userRoots env name
    logInfo m!"TARGET {name}: roots {found}"
    unless found == [] do throwError "Admission roots remain for {name}: {found}"
    let ax ← collectAxioms name
    unless ax.all allowed.contains do throwError "Unexpected axiom for {name}: {ax}"
  logInfo m!"PASS 1: all {targets.size} frozen targets have empty roots and axioms within the permitted triple."
  -- Passes 2-4 share the memoized axiom walk.
  let mut cache : Std.HashMap Name Bool := {}
  let mut tcslibTotal := 0
  let mut tcslibBad : Array Name := #[]
  let mut moduleTotals : Array (Name × Nat) := #[]
  let mut surfaceBad : Array Name := #[]
  for (modName, pubs, expected) in ownedModules do
    let mut cnt := 0
    let mut actual : Array Name := #[]
    for (name, _) in env.constants.toList do
      if env.getModuleIdxFor? name |>.any (fun i => env.header.moduleNames[i.toNat]! == modName) then
        cnt := cnt + 1
        let (ok, c) := ((clean name).run env).run cache
        cache := c
        unless ok do tcslibBad := tcslibBad.push name
        if privateToUserName name == name then
          actual := actual.push name
          unless expected.contains name do
            surfaceBad := surfaceBad.push name
    -- Reverse direction: every expected inventory entry (hence every source
    -- public) exists and is owned by exactly this module.
    for e in expected do
      unless actual.contains e do
        throwError "Expected kernel name missing from {modName}: {e}"
    for p in pubs do
      unless expected.contains p && actual.contains p do
        throwError "Source public missing or mis-owned in {modName}: {p}"
    unless actual.size == expected.size do
      throwError "Inventory size mismatch in {modName}: actual {actual.size} vs expected {expected.size}"
    moduleTotals := moduleTotals.push (modName, cnt)
  unless surfaceBad.isEmpty do
    throwError "Kernel names outside the reviewed exact inventory: {surfaceBad}"
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      if (`TCSlib).isPrefixOf (env.header.moduleNames[idx.toNat]!) then
        tcslibTotal := tcslibTotal + 1
        let (ok, c) := ((clean name).run env).run cache
        cache := c
        unless ok do tcslibBad := tcslibBad.push name
  unless tcslibBad.isEmpty do
    throwError "Declarations whose closures exceed the permitted axioms: {tcslibBad}"
  for (m, n) in moduleTotals do
    logInfo m!"PASS 2/3 {m}: {n} checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions)."
  logInfo m!"PASS 4: {tcslibTotal} checked TCSlib declarations in the import closure; every transitive closure is within propext/Classical.choice/Quot.sound (sorryAx and any other axiom would fail this run)."
  logInfo "R3 CLOSURE AUDIT PASS: the round-2 finding-1 surface repair discharged -- exact two-directional inventory equality on all six owned modules; axiom, target, and coverage passes unchanged from round 2."

end R3Audit
