/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunPhase
import TCSlib.Complexity.RAMSimulation.Sim.Startup
import TCSlib.Complexity.TuringMachine.Build.NDHost
import Mathlib.Data.List.GetD

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The finite position and parity host of the RAM simulation

The host runs the start-up and then instruction phases indexed by a program position and an
alternating parity. Every dispatch flips parity, including a jump to the current position.
Positions beyond the program are represented by its final rejecting position.

## Main definitions

The instruction phases use one common immediate-address width depending only on the program.

## Main results

* `WordRAM.Sim.runProgram_immBound`: a finite program admits one such address width.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- A finite program has one positive address width covering every fetched instruction,
including the default rejection past the end.

**Proof sketch.** Take the maximum absolute value of twice an immediate address, and choose
one more bit than that maximum. `Nat.lt_two_pow_self` bounds it by the corresponding power of
two. The empty immediate list of the default rejection needs no bound. -/
theorem runProgram_immBound (P : XProgram) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ p : ℕ, ImmBound a (P.getD p (.base .reject)) := by
  classical
  let addresses := (P.flatMap immediates).toFinset
  let m := addresses.sup (fun z => (2 * z).natAbs)
  refine ⟨m + 1, Nat.succ_pos _, ?_⟩
  intro p
  rw [immBound_iff]
  intro z hz
  by_cases hp : p < P.length
  · have hmem : P.getD p (.base .reject) ∈ P := by
      rw [List.getD_eq_getElem P (.base .reject) hp]
      exact List.getElem_mem hp
    have hzmem : z ∈ addresses := List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨_, hmem, hz⟩)
    have habs : (2 * z).natAbs ≤ m := Finset.le_sup (f := fun z : ℤ => (2 * z).natAbs) hzmem
    have hpow : (m : ℤ) < (2 : ℤ) ^ (m + 1) := by
      exact_mod_cast (Nat.lt_succ_self m).trans (Nat.lt_two_pow_self (n := m + 1))
    have hupper : 2 * z ≤ ((2 * z).natAbs : ℤ) := Int.le_natAbs
    have hneg : -(2 * z) ≤ ((-(2 * z)).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at hneg
    rw [inRange_iff]
    constructor <;> omega
  · rw [List.getD_eq_default P (.base .reject) (Nat.le_of_not_gt hp), immediates_def] at hz
    cases hz

/-- The start-up and the finite family of uniform instruction phases chosen for one program.
The word-size witness remains a parameter, so the host is independent of input and bounds. -/
structure RunSetup (P : XProgram) (fn : Bool) (Mw : FinTM Bool) where
  width : ℕ
  width_pos : 1 ≤ width
  bounded : ∀ p : ℕ, ImmBound width (P.getD p (.base .reject))
  extraTapes : ℕ
  StartState : Type
  finiteStart : Fintype StartState
  decidableStart : DecidableEq StartState
  startup : MultiTapeTM (8 + extraTapes) Bool StartState
  startEntry : StartState
  startExit : StartState
  startCost : ℕ
  start_correct : ∀ (x : List Bool) (W tw sw : ℕ), Mw.ComputesInTime x (Nat.bits W) tw →
    Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw →
    ∃ (t : ℕ) (o : Fin 8 → ℤ), t ≤ tw + startCost * (x.length + W ^ 2 + 1) ∧
      (∀ s < t, (startup.runFrom (Turing.Cfg.init startEntry x) s).state ≠ some startExit) ∧
      (startup.runFrom (Turing.Cfg.init startEntry x) t).state = some startExit ∧
      Encodes width fn {-1} (XCfg.init W x.length) (Fin.castAddEmb extraTapes) o
        (startup.runFrom (Turing.Cfg.init startEntry x) t) ∧
      startup.spaceUsed (Turing.Cfg.init startEntry x) t ≤
        sw + startCost * (W + (Nat.bits x.length).length + 1)
  phases : (p : Fin (P.length + 1)) → RunPhase width fn (P.getD p.val (.base .reject))

attribute [instance] RunSetup.finiteStart RunSetup.decidableStart

/-- The approved start-up and instruction interfaces supply a finite setup for every program
and word-size witness. The choices of phases are made once for the whole finite program. -/
theorem exists_runSetup (P : XProgram) (fn : Bool) (Mw : FinTM Bool) :
    Nonempty (RunSetup P fn Mw) := by
  classical
  obtain ⟨a, ha, hbound⟩ := runProgram_immBound P
  obtain ⟨k', S, hfin, hdec, R, entry, exit, C, hstart⟩ := exists_startup a ha fn Mw
  exact ⟨{
    width := a
    width_pos := ha
    bounded := hbound
    extraTapes := k'
    StartState := S
    finiteStart := hfin
    decidableStart := hdec
    startup := R
    startEntry := entry
    startExit := exit
    startCost := C
    start_correct := hstart
    phases := fun p => Classical.choice (exists_runPhase a fn _ (hbound p.val)) }⟩

/-- The finite representative of a program position: positions past the program are clamped
to the final rejecting position. -/
@[simps (config := { isSimp := false }) val]
def runPosition (P : XProgram) (p : ℕ) : Fin (P.length + 1) :=
  ⟨min p P.length, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Clamping a position leaves its fetched instruction unchanged: both a clamped endpoint
and every position beyond it fetch the default rejection. -/
theorem runPosition_fetch (P : XProgram) (p : ℕ) :
    P.getD (runPosition P p).val (.base .reject) = P.getD p (.base .reject) := by
  rw [runPosition_val]
  by_cases hp : p ≤ P.length
  · rw [min_eq_left hp]
  · rw [min_eq_right (Nat.le_of_not_ge hp), List.getD_eq_default P (.base .reject) le_rfl,
      List.getD_eq_default P (.base .reject) (Nat.le_of_not_ge hp)]

namespace RunSetup

variable {P : XProgram} {fn : Bool} {Mw : FinTM Bool} (A : RunSetup P fn Mw)

/-- The host's phase indices consist of the start-up and position/parity pairs. -/
abbrev Index := Option (Fin (P.length + 1) × Bool)

/-- The phase-index type is an optional position/parity pair. -/
theorem index_eq : Index (P := P) = Option (Fin (P.length + 1) × Bool) := rfl

/-- The control-state type of a phase: start-up states, or the instruction's states.
This reducible type notation keeps dependent tags usable in the simulation's other files. -/
abbrev PhaseState : Index (P := P) → Type
  | none => A.StartState
  | some (p, _) => (A.phases p).State

/-- The start-up phase uses its chosen state type. -/
theorem phaseState_none : A.PhaseState none = A.StartState := rfl

/-- A position/parity phase uses that position's instruction state type. -/
theorem phaseState_some (p : Fin (P.length + 1)) (par : Bool) :
    A.PhaseState (some (p, par)) = (A.phases p).State := rfl

instance phaseFintype (i : Index (P := P)) : Fintype (A.PhaseState i) :=
  match i with
  | none => A.finiteStart
  | some (p, _) => (A.phases p).finiteState

instance phaseDecidableEq (i : Index (P := P)) : DecidableEq (A.PhaseState i) :=
  match i with
  | none => A.decidableStart
  | some (p, _) => (A.phases p).decidableState

/-- The host's phase machines: a deterministic start-up and embedded instruction phases. -/
def phase : (i : Index (P := P)) → NDTM (8 + A.extraTapes) Bool (A.PhaseState i)
  | none => A.startup.toNDTM
  | some (p, _) => runEmbedND (Fin.castAddEmb A.extraTapes) (A.phases p).machine

/-- The start-up machine is the deterministic embedding of the chosen start-up. -/
theorem phase_none : A.phase none = A.startup.toNDTM := rfl

/-- The instruction at a position is embedded on the first eight tapes. -/
theorem phase_some (p : Fin (P.length + 1)) (par : Bool) :
    A.phase (some (p, par)) = runEmbedND (Fin.castAddEmb A.extraTapes) (A.phases p).machine := rfl

/-- The host's state type is the disjoint union of its finite phase state types. -/
abbrev State := Σ i : Index (P := P), A.PhaseState i

/-- The host state type, as its dependent-sum expression. -/
theorem state_eq : A.State = (Σ i : Index (P := P), A.PhaseState i) := rfl

/-- The entry tag reached by a next/jump dispatch. Every dispatch changes parity. -/
def resumeTag (p : Fin (P.length + 1)) (par jump : Bool) : A.State :=
  let p' := runPosition P (if jump then jumpTarget (P.getD p.val (.base .reject)) else p.val + 1)
  ⟨some (p', !par), (A.phases p').entry⟩

/-- The next/jump destination is the clamped target, with opposite parity and its phase entry. -/
theorem resumeTag_eq (p : Fin (P.length + 1)) (par jump : Bool) :
    A.resumeTag p par jump =
      let p' := runPosition P
        (if jump then jumpTarget (P.getD p.val (.base .reject)) else p.val + 1)
      ⟨some (p', !par), (A.phases p').entry⟩ := rfl

/-- The redirect table: leave the start-up at its exit, and otherwise use the instruction's
next/jump tag. Verdict phases have no redirect. -/
def redirect : (i : Index (P := P)) → A.PhaseState i → Option A.State
  | none, q => if q = A.startExit then some ⟨some (0, false), (A.phases 0).entry⟩ else none
  | some (p, par), q => ((A.phases p).redirect q).map (A.resumeTag p par)

/-- A start-up state redirects exactly when it is the designated exit. -/
theorem redirect_none (q : A.StartState) :
    A.redirect none q =
      if q = A.startExit then some ⟨some (0, false), (A.phases 0).entry⟩ else none := rfl

/-- An instruction redirect tags its chosen next/jump destination in the host. -/
theorem redirect_some (p : Fin (P.length + 1)) (par : Bool) (q : (A.phases p).State) :
    A.redirect (some (p, par)) q = ((A.phases p).redirect q).map (A.resumeTag p par) := rfl

/-- The simulation's nondeterministic phase host, entered at the chosen start-up entry. -/
def host : NDTM (8 + A.extraTapes) Bool A.State :=
  NDTM.phaseHostND A.phase ⟨none, A.startEntry⟩ A.redirect

/-- A deterministic slice of the simulation host is the existing deterministic phase host
of the same slices. This is the interface used to transfer deterministic phase contracts. -/
theorem host_fixChoice (b : Bool) :
    A.host.fixChoice b = phaseHostTM (fun i => (A.phase i).fixChoice b)
      ⟨none, A.startEntry⟩ A.redirect := by
  rw [host, NDTM.phaseHostND_fixChoice]

/-- The simulation host starts in the tagged start-up entry. -/
theorem host_q₀ : A.host.q₀ = ⟨none, A.startEntry⟩ := by
  calc A.host.q₀ = (A.host.fixChoice false).q₀ := (NDTM.fixChoice_q₀ _ _).symm
    _ = ⟨none, A.startEntry⟩ := by rw [host_fixChoice, phaseHostTM_q₀]

/-- A branch of the simulation host is a branch of the chosen standard phase host. -/
theorem host_runWith {x : List Bool} (w : List Bool)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x) :
    A.host.runWith w d =
      (NDTM.phaseHostND A.phase ⟨none, A.startEntry⟩ A.redirect).runWith w d := rfl

/-- The simulation host bundled with its finite state type and fixed number of tapes. -/
@[simps (config := { isSimp := false }) k State tm]
def finHost : FinNDTM Bool := ⟨8 + A.extraTapes, A.State, A.host⟩

end RunSetup

end WordRAM.Sim
