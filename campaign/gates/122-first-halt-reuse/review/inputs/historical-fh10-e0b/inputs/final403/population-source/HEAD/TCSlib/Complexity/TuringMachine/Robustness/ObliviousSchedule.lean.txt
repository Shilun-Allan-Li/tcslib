/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines: the length-only schedule

This file defines obliviousness (`Turing.FinTM.Oblivious`) and builds the generic
layers of the oblivious-simulation construction: the masked clock (an
input-insensitive replay of a witness machine), the schedule decoration
(`decorateTM`, data transducers whose extra tapes follow one designated schedule
head), and the transverse binary coding (`parallelTM`), together with the concrete
length-only schedule machine `obliviousSchedule` and its trajectory certificate.
It was split out mechanically from `Robustness/Oblivious.lean` at the epoch-3→4
merge; the construction is the epoch-3 fill, batch C. The candidate machine, its
setup and halting analysis, and the final theorem `Complexity.oblivious_of_mem_DTIME`
live in the subsequent chain `ObliviousCandidate.lean`, `ObliviousSetup.lean`,
`ObliviousLedger.lean`, and `Robustness/Oblivious.lean`.

## Design

* Configurations are indexed by their input, so head positions of runs on different
  inputs live in different types only for the input head; obliviousness compares
  `Fin`-valued input positions through `ℕ` and work positions (in `ℤ`) directly.
* `Oblivious` constrains *represented* head trajectories only — the input head and
  the work heads. Our model has no output-head position (output is an append-only
  stream), so emission schedules are deliberately unconstrained; [AB09]'s read-write
  output head is covered by this reading only via a bridge, e.g. a machine that emits
  once at a fixed final time, as the decider produced in `Robustness/Oblivious.lean`
  does.
* `Oblivious` does **not** imply that the halting time is determined by the input
  length: heads freeze on halting, but frozen positions can coincidentally agree — a
  stationary-head machine can halt after one or two steps depending on its first
  input bit while satisfying `Oblivious` (phase-2 audit, finding 1, with an explicit
  counterexample in `audits/phase2-findings.md`). The `TimeConstructible` hypothesis
  of the final theorem (in `Robustness/Oblivious.lean`) is required by the
  *construction* (the simulator derives a length-determined step budget and pads
  its schedule to it), not forced by the definition. If a
  downstream use (the Cook-Levin tableau, Ch. 2) needs length-determined halting or a
  simultaneous one-work-tape oblivious normal form (`M.k = 1 ∧ M.Oblivious`), those
  are separate conjuncts for that normal-form theorem.

## Main definitions

* `Turing.FinTM.Oblivious` — [AB09, Remark 1.7]. Relocated here from
  `Robustness/Oblivious.lean`; its fully qualified name is unchanged.
* `Complexity.obliviousSchedule` — the concrete length-only schedule machine.

## Main results

* `Complexity.decorateTM_oblivious`, `Complexity.parallelTM_oblivious` — schedule
  decoration and transverse binary coding preserve obliviousness.
* `Complexity.obliviousSchedule_oblivious` — the schedule's trajectory certificate.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, Exercise 1.5.)
-/

namespace Turing.FinTM

/-- A machine is *oblivious* if, at every step, its head positions on two inputs of
the same length agree: they are a function of the input length and the time only.
[AB09, Remark 1.7] -/
def Oblivious {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (x y : List Γ), x.length = y.length → ∀ t : ℕ,
    (((M.tm.runFrom (M.tm.initCfg x) t).inputPos : ℕ) =
      ((M.tm.runFrom (M.tm.initCfg y) t).inputPos : ℕ)) ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos =
      (M.tm.runFrom (M.tm.initCfg y) t).workTapePos

end Turing.FinTM

namespace Complexity

open Turing

/-- Replace the input by the constant word of the same length, preserving every
stored component. Only the proof bounding the dependent input position changes. -/
private def maskedCfg {k : ℕ} {A S : Type} (zero : A) {x : List A}
    (c : Cfg k A S x) : Cfg k A S (List.replicate x.length zero) :=
  ⟨c.state, ⟨c.inputPos.val, by simpa only [List.length_replicate] using c.inputPos.isLt⟩,
    c.workTapes, c.workTapePos, c.output⟩

/-- The masked configuration reads a blank at precisely the original boundaries
and reads the fixed symbol at every interior position. -/
private lemma maskedCfg_input {k : ℕ} {A S : Type} (zero : A) {x : List A}
    (c : Cfg k A S x) :
    (maskedCfg zero c).inputSymbol = c.inputSymbol.map (fun _ => zero) := by
  unfold Cfg.inputSymbol
  simp only [maskedCfg, List.length_replicate, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- Input masking commutes with applying a supplied action. -/
private lemma maskedCfg_apply {k : ℕ} {A S : Type} (zero : A) {x : List A}
    (a : Action k A S) (c : Cfg k A S x) :
    maskedCfg zero (a.apply c) = a.apply (maskedCfg zero c) := by
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp only [maskedCfg, Action.apply, moveInputPos, List.length_replicate]
    split <;> rfl
  · rfl
  · rfl
  · rfl

/-- The clock transition table preserves blanks and substitutes the fixed symbol for
every nonblank input read. [AB09, Exercise 1.5], masked-clock implementation. -/
def maskedClock {A : Type} (W : FinTM A) (zero : A) : FinTM A where
  k := W.k
  State := W.State
  tm := { q₀ := W.tm.q₀, tr := fun q inp ws => W.tm.tr q (inp.map (fun _ => zero)) ws }

/-- One masked transition equals one witness transition on the constant input,
including the absorbing halted case. -/
private lemma maskedClock_step {A : Type} (W : FinTM A) (zero : A) {x : List A}
    (c : Cfg W.k A W.State x) :
    maskedCfg zero ((maskedClock W zero).tm.step c) = W.tm.step (maskedCfg zero c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [maskedCfg, hs]
  | some q =>
    have hstate : (maskedCfg zero c).state = some q := hs
    rw [hstate]
    dsimp only [maskedClock]
    rw [maskedCfg_input zero, maskedCfg_apply zero]
    rfl

/-- **Masked-clock lockstep.** At every physical time, all five configuration
components coincide with the witness on the constant input of the same length.

**Proof sketch.** Initialization has the same state, numerical input position,
blank tapes, work positions, and empty output. The preceding one-step lemma
preserves this equality, so induction includes both live and halted times. -/
private lemma maskedClock_lockstep {A : Type} (W : FinTM A) (zero : A) (x : List A) (t : ℕ) :
    maskedCfg zero ((maskedClock W zero).tm.runFrom ((maskedClock W zero).tm.initCfg x) t) =
      W.tm.runFrom (W.tm.initCfg (List.replicate x.length zero)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', maskedClock_step W zero, ih,
      MultiTapeTM.runFrom_succ_eq_step']

/-- Masking is oblivious on every input, without a halting premise. -/
private lemma maskedClock_oblivious {A : Type} (W : FinTM A) (zero : A) : (maskedClock W zero).Oblivious := by
  intro x y hxy t
  have hx := maskedClock_lockstep W zero x t
  have hy := maskedClock_lockstep W zero y t
  constructor
  · exact (congrArg (fun c => c.inputPos.val) hx).trans
      ((congrArg (fun n => (W.tm.runFrom (W.tm.initCfg (List.replicate n zero)) t).inputPos.val)
        hxy).trans (congrArg (fun c => c.inputPos.val) hy).symm)
  · have hxp := congrArg Cfg.workTapePos hx
    have hyp := congrArg Cfg.workTapePos hy
    dsimp only [maskedCfg] at hxp hyp
    rw [hxp, hyp, hxy]

/-- A transition table insensitive to nonblank input contents is oblivious.
The constant-input lockstep supplies the entire trajectory, including halting. -/
private lemma inputInsensitive_oblivious {A : Type} (P : FinTM A) (zero : A)
    (h : ∀ q inp ws, P.tm.tr q (inp.map (fun _ => zero)) ws = P.tm.tr q inp ws) :
    P.Oblivious := by
  have hm : (maskedClock P zero).tm = P.tm := by
    have ht : (fun q inp ws => P.tm.tr q (inp.map (fun _ => zero)) ws) = P.tm.tr := by
      funext q inp ws
      exact h q inp ws
    change { q₀ := P.tm.q₀, tr := fun q inp ws => P.tm.tr q (inp.map (fun _ => zero)) ws } = P.tm
    rw [ht]
  simpa only [FinTM.Oblivious, hm] using maskedClock_oblivious P zero

/-- The masked witness retains its length-dependent budget output and time bound. -/
lemma maskedClock_computes (W : FinTM Bool) (T : ℕ → ℕ) (b : ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1))) :
    ∀ x, (maskedClock W false).ComputesInTime x (T x.length).bits (b * (T x.length + 1)) := by
  intro x
  have hw := (FinTM.computesInTime_iff W _ _ _).mp (hW (List.replicate x.length false))
  simp only [List.length_replicate] at hw
  have hc := maskedClock_lockstep W false x (b * (T x.length + 1))
  rw [FinTM.computesInTime_iff]
  exact ⟨(congrArg Cfg.state hc).trans hw.1, (congrArg Cfg.output hc).trans hw.2⟩

/-- A data transducer decorates a schedule without selecting any head movement.
Its extra tapes all follow one designated schedule head. Its finite data state,
writes, and emissions may depend on the actual input and on data-tape contents. -/
def decorateTM {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A) : FinTM A where
  k := P.k + l
  State := P.State × D
  tm :=
    { q₀ := (P.tm.q₀, initial)
      tr := fun q inp ws =>
        let a := P.tm.tr q.1 inp (fun i => ws (i.castAdd l))
        let v := visit q.1 q.2 inp (fun i => ws (i.castAdd l))
          (fun i => ws (i.natAdd P.k))
        ⟨a.inputTape,
          Fin.addCases a.workTapes (fun i => (v.2.1 i, (a.workTapes head).2)),
          v.2.2, a.state.map (fun s => (s, v.1))⟩ }

/-- Project a decorated computation onto the schedule; the schedule's output is
empty and its data tapes and finite data state are discarded. -/
private def scheduleCfg {A D S : Type} {k l : ℕ} {x : List A}
    (c : Cfg (k + l) A (S × D) x) : Cfg k A S x :=
  ⟨c.state.map Prod.fst, c.inputPos, fun i => c.workTapes (i.castAdd l),
    fun i => c.workTapePos (i.castAdd l), []⟩

/-- Projection of one decorated transition is one schedule transition. This is
an equality of configurations, not merely a macro-boundary correspondence. -/
private lemma decorateTM_step {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A)
    (hout : ∀ q inp ws, (P.tm.tr q inp ws).output = none)
    {x : List A} (c : Cfg (P.k + l) A (P.State × D) x) :
    scheduleCfg ((decorateTM P l head initial visit).tm.step c) =
      P.tm.step (scheduleCfg c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [scheduleCfg, hs, Option.map_none]
  | some q =>
    have hstate : (scheduleCfg c).state = some q.1 := by
      simp only [scheduleCfg, hs, Option.map_some]
    have hin : (scheduleCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (scheduleCfg c).workTapeSymbols = fun i => c.workTapeSymbols (i.castAdd l) := rfl
    rw [hstate]
    dsimp only [decorateTM]
    rw [hin, hw]
    apply Cfg.ext
    · simp only [scheduleCfg, Action.apply, Option.map_map, Function.comp_def]
      cases (P.tm.tr q.1 c.inputSymbol (fun i => c.workTapeSymbols (i.castAdd l))).state <;> rfl
    · rfl
    · funext i z
      simp only [scheduleCfg, Action.apply, Fin.addCases_left, Cfg.workTapeSymbols]
    · funext i
      simp only [scheduleCfg, Action.apply, Fin.addCases_left]
    · simp only [scheduleCfg, Action.apply, hout, Option.toList_none, List.append_nil]

/-- The schedule projection is exact at every physical step.
**Proof sketch.** Projection preserves initialization. Induct on time and use
the preceding step equality; the final emitted data bit is deliberately absent
from the schedule projection. -/
lemma decorateTM_run {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A)
    (hout : ∀ q inp ws, (P.tm.tr q inp ws).output = none)
    (x : List A) (t : ℕ) :
    scheduleCfg ((decorateTM P l head initial visit).tm.runFrom
      ((decorateTM P l head initial visit).tm.initCfg x) t) =
      P.tm.runFrom (P.tm.initCfg x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', decorateTM_step P l head initial visit hout,
      ih, MultiTapeTM.runFrom_succ_eq_step']

/-- Every data head stays aligned with the designated schedule head, including
after halting. Data-selected writes therefore cannot alter a trajectory. -/
private lemma decorateTM_heads {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A)
    (x : List A) (t : ℕ) (i : Fin l) :
    ((decorateTM P l head initial visit).tm.runFrom
      ((decorateTM P l head initial visit).tm.initCfg x) t).workTapePos (i.natAdd P.k) =
    ((decorateTM P l head initial visit).tm.runFrom
      ((decorateTM P l head initial visit).tm.initCfg x) t).workTapePos (head.castAdd l) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    generalize hc : (decorateTM P l head initial visit).tm.runFrom
      ((decorateTM P l head initial visit).tm.initCfg x) t = c at *
    unfold MultiTapeTM.step
    cases hs : c.state with
    | none => exact ih
    | some q =>
      simp only [decorateTM, Action.apply, Fin.addCases_left, Fin.addCases_right, ih]

/-- Adding data transductions preserves an oblivious schedule on all inputs.

**Proof sketch.** At every time the schedule heads equal the original schedule's
heads by projection, and every extra data head equals its designated schedule
head. Apply the original obliviousness relation to the two equal-length inputs.
This proof permits arbitrary data states, different answers, and arbitrary
data-selected writes; none can choose a move or terminate the schedule early. -/
lemma decorateTM_oblivious {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A)
    (hout : ∀ q inp ws, (P.tm.tr q inp ws).output = none)
    (hP : P.Oblivious) : (decorateTM P l head initial visit).Oblivious := by
  intro x y hxy t
  have hx := decorateTM_run P l head initial visit hout x t
  have hy := decorateTM_run P l head initial visit hout y t
  obtain ⟨hin, hw⟩ := hP x y hxy t
  constructor
  · exact (congrArg (fun c => c.inputPos.val) hx).trans
      (hin.trans (congrArg (fun c => c.inputPos.val) hy).symm)
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (congrArg (fun c => c.workTapePos j) hx).trans
        ((congrFun hw j).trans (congrArg (fun c => c.workTapePos j) hy).symm)
    · rw [decorateTM_heads, decorateTM_heads]
      exact (congrArg (fun c => c.workTapePos head) hx).trans
        ((congrFun hw head).trans (congrArg (fun c => c.workTapePos head) hy).symm)

/-- A binary block stored transversely on one track per nonblank symbol. All
tracks of a logical tape share a head coordinate. A logical read or write thus
takes exactly one physical transition; no data-dependent coding phase is used.
The theorem imposes no bound on the number of work tapes. -/
private def parallelCode {A : Type} [DecidableEq A] : Option A ↪ (A → Option Bool) where
  toFun a j := a.map (fun b => decide (b = j))
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => have hb := congrFun h b; simp at hb
    | some a =>
      cases b with
      | none => have ha := congrFun h a; simp at ha
      | some b =>
        have ha := congrFun h a
        have hba : b = a := by simpa using ha.symm
        exact congrArg some hba.symm

/-- Decode a transverse block. Arbitrary malformed blocks have a total chosen
decoding; initialized simulations only read encoded blocks. -/
private noncomputable def parallelDecode {A : Type} [DecidableEq A]
    (v : A → Option Bool) : Option A := Function.invFun parallelCode v

/-- Decode is a left inverse on all valid blocks, including the blank block. -/
private lemma parallelDecode_code {A : Type} [DecidableEq A] (a : Option A) :
    parallelDecode (parallelCode a) = a :=
  Function.leftInverse_invFun parallelCode.injective a

/-- A fixed decoder for the two embedded output symbols. -/
private def parallelBit {A : Type} [DecidableEq A] (e : Bool ↪ A) (a : A) : Bool :=
  decide (a = e true)

/-- The fixed output decoder is correct on both embedded bits. -/
private lemma parallelBit_embed {A : Type} [DecidableEq A] (e : Bool ↪ A) (b : Bool) :
    parallelBit e (e b) = b := by
  cases b <;> simp [parallelBit, e.injective.eq_iff]

/-- The finite binary realization uses a constant block of parallel tracks for
each source tape and performs every logical step in one physical step. -/
noncomputable def parallelTM {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) : FinTM Bool where
  k := Fintype.card (Fin P.k × A)
  State := P.State
  tm :=
    { q₀ := P.tm.q₀
      tr := fun q inp ws =>
        let idx := Fintype.equivFin (Fin P.k × A)
        let a := P.tm.tr q (inp.map e) (fun i => parallelDecode (fun j => ws (idx (i, j))))
        ⟨a.inputTape, fun p =>
          let ij := idx.symm p
          ((a.workTapes ij.1).1.map (fun s => parallelCode s ij.2), (a.workTapes ij.1).2),
          a.output.map (parallelBit e), a.state⟩ }

/-- The complete configuration encoding for the transverse binary realization. -/
private noncomputable def parallelCfg {A S : Type} [Fintype A] [DecidableEq A]
    {k : ℕ} {x : List Bool} (e : Bool ↪ A) (c : Cfg k A S (x.map e)) :
    Cfg (Fintype.card (Fin k × A)) Bool S x where
  state := c.state
  inputPos := ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩
  workTapes p z :=
    let ij := (Fintype.equivFin (Fin k × A)).symm p
    parallelCode (c.workTapes ij.1 z) ij.2
  workTapePos p := c.workTapePos ((Fintype.equivFin (Fin k × A)).symm p).1
  output := c.output.map (parallelBit e)

/-- The native input read is preserved through the symbol embedding. -/
private lemma parallelCfg_input {A S : Type} [Fintype A] [DecidableEq A]
    {k : ℕ} {x : List Bool} (e : Bool ↪ A) (c : Cfg k A S (x.map e)) :
    (parallelCfg e c).inputSymbol.map e = c.inputSymbol := by
  unfold Cfg.inputSymbol
  simp only [parallelCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- All tracks of a scanned logical cell decode to its original symbol. -/
private lemma parallelCfg_read {A S : Type} [Fintype A] [DecidableEq A]
    {k : ℕ} {x : List Bool} (e : Bool ↪ A) (c : Cfg k A S (x.map e)) (i : Fin k) :
    parallelDecode (fun j => (parallelCfg e c).workTapeSymbols
      (Fintype.equivFin (Fin k × A) (i, j))) = c.workTapeSymbols i := by
  simp only [parallelCfg, Cfg.workTapeSymbols, Equiv.symm_apply_apply]
  exact parallelDecode_code _

/-- **One-step binary correspondence.** Both reads and writes of a logical cell
are simultaneous across its fixed collection of tracks.

**Proof sketch.** Decode the scanned tracks using the left-inverse lemma. Both
machines consequently choose the same source action. On each track a write
changes exactly the source head's coordinate, every track moves by the source
move, and input motion and output decoding commute with the action. The halted
case is absorbing on both sides. -/
private lemma parallelTM_step {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) {x : List Bool} (c : Cfg P.k A P.State (x.map e)) :
    (parallelTM P e).tm.step (parallelCfg e c) = parallelCfg e (P.tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [parallelCfg, hs]
  | some q =>
    have hstate : (parallelCfg e c).state = some q := hs
    rw [hstate]
    dsimp only [parallelTM]
    rw [parallelCfg_input]
    have hr : (fun i => parallelDecode (fun j => (parallelCfg e c).workTapeSymbols
        (Fintype.equivFin (Fin P.k × A) (i, j)))) = c.workTapeSymbols := by
      funext i
      exact parallelCfg_read e c i
    rw [hr]
    let a := P.tm.tr q c.inputSymbol c.workTapeSymbols
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      simp only [Action.apply, parallelCfg, moveInputPos, List.length_map]
      split <;> rfl
    · funext p z
      dsimp only [Action.apply, parallelCfg]
      cases hw : (a.workTapes ((Fintype.equivFin (Fin P.k × A)).symm p).1).1 with
      | none => simp only [Option.map_none]
      | some b =>
        by_cases hz : z = c.workTapePos ((Fintype.equivFin (Fin P.k × A)).symm p).1
        · subst z
          simp only [Option.map_some, Function.update_self]
        · simp only [Option.map_some, Function.update_of_ne hz]
    · rfl
    · simp only [Action.apply, parallelCfg, List.map_append, Option.toList_map]

/-- The transverse code preserves initialized configurations exactly. -/
private lemma parallelCfg_init {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) (x : List Bool) :
    parallelCfg e (P.tm.initCfg (x.map e)) = (parallelTM P e).tm.initCfg x := by
  apply Cfg.ext rfl _ _ rfl rfl
  · apply Fin.ext
    rfl
  · funext p z
    rfl

/-- The exact binary correspondence holds at every physical time, with no
intermediate coding states or variable-duration memory accesses. -/
lemma parallelTM_run {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) (x : List Bool) (t : ℕ) :
    (parallelTM P e).tm.runFrom ((parallelTM P e).tm.initCfg x) t =
      parallelCfg e (P.tm.runFrom (P.tm.initCfg (x.map e)) t) := by
  induction t with
  | zero => exact (parallelCfg_init P e x).symm
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, parallelTM_step P e,
      MultiTapeTM.runFrom_succ_eq_step']

/-- Exact binary coding preserves obliviousness, including all intermediate
physical times and all times after halting. -/
lemma parallelTM_oblivious {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) (hP : P.Oblivious) : (parallelTM P e).Oblivious := by
  intro x y hxy t
  obtain ⟨hin, hw⟩ := hP (x.map e) (y.map e) (by simpa using hxy) t
  rw [parallelTM_run, parallelTM_run]
  constructor
  · exact hin
  · funext p
    exact congrFun hw ((Fintype.equivFin (Fin P.k × A)).symm p).1

/-- A completed output over the embedded bits is preserved at the same time. -/
lemma parallelTM_computes {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) (x w : List Bool) (t : ℕ)
    (h : P.ComputesInTime (x.map e) (w.map e) t) :
    (parallelTM P e).ComputesInTime x w t := by
  obtain ⟨hs, ho⟩ := (FinTM.computesInTime_iff P _ _ _).mp h
  rw [FinTM.computesInTime_iff, parallelTM_run]
  constructor
  · exact hs
  · change (P.tm.runFrom (P.tm.initCfg (x.map e)) t).output.map (parallelBit e) = w
    rw [ho, List.map_map]
    simp only [Function.comp_def, parallelBit_embed]
    exact List.map_id w

/-- Schedule symbols and data cells occupy disjoint parts of one finite logical
alphabet. In a data cell the second payload is the cached left neighbor. -/
inductive OblSymbol where
  | bit : Bool → OblSymbol
  | origin : OblSymbol
  | unit : OblSymbol
  | inside : OblSymbol
  | edge : Bool → OblSymbol
  | cell : (Option Bool × Fin 3) → (Option Bool × Fin 3) → OblSymbol
  deriving DecidableEq, Fintype

/-- Embed the binary native input in the logical alphabet. -/
def oblEmbed : Bool ↪ OblSymbol := ⟨OblSymbol.bit, fun _ _ h => OblSymbol.bit.inj h⟩

/-- Decode clock tape symbols; only actual bit tags carry clock data. -/
def clockBit : Option OblSymbol → Option Bool
  | some (.bit b) => some b
  | _ => none

/-- Finite phases of the length-only clock, copy, allocation, and repeated
full-sweep schedule. The source decider's state is absent from this type. -/
inductive OblPhase (S : Type) (a : ℕ) where
  | init : OblPhase S a
  | clock : S → OblPhase S a
  | resetStart : OblPhase S a
  | resetScan : OblPhase S a
  | copyLeft : OblPhase S a
  | copyLeftWrite : OblPhase S a
  | copyFirst : OblPhase S a
  | copyMore : OblPhase S a
  | copyReturn : OblPhase S a
  | budgetStart : OblPhase S a
  | budgetBack : OblPhase S a
  | append : Fin (a + 2) → OblPhase S a
  | borrow : Bool → OblPhase S a
  | unaryStart : OblPhase S a
  | unaryBack : OblPhase S a
  | layoutRight : Fin 3 → OblPhase S a
  | rightEdge : OblPhase S a
  | layoutReturn : Fin 3 → OblPhase S a
  | layoutLeft : Fin 3 → OblPhase S a
  | leftEdge : OblPhase S a
  | unaryReset : OblPhase S a
  | startCenter : OblPhase S a
  | macroCheck : OblPhase S a
  | seekLeft : OblPhase S a
  | forward : OblPhase S a
  | backward : OblPhase S a
  | returnCenter : OblPhase S a
  deriving DecidableEq, Fintype

/-- A schedule action leaves the clock work block stationary. The three extra
tapes are the binary budget, unary macrostep counter, and sweep guide. -/
def oblAction {S : Type} {k : ℕ} (q : Option S) (inp : SignType)
    (budget unary guide : Option (Option OblSymbol) × SignType) : Action (k + 3) OblSymbol S :=
  ⟨inp, Fin.addCases (fun _ => (none, 0)) (fun i =>
    if i.val = 0 then budget else if i.val = 1 then unary else guide), none, q⟩

/-- Advance a three-cell allocation phase; the caller advances its unary
counter only when the phase returns to zero. -/
def nextThird (i : Fin 3) : Fin 3 :=
  if h : i.val < 2 then ⟨i.val + 1, by omega⟩ else 0

/-- **Length-only schedule.** The clock is input-masked; copying branches only
on blank versus nonblank. Decrementing the captured fixed-width binary budget
appends `a+1` unary markers for every successful decrement, after an initial
`a+1` markers. Thus the intended unary budget is `(a+1)(T(n)+1)`.

The guide has radius three times the unary budget. Every macrostep starts at
its marked origin, traverses the entire guide in both directions, and returns
to that origin before advancing the unary counter. All these actions are
independent of the source decider and of all decorated data tapes. -/
def obliviousSchedule (W : FinTM Bool) (a : ℕ) : FinTM OblSymbol where
  k := W.k + 3
  State := OblPhase W.State a
  tm :=
    { q₀ := .init
      tr := fun q inp ws =>
        let bit := ws (Fin.natAdd W.k (0 : Fin 3))
        let unary := ws (Fin.natAdd W.k (1 : Fin 3))
        let guide := ws (Fin.natAdd W.k (2 : Fin 3))
        let stay := (none, (0 : SignType))
        let move (d : SignType) := (none, d)
        let put (s : OblSymbol) (d : SignType) := (some (some s), d)
        let act := fun q inp b u g => oblAction (k := W.k) (some q) inp b u g
        let interior := if guide = some .origin then OblSymbol.origin else .inside
        match q with
        | .init => act (.clock W.tm.q₀) 0 (put .origin .pos) (put .origin .pos) stay
        | .clock s =>
          let action := W.tm.tr s (inp.map (fun _ => false))
            (fun i => clockBit (ws (i.castAdd 3)))
          ⟨action.inputTape,
            Fin.addCases (fun i => ((action.workTapes i).1.map (Option.map OblSymbol.bit),
              (action.workTapes i).2)) (fun j =>
              if j.val = 0 then
                match action.output with
                | none => stay
                | some b => put (.bit b) .pos
              else stay),
            none, some ((action.state.map OblPhase.clock).getD .resetStart)⟩
        | .resetStart => act .resetScan .neg stay stay stay
        | .resetScan =>
          match inp with
          | none => act .copyLeft .pos stay stay stay
          | some _ => act .resetScan .neg stay stay stay
        | .copyLeft => act .copyLeftWrite 0 stay stay (move .neg)
        | .copyLeftWrite => act .copyFirst 0 stay stay (put .inside .pos)
        | .copyFirst =>
          match inp with
          | none => act .copyReturn 0 stay stay (put .origin 0)
          | some _ => act .copyMore .pos stay stay (put .origin .pos)
        | .copyMore =>
          match inp with
          | none => act .copyReturn 0 stay stay (put .inside 0)
          | some _ => act .copyMore .pos stay stay (put .inside .pos)
        | .copyReturn =>
          if guide = some .origin then act .budgetStart 0 stay stay stay
          else act .copyReturn 0 stay stay (move .neg)
        | .budgetStart => act .budgetBack 0 (move .neg) stay stay
        | .budgetBack =>
          if bit = some .origin then act (.append 0) 0 (move .pos) stay stay
          else act .budgetBack 0 (move .neg) stay stay
        | .append i =>
          if h : i.val < a + 1 then
            act (.append ⟨i.val + 1, by omega⟩) 0 stay (put .unit .pos) stay
          else act (.borrow true) 0 stay stay stay
        | .borrow carry =>
          match bit with
          | some (.bit b) =>
            act (.borrow (carry && !b)) 0 (put (.bit (Bool.xor b carry)) .pos) stay stay
          | _ =>
            if carry then act .unaryStart 0 stay stay stay
            else act .budgetStart 0 stay stay stay
        | .unaryStart => act .unaryBack 0 stay (move .neg) stay
        | .unaryBack =>
          if unary = some .origin then act (.layoutRight 0) 0 stay (move .pos) stay
          else act .unaryBack 0 stay (move .neg) stay
        | .layoutRight i =>
          if unary = some .unit then
            act (.layoutRight (nextThird i)) 0 stay
              (move (if i.val = 2 then .pos else 0)) (put interior .pos)
          else act .rightEdge 0 stay stay (put .inside .pos)
        | .rightEdge => act (.layoutReturn 0) 0 stay (move .neg) (put (.edge true) .neg)
        | .layoutReturn i =>
          if unary = some .origin then act (.layoutLeft 0) 0 stay (move .pos) stay
          else act (.layoutReturn (nextThird i)) 0 stay
            (move (if i.val = 2 then .neg else 0)) (move .neg)
        | .layoutLeft i =>
          if unary = some .unit then
            act (.layoutLeft (nextThird i)) 0 stay
              (move (if i.val = 2 then .pos else 0)) (put interior .neg)
          else act .leftEdge 0 stay stay (put .inside .neg)
        | .leftEdge => act .unaryReset 0 stay (move .neg) (put (.edge false) 0)
        | .unaryReset =>
          if unary = some .origin then act .startCenter 0 stay (move .pos) stay
          else act .unaryReset 0 stay (move .neg) stay
        | .startCenter =>
          if guide = some .origin then act .macroCheck 0 stay stay stay
          else act .startCenter 0 stay stay (move .pos)
        | .macroCheck =>
          if unary = some .unit then act .seekLeft 0 stay stay stay
          else oblAction none 0 stay stay stay
        | .seekLeft =>
          if guide = some (.edge false) then act .forward 0 stay stay (move .pos)
          else act .seekLeft 0 stay stay (move .neg)
        | .forward =>
          if guide = some (.edge true) then act .backward 0 stay stay (move .neg)
          else act .forward 0 stay stay (move .pos)
        | .backward =>
          if guide = some (.edge false) then act .returnCenter 0 stay stay (move .pos)
          else act .backward 0 stay stay (move .neg)
        | .returnCenter =>
          if guide = some .origin then act .macroCheck 0 stay (move .pos) stay
          else act .returnCenter 0 stay stay (move .pos) }

/-- The length-only schedule emits no symbols; a decoration supplies the final
answer at the schedule's final halting transition. -/
lemma obliviousSchedule_output (W : FinTM Bool) (a : ℕ)
    (q : (obliviousSchedule W a).State) (inp : Option OblSymbol)
    (ws : Fin (W.k + 3) → Option OblSymbol) :
    ((obliviousSchedule W a).tm.tr q inp ws).output = none := by
  cases q <;> simp only [obliviousSchedule, oblAction]
  all_goals repeat' first | rfl | split

/-- **Trajectory certificate for the whole schedule.** On arbitrary equal-length
logical inputs, every clock, budget, counter, and guide head has the same
position at every time. This needs no computation or halting hypothesis. -/
lemma obliviousSchedule_oblivious (W : FinTM Bool) (a : ℕ) :
    (obliviousSchedule W a).Oblivious := by
  apply inputInsensitive_oblivious _ (.bit false)
  intro q inp ws
  cases q <;> cases inp <;> rfl

end Complexity
