/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Simulation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Sweep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines

A machine is *oblivious* if its head movements depend only on the input length, not on
the input itself [AB09, Remark 1.7 and Exercise 1.5]. Obliviousness will matter for
the Cook-Levin theorem (Chapter 2), where the tableau of an oblivious computation has
input-independent structure.

## Design

* Configurations are indexed by their input, so head positions of runs on different
  inputs live in different types only for the input head; obliviousness compares
  `Fin`-valued input positions through `ℕ` and work positions (in `ℤ`) directly.
* `Oblivious` constrains *represented* head trajectories only — the input head and
  the work heads. Our model has no output-head position (output is an append-only
  stream), so emission schedules are deliberately unconstrained; [AB09]'s read-write
  output head is covered by this reading only via a bridge, e.g. a machine that emits
  once at a fixed final time, as the decider produced below does.
* `Oblivious` does **not** imply that the halting time is determined by the input
  length: heads freeze on halting, but frozen positions can coincidentally agree — a
  stationary-head machine can halt after one or two steps depending on its first
  input bit while satisfying `Oblivious` (phase-2 audit, finding 1, with an explicit
  counterexample in `audits/phase2-findings.md`). The `TimeConstructible` hypothesis
  below is required by the *construction* (the simulator derives a length-determined
  step budget and pads its schedule to it), not forced by the definition. If a
  downstream use (the Cook-Levin tableau, Ch. 2) needs length-determined halting or a
  simultaneous one-work-tape oblivious normal form (`M.k = 1 ∧ M.Oblivious`), those
  are separate conjuncts for that normal-form theorem.
* We state the quadratic version — Exercise 1.5's *first assertion*, adapted to this
  model; the exercise's final two-tape normal form is **not** included here. The
  `O(T log T)` sharpening (Exercise 1.6) is a stretch goal alongside §1.7, off the
  critical path.

## Main definitions

* `Turing.FinTM.Oblivious` — [AB09, Remark 1.7].

## Main results

* `Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5]: every language decidable
  in time-constructible time `T` is decided by an oblivious machine in `O((T + 1)²)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, p. 17; Exercise 1.5, p. 34.)
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
private def maskedClock {A : Type} (W : FinTM A) (zero : A) : FinTM A where
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
private lemma maskedClock_computes (W : FinTM Bool) (T : ℕ → ℕ) (b : ℕ)
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
private def decorateTM {A D : Type} [Fintype D] [DecidableEq D]
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
private lemma decorateTM_run {A D : Type} [Fintype D] [DecidableEq D]
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
private lemma decorateTM_oblivious {A D : Type} [Fintype D] [DecidableEq D]
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
private noncomputable def parallelTM {A : Type} [Fintype A] [DecidableEq A]
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
private lemma parallelTM_run {A : Type} [Fintype A] [DecidableEq A]
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
private lemma parallelTM_oblivious {A : Type} [Fintype A] [DecidableEq A]
    (P : FinTM A) (e : Bool ↪ A) (hP : P.Oblivious) : (parallelTM P e).Oblivious := by
  intro x y hxy t
  obtain ⟨hin, hw⟩ := hP (x.map e) (y.map e) (by simpa using hxy) t
  rw [parallelTM_run, parallelTM_run]
  constructor
  · exact hin
  · funext p
    exact congrFun hw ((Fintype.equivFin (Fin P.k × A)).symm p).1

/-- A completed output over the embedded bits is preserved at the same time. -/
private lemma parallelTM_computes {A : Type} [Fintype A] [DecidableEq A]
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
private inductive OblSymbol where
  | bit : Bool → OblSymbol
  | origin : OblSymbol
  | unit : OblSymbol
  | inside : OblSymbol
  | edge : Bool → OblSymbol
  | cell : (Option Bool × Fin 3) → (Option Bool × Fin 3) → OblSymbol
  deriving DecidableEq, Fintype

/-- Embed the binary native input in the logical alphabet. -/
private def oblEmbed : Bool ↪ OblSymbol := ⟨OblSymbol.bit, fun _ _ h => OblSymbol.bit.inj h⟩

/-- Decode clock tape symbols; only actual bit tags carry clock data. -/
private def clockBit : Option OblSymbol → Option Bool
  | some (.bit b) => some b
  | _ => none

/-- Finite phases of the length-only clock, copy, allocation, and repeated
full-sweep schedule. The source decider's state is absent from this type. -/
private inductive OblPhase (S : Type) (a : ℕ) where
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
private def oblAction {S : Type} {k : ℕ} (q : Option S) (inp : SignType)
    (budget unary guide : Option (Option OblSymbol) × SignType) : Action (k + 3) OblSymbol S :=
  ⟨inp, Fin.addCases (fun _ => (none, 0)) (fun i =>
    if i.val = 0 then budget else if i.val = 1 then unary else guide), none, q⟩

/-- Advance a three-cell allocation phase; the caller advances its unary
counter only when the phase returns to zero. -/
private def nextThird (i : Fin 3) : Fin 3 :=
  if h : i.val < 2 then ⟨i.val + 1, by omega⟩ else 0

/-- **Length-only schedule.** The clock is input-masked; copying branches only
on blank versus nonblank. Decrementing the captured fixed-width binary budget
appends `a+1` unary markers for every successful decrement, after an initial
`a+1` markers. Thus the intended unary budget is `(a+1)(T(n)+1)`.

The guide has radius three times the unary budget. Every macrostep starts at
its marked origin, traverses the entire guide in both directions, and returns
to that origin before advancing the unary counter. All these actions are
independent of the source decider and of all decorated data tapes. -/
private def obliviousSchedule (W : FinTM Bool) (a : ℕ) : FinTM OblSymbol where
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
private lemma obliviousSchedule_output (W : FinTM Bool) (a : ℕ)
    (q : (obliviousSchedule W a).State) (inp : Option OblSymbol)
    (ws : Fin (W.k + 3) → Option OblSymbol) :
    ((obliviousSchedule W a).tm.tr q inp ws).output = none := by
  cases q <;> simp only [obliviousSchedule, oblAction]
  all_goals repeat' first | rfl | split

/-- **Trajectory certificate for the whole schedule.** On arbitrary equal-length
logical inputs, every clock, budget, counter, and guide head has the same
position at every time. This needs no computation or halting hypothesis. -/
private lemma obliviousSchedule_oblivious (W : FinTM Bool) (a : ℕ) :
    (obliviousSchedule W a).Oblivious := by
  apply inputInsensitive_oblivious _ (.bit false)
  intro q inp ws
  cases q <;> cases inp <;> rfl

/-- Payload tags distinguish ordinary cells from the two virtual input
boundaries. A logical head is at the guide's marked origin; moving a virtual
head shifts its represented tape while the physical schedule stays fixed. -/
private abbrev OblPayload := Option Bool × Fin 3

/-- Blank payload, used also for the neighbor just outside a sweep. -/
private def blankPayload : OblPayload := (none, 0)

/-- Untouched physical blanks decode to a blank payload and blank neighbor. -/
private def dataCell : Option OblSymbol → OblPayload × OblPayload
  | some (.cell current left) => (current, left)
  | _ => (blankPayload, blankPayload)

/-- The source state, saved answer, source reads at macrostep entry, and sweep
neighbor registers form a finite data state. Coordinates stay on tapes. -/
private abbrev OblData (M : FinTM Bool) :=
  Option M.State × Bool × (Fin (M.k + 1) → OblPayload) × (Fin (M.k + 1) → OblPayload)

/-- The source action is the identity after halting. It never halts or shortens
the physical schedule, whose state is maintained separately. -/
private def obliviousSourceAction (M : FinTM Bool) (q : Option M.State)
    (read : Fin (M.k + 1) → OblPayload) : Action M.k Bool M.State :=
  match q with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some q => M.tm.tr q (read (Fin.natAdd M.k (0 : Fin 1))).1
      (fun i => (read (i.castAdd 1)).1)

/-- Directions of virtual work heads and the clamped virtual input head.
These directions select shifted payloads, never physical head moves. -/
private def obliviousSourceMove (M : FinTM Bool) (q : Option M.State)
    (read : Fin (M.k + 1) → OblPayload) : Fin (M.k + 1) → SignType :=
  let a := obliviousSourceAction M q read
  Fin.addCases (fun i => (a.workTapes i).2) (fun _ =>
    let tag := (read (Fin.natAdd M.k (0 : Fin 1))).2
    if (tag = 1 ∧ a.inputTape = .neg) ∨ (tag = 2 ∧ a.inputTape = .pos)
    then 0 else a.inputTape)

/-- The initial data state has a live source state, no answer emission, and
blank sweep registers. -/
private def obliviousDataInit (M : FinTM Bool) : OblData M :=
  (some M.tm.q₀, false, fun _ => blankPayload, fun _ => blankPayload)

/-- Data updates along the prescribed schedule. The input is copied with
explicit boundary payloads. At each marked origin the source transition is
selected and its writes are performed. The forward sweep caches left neighbors;
the backward sweep shifts each tape according to its virtual move. The return
to the origin installs the source successor state, including the idle `none`.
Only the final failed unary-counter test emits the stored answer. -/
private def obliviousVisit (W M : FinTM Bool) (a : ℕ)
    (phase : OblPhase W.State a) (d : OblData M) (inp : Option OblSymbol)
    (schedule : Fin (W.k + 3) → Option OblSymbol)
    (data : Fin (M.k + 1) → Option OblSymbol) :
    OblData M × (Fin (M.k + 1) → Option (Option OblSymbol)) × Option OblSymbol :=
  let unary := schedule (Fin.natAdd W.k (1 : Fin 3))
  let guide := schedule (Fin.natAdd W.k (2 : Fin 3))
  let noWrites := fun (_ : Fin (M.k + 1)) => (none : Option (Option OblSymbol))
  let keep := (d, noWrites, (none : Option OblSymbol))
  let current := fun i => (dataCell (data i)).1
  let copy (payload : OblPayload) :=
    (d, Fin.addCases (fun _ => none) (fun (_ : Fin 1) =>
      some (some (.cell payload blankPayload))), (none : Option OblSymbol))
  match phase with
  | .copyLeftWrite => copy (none, 1)
  | .copyFirst | .copyMore =>
    copy (clockBit inp, if inp.isNone then 2 else 0)
  | .macroCheck =>
    if unary = some .unit then
      let action := obliviousSourceAction M d.1 current
      ((d.1, action.output.getD d.2.1, current, fun _ => blankPayload),
        Fin.addCases (fun i => (action.workTapes i).1.map (fun p =>
          some (.cell (p, 0) blankPayload))) (fun _ => none), none)
    else (d, noWrites, some (.bit d.2.1))
  | .seekLeft =>
    if guide = some (.edge false) then
      ((d.1, d.2.1, d.2.2.1, fun _ => blankPayload), noWrites, none)
    else keep
  | .forward =>
    if guide = some (.edge true) then
      ((d.1, d.2.1, d.2.2.1, fun _ => blankPayload), noWrites, none)
    else
      ((d.1, d.2.1, d.2.2.1, current),
        fun i => some (some (.cell (current i) (d.2.2.2 i))), none)
  | .backward =>
    if guide = some (.edge false) then keep
    else
      ((d.1, d.2.1, d.2.2.1, current),
        fun i => some (some (.cell
          (match obliviousSourceMove M d.1 d.2.2.1 i with
            | .neg => (dataCell (data i)).2
            | .zero => current i
            | .pos => d.2.2.2 i) blankPayload)), none)
  | .returnCenter =>
    if guide = some .origin then
      (((obliviousSourceAction M d.1 d.2.2.1).state, d.2.1, d.2.2.1, d.2.2.2), noWrites, none)
    else keep
  | _ => keep

/-- The concrete binary simulator candidate. The finite alphabet is realized
by simultaneous transverse binary blocks, retaining the exact schedule. -/
private noncomputable def obliviousCandidate (W M : FinTM Bool) (a : ℕ) : FinTM Bool := by
  classical
  exact parallelTM
    (decorateTM (obliviousSchedule W a) (M.k + 1) (Fin.natAdd W.k (2 : Fin 3))
      (obliviousDataInit M) (obliviousVisit W M a)) oblEmbed

/-- The concrete simulator is oblivious on all binary inputs of every length,
including empty input and inputs with different simulated answers. No source
computation assumption is used in this trajectory theorem. -/
private lemma obliviousCandidate_oblivious (W M : FinTM Bool) (a : ℕ) :
    (obliviousCandidate W M a).Oblivious := by
  classical
  unfold obliviousCandidate
  apply parallelTM_oblivious
  exact decorateTM_oblivious _ _ _ _ _ (obliviousSchedule_output W a)
    (obliviousSchedule_oblivious W a)

/-- An already halted source contributes no further writes, no output, and no
virtual movement. The surrounding physical schedule nevertheless continues. -/
private lemma obliviousSourceAction_idle (M : FinTM Bool)
    (read : Fin (M.k + 1) → OblPayload) :
    obliviousSourceAction M none read = ⟨0, fun _ => (none, 0), none, none⟩ := rfl

/-- Every virtual head is stationary during an idle macrostep. -/
private lemma obliviousSourceMove_idle (M : FinTM Bool)
    (read : Fin (M.k + 1) → OblPayload) :
    obliviousSourceMove M none read = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [obliviousSourceMove, obliviousSourceAction]
  · simp [obliviousSourceMove, obliviousSourceAction]

/-- The little-endian value of a possibly zero-padded budget word. -/
private def budgetValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (budgetValue bs)

/-- The clock's canonical bit representation has the prescribed numeric value. -/
private lemma budgetValue_bits (n : ℕ) : budgetValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [budgetValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simp only [budgetValue, ih]

/-- The fixed-width borrow pass of the budget controller. It always processes
the whole word, retaining its width even when leading high bits become zero. -/
private def budgetBorrow : Bool → List Bool → Bool × List Bool
  | carry, [] => (carry, [])
  | carry, b :: bs =>
    let rest := budgetBorrow (carry && !b) bs
    (rest.1, Bool.xor b carry :: rest.2)

/-- A cleared borrow leaves every remaining bit unchanged. -/
private lemma budgetBorrow_false (bs : List Bool) : budgetBorrow false bs = (false, bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [budgetBorrow, ih]

/-- Every borrow pass has exactly the original word width. -/
private lemma budgetBorrow_length (carry : Bool) (bs : List Bool) :
    (budgetBorrow carry bs).2.length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [budgetBorrow, List.length_cons, ih]

/-- Borrow underflow occurs exactly at numeric zero, even for padded words. -/
private lemma budgetBorrow_underflow (bs : List Bool) :
    (budgetBorrow true bs).1 = true ↔ budgetValue bs = 0 := by
  induction bs with
  | nil => simp [budgetBorrow, budgetValue]
  | cons b bs ih =>
    cases b <;> simp [budgetBorrow, budgetBorrow_false, budgetValue, Nat.bit_val, ih]

/-- A successful full-width borrow subtracts exactly one.
**Proof sketch.** For a low one, clear it and leave the tail unchanged. For a
low zero, the positive input has a positive high part; recursively decrement
that part and write a low one. Underflow is excluded by positivity. -/
private lemma budgetBorrow_value (bs : List Bool) (h : 0 < budgetValue bs) :
    budgetValue (budgetBorrow true bs).2 + 1 = budgetValue bs := by
  induction bs with
  | nil => simp [budgetValue] at h
  | cons b bs ih =>
    cases b with
    | false =>
      have ht : 0 < budgetValue bs := by simpa [budgetValue, Nat.bit_val] using h
      have hb := ih ht
      change Nat.bit true (budgetValue (budgetBorrow true bs).2) + 1 = Nat.bit false (budgetValue bs)
      simp only [Nat.bit_val]
      change (2 * budgetValue (budgetBorrow true bs).2 + 1) + 1 = 2 * budgetValue bs + 0
      omega
    | true => simp [budgetBorrow, budgetBorrow_false, budgetValue, Nat.bit_val]

/-- A single active tape lane, with every inactive tape taken from a base
configuration. This supports exact setup transductions in a multi-tape machine. -/
private def laneCfg {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) : Cfg k A S x :=
  ⟨q, base.inputPos, Function.update base.workTapes lane (FinTM.sweepTape z l r),
    Function.update base.workTapePos lane z, base.output⟩

/-- An action that writes and moves just one lane, leaving input and output
stationary. -/
private def laneAction {A S : Type} {k : ℕ} (lane : Fin k) (q : S)
    (s : Option A) (d : SignType) : Action k A S :=
  ⟨0, Function.update (fun _ => (none, 0)) lane (some s, d), none, some q⟩

/-- The active lane reads the first unprocessed zipper entry. -/
private lemma laneCfg_read {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) :
    (laneCfg base lane q z l r).workTapeSymbols lane = r.head?.join := by
  simp only [laneCfg, Cfg.workTapeSymbols, Function.update_self, FinTM.sweepTape_read]

/-- The right-moving zipper identity lifts to one lane of any machine. -/
private lemma laneCfg_right {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S) (q' : S)
    (z : ℤ) (l r : List (Option A)) (a b : Option A) :
    (laneAction lane q' b .pos).apply (laneCfg base lane q z l (a :: r)) =
      laneCfg base lane (some q') (z + 1) (b :: l) r := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    by_cases hi : i = lane
    · subst i
      simp only [laneAction, laneCfg, Action.apply, Function.update_self]
      exact FinTM.sweepTape_right z l r a b
    · simp only [laneAction, laneCfg, Action.apply, Function.update_of_ne hi]
  · funext i
    by_cases hi : i = lane
    · subst i
      simp [laneAction, laneCfg]
    · simp [laneAction, laneCfg, hi]
  · exact List.append_nil _

/-- A finite forward transduction on one lane has exact cost equal to its word
length, without changing inactive tapes.
**Proof sketch.** The first entry supplies the local transition hypothesis.
One write-and-right step moves it into the left zipper stack, and induction
processes the remaining word. The full resulting configuration is retained. -/
private lemma lane_run {A S R C : Type} {k : ℕ} {x : List A}
    (tm : MultiTapeTM k A S) (lane : Fin k)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s c inp ws, ws lane = some (symbol c) →
      tm.tr (state s) inp ws = laneAction lane (state (visit s c).1)
        (some (symbol (visit s c).2)) .pos)
    (base : Cfg k A S x) (as : List C) (s : R)
    (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (laneCfg base lane (some (state s)) z l
      (as.map (fun c => some (symbol c)) ++ r)) as.length =
    laneCfg base lane (some (state (FinTM.sweepFold visit s as).1)) (z + as.length)
      (((FinTM.sweepFold visit s as).2.map (fun c => some (symbol c))).reverse ++ l) r := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, MultiTapeTM.runFrom_zero,
      FinTM.sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (laneCfg base lane (some (state s)) z l
        (some (symbol a) :: (as.map (fun c => some (symbol c)) ++ r))).workTapeSymbols lane =
        some (symbol a) := laneCfg_read _ _ _ _ _ _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [htr s a _ _ hr, laneCfg_right, ih]
    simp only [FinTM.sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- Local finite transducer for a full-width binary borrow. -/
private def budgetVisit (carry b : Bool) : Bool × Bool := (carry && !b, Bool.xor b carry)

/-- The sweep fold is precisely the fixed-width borrow operation. -/
private lemma budgetFold (carry : Bool) (bs : List Bool) :
    FinTM.sweepFold budgetVisit carry bs = budgetBorrow carry bs := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [FinTM.sweepFold, budgetVisit, budgetBorrow, ih]

/-- Updating the budget lane of the three-tape schedule is a focused action. -/
private lemma oblAction_budget {S : Type} {k : ℕ} (q : S)
    (b : Option OblSymbol) (d : SignType) :
    oblAction (k := k) (some q) 0 (some b, d) (none, 0) (none, 0) =
      laneAction (Fin.natAdd k (0 : Fin 3)) q b d := by
  unfold oblAction laneAction
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hn : j.castAdd 3 ≠ Fin.natAdd k (0 : Fin 3) := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = k + 0 at hv
      have := j.isLt
      omega
    simp [hn]
  · by_cases hj : j = 0
    · subst j
      simp
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hn : Fin.natAdd k j ≠ Fin.natAdd k (0 : Fin 3) := by
        intro he
        apply hj
        apply Fin.ext
        have hh := congrArg Fin.val he
        simpa using hh
      simp [hj, hn]

/-- The concrete controller's borrow transition realizes the local bit rule. -/
private lemma obliviousSchedule_borrow (W : FinTM Bool) (a : ℕ)
    (carry b : Bool) (inp : Option OblSymbol) (ws : Fin (W.k + 3) → Option OblSymbol)
    (hw : ws (Fin.natAdd W.k (0 : Fin 3)) = some (.bit b)) :
    (obliviousSchedule W a).tm.tr (.borrow carry) inp ws =
      laneAction (Fin.natAdd W.k (0 : Fin 3))
        (OblPhase.borrow (S := W.State) (a := a) (carry && !b))
        (some (.bit (Bool.xor b carry))) .pos := by
  simp only [obliviousSchedule, hw]
  exact oblAction_budget _ _ _

/-- The implemented borrow pass has exact cost equal to the captured word's
width and exactly the abstract numeric result. Other tape contents and head
positions, including copied input data in later decorations, are unchanged. -/
private lemma obliviousSchedule_borrow_run (W : FinTM Bool) (a : ℕ)
    {x : List OblSymbol} (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (carry : Bool) (bs : List Bool) (z : ℤ) (l r : List (Option OblSymbol)) :
    (obliviousSchedule W a).tm.runFrom
      (laneCfg base (Fin.natAdd W.k (0 : Fin 3)) (some (.borrow carry)) z l
        (bs.map (fun b => some (.bit b)) ++ r)) bs.length =
      laneCfg base (Fin.natAdd W.k (0 : Fin 3))
        (some (.borrow (budgetBorrow carry bs).1)) (z + bs.length)
        (((budgetBorrow carry bs).2.map (fun b => some (.bit b))).reverse ++ l) r := by
  have h := lane_run (obliviousSchedule W a).tm (Fin.natAdd W.k (0 : Fin 3))
    OblPhase.borrow OblSymbol.bit budgetVisit (obliviousSchedule_borrow W a) base bs carry z l r
  simpa only [budgetFold] using h

/-- The virtual input word has separate left and right boundary payloads. -/
private def inputPayload (x : List Bool) (z : ℤ) : OblPayload :=
  (FinTM.bufferTape x z, if z = -1 then 1 else if z = x.length then 2 else 0)

/-- The boundary tag at a native source input position. -/
private def inputTag {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Fin 3 :=
  if c.inputPos.val = 0 then 1 else if c.inputPos.val = x.length + 1 then 2 else 0

/-- The virtual input payload at its head gives precisely the native read and
boundary tag, including both boundaries on empty input. -/
private lemma inputPayload_head {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) :
    inputPayload x ((c.inputPos.val : ℤ) - 1) = (c.inputSymbol, inputTag c) := by
  unfold inputPayload inputTag
  rw [FinTM.bufferTape_inputSymbol]
  have hleft : (c.inputPos.val : ℤ) - 1 = -1 ↔ c.inputPos.val = 0 := by omega
  have hright : (c.inputPos.val : ℤ) - 1 = x.length ↔ c.inputPos.val = x.length + 1 := by omega
  simp only [hleft, hright]

/-- Native input clamping, expressed as a virtual tape-shift direction. -/
private def clippedMove {n : ℕ} (p : Fin (n + 2)) (d : SignType) : SignType :=
  if (p.val = 0 ∧ d = .neg) ∨ (p.val = n + 1 ∧ d = .pos) then 0 else d

/-- The clipped virtual displacement equals the native input-head displacement. -/
private lemma clippedMove_correct {n : ℕ} (p : Fin (n + 2)) (d : SignType) :
    ((moveInputPos p d).val : ℤ) - 1 = (p.val : ℤ) - 1 + (clippedMove p d : ℤ) := by
  cases d with
  | zero => simp [clippedMove]
  | neg =>
    rw [FinTM.moveInputPos_neg_val]
    by_cases h : p.val = 0
    · simp [clippedMove, h]
    · have hm : clippedMove p .neg = .neg := by simp [clippedMove, h]
      rw [hm]
      change ((p.val - 1 : ℕ) : ℤ) - 1 = (p.val : ℤ) - 1 + (-1)
      omega
  | pos =>
    by_cases h : p.val = n + 1
    · have hp : p = ⟨n + 1, by omega⟩ := Fin.ext h
      rw [hp]
      simp [clippedMove, SignType.pos_eq_one]
    · rw [moveInputPos_pos_of_ne_right p h]
      simp [clippedMove, h]

/-- Head-centered source tape payloads. The last tape is the copied virtual
input; the earlier tapes are the source work tapes. -/
private def sourcePayload {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (z : ℤ) : Fin (k + 1) → OblPayload :=
  Fin.addCases (fun i => (c.workTapes i (c.workTapePos i + z), 0))
    (fun _ => inputPayload x ((c.inputPos.val : ℤ) - 1 + z))

/-- Source reads at a macrostep origin. -/
private def sourceReads {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Fin (k + 1) → OblPayload :=
  Fin.addCases (fun i => (c.workTapeSymbols i, 0)) (fun _ => (c.inputSymbol, inputTag c))

/-- Reading the marked origin obtains all source reads simultaneously. -/
private lemma sourcePayload_origin {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : sourcePayload c 0 = sourceReads c := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [sourcePayload, sourceReads, Cfg.workTapeSymbols]
  · simp [sourcePayload, sourceReads, inputPayload_head]

/-- Interpret halting as an identity action for an idle macrostep. -/
private def sourceTotalAction (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Action M.k Bool M.State :=
  match c.state with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some q => M.tm.tr q c.inputSymbol c.workTapeSymbols

/-- The data controller selects the exact source transition at the origin. -/
private lemma obliviousSourceAction_correct (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    obliviousSourceAction M c.state (sourcePayload c 0) = sourceTotalAction M c := by
  rw [sourcePayload_origin]
  cases hs : c.state <;> simp [obliviousSourceAction, sourceTotalAction, hs, sourceReads]

/-- Applying the totalized action is exactly one source step, including idle
steps after source halting. -/
private lemma sourceTotalAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : (sourceTotalAction M c).apply c = M.tm.step c := by
  cases hs : c.state with
  | none =>
    apply Cfg.ext
    · simpa only [sourceTotalAction, hs, Action.apply, MultiTapeTM.step] using hs.symm
    · simp [sourceTotalAction, hs, MultiTapeTM.step]
    · simp [sourceTotalAction, hs, MultiTapeTM.step]
    · funext i
      simp [sourceTotalAction, hs, MultiTapeTM.step]
    · simp [sourceTotalAction, hs, MultiTapeTM.step]
  | some q => simp [sourceTotalAction, MultiTapeTM.step, hs]

/-- The shifts prescribed by a supplied source action. -/
private def sourceShift {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) : Fin (k + 1) → SignType :=
  Fin.addCases (fun i => (a.workTapes i).2) (fun _ => clippedMove c.inputPos a.inputTape)

/-- The controller's virtual shift agrees with native clamping and source work
head movement. -/
private lemma obliviousSourceMove_correct (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    obliviousSourceMove M c.state (sourcePayload c 0) = sourceShift c (sourceTotalAction M c) := by
  unfold obliviousSourceMove
  rw [obliviousSourceAction_correct, sourcePayload_origin]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [sourceShift]
  · simp only [Fin.addCases_right, sourceReads, sourceShift]
    have hp := c.inputPos.isLt
    by_cases hl : c.inputPos.val = 0
    · simp [inputTag, clippedMove, hl]
    · by_cases hr : c.inputPos.val = x.length + 1
      · simp [inputTag, clippedMove, hl, hr]
      · simp [inputTag, clippedMove, hl, hr]

/-- The origin write precedes tape shifting. Input payloads are read-only. -/
private def sourceWrittenPayload {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (z : ℤ) : Fin (k + 1) → OblPayload :=
  Fin.addCases (fun i =>
    (if z = 0 then (a.workTapes i).1.getD (c.workTapeSymbols i)
      else c.workTapes i (c.workTapePos i + z), 0))
    (fun _ => inputPayload x ((c.inputPos.val : ℤ) - 1 + z))

/-- **Head-centered simulation identity.** Write at the old origin, then shift
each virtual tape by its source displacement. The resulting payloads are those
of the next source configuration.

**Proof sketch.** For a work tape, the updated cell is at old relative coordinate
zero and the new head offset is exactly its movement. For the input tape the
word is unchanged and the clamped-displacement identity changes only its origin.
This includes stationary moves, boundary attempts, and writes of blank. -/
private lemma sourcePayload_apply {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (z : ℤ) (i : Fin (k + 1)) :
    sourcePayload (a.apply c) z i =
      sourceWrittenPayload c a (z + (sourceShift c a i : ℤ)) i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sourcePayload, sourceShift, sourceWrittenPayload, Fin.addCases_left]
    have he : c.workTapePos j + ((a.workTapes j).2 : ℤ) + z =
        c.workTapePos j + (z + ((a.workTapes j).2 : ℤ)) := by omega
    dsimp only [Action.apply]
    rw [he]
    by_cases hz : z + ((a.workTapes j).2 : ℤ) = 0
    · rw [hz]
      simp only [add_zero, if_true]
      cases hw : (a.workTapes j).1 <;> simp [hw, Cfg.workTapeSymbols]
    · have hn : c.workTapePos j + (z + ((a.workTapes j).2 : ℤ)) ≠ c.workTapePos j := by omega
      cases hw : (a.workTapes j).1 <;> simp [hz, hw, Function.update_of_ne hn]
  · simp only [sourcePayload, sourceShift, sourceWrittenPayload, Fin.addCases_right, Action.apply]
    rw [clippedMove_correct]
    congr 1
    omega

/-- One parallel row of a head-centered tape layout. -/
private def payloadRow {I : Type} (f : ℤ → I → OblPayload) (z : ℤ) (cached : Bool) :
    I → OblPayload × OblPayload :=
  fun i => (f z i, if cached then f (z - 1) i else blankPayload)

/-- The forward row transducer records its incoming left neighbor. -/
private def payloadForward {I : Type} (left : I → OblPayload)
    (row : I → OblPayload × OblPayload) :
    (I → OblPayload) × (I → OblPayload × OblPayload) :=
  (fun i => (row i).1, fun i => ((row i).1, left i))

/-- The return row transducer chooses the neighbor selected by each virtual
head movement while all physical heads move left. -/
private def payloadBackward {I : Type} (d : I → SignType) (right : I → OblPayload)
    (row : I → OblPayload × OblPayload) :
    (I → OblPayload) × (I → OblPayload × OblPayload) :=
  (fun i => (row i).1, fun i =>
    ((match d i with | .neg => (row i).2 | .zero => (row i).1 | .pos => right i), blankPayload))

/-- A forward row preserves the payload and records exactly its left neighbor. -/
private lemma payloadForward_row {I : Type} (f : ℤ → I → OblPayload) (z : ℤ) :
    payloadForward (f (z - 1)) (payloadRow f z false) = (f z, payloadRow f z true) := rfl

/-- A backward row implements the chosen shifts exactly. -/
private lemma payloadBackward_row {I : Type} (f : ℤ → I → OblPayload)
    (d : I → SignType) (z : ℤ) :
    payloadBackward d (f (z + 1)) (payloadRow f z true) =
      (f z, payloadRow (fun z i => f (z + (d i : ℤ)) i) z false) := by
  apply Prod.ext
  · rfl
  · funext i
    cases hd : d i <;> simp [payloadBackward, payloadRow, hd, SignType.cast, sub_eq_add_neg]

/-- Consecutive parallel rows of the fixed layout. -/
private def payloadZone {I : Type} (f : ℤ → I → OblPayload) (z : ℤ)
    (cached : Bool) : ℕ → List (I → OblPayload × OblPayload)
  | 0 => []
  | n + 1 => payloadRow f z cached :: payloadZone f (z + 1) cached n

/-- Every guide cell contributes exactly one parallel data row. -/
private lemma payloadZone_length {I : Type} (f : ℤ → I → OblPayload) (z : ℤ)
    (cached : Bool) (n : ℕ) : (payloadZone f z cached n).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [payloadZone, List.length_cons, ih]

/-- The full forward transduction installs all left-neighbor caches.
**Proof sketch.** The first row supplies the next carry register, and induction
handles the remaining consecutive rows. The visited interval is fixed throughout. -/
private lemma payloadForward_zone {I : Type} (f : ℤ → I → OblPayload) (z : ℤ) (n : ℕ) :
    FinTM.sweepFold payloadForward (f (z - 1)) (payloadZone f z false n) =
      (f (z + n - 1), payloadZone f z true n) := by
  induction n generalizing z with
  | zero => simp [payloadZone, FinTM.sweepFold]
  | succ n ih =>
    simp only [payloadZone, FinTM.sweepFold, payloadForward_row]
    rw [show f z = f (z + 1 - 1) from congrArg f (by omega)]
    rw [ih]
    rw [show z + 1 + (n : ℤ) - 1 = z + (n + 1 : ℕ) - 1 by omega]

/-- The full return transduction shifts every row as prescribed.
**Proof sketch.** Scan the reversed interval with the right-neighbor register.
The induction hypothesis processes all but its original first row, and the
one-row identity finishes that row with the correct right neighbor. -/
private lemma payloadBackward_zone {I : Type} (f : ℤ → I → OblPayload)
    (d : I → SignType) (z : ℤ) (n : ℕ) :
    FinTM.sweepFold (payloadBackward d) (f (z + n)) (payloadZone f z true n).reverse =
      (f z, (payloadZone (fun z i => f (z + (d i : ℤ)) i) z false n).reverse) := by
  induction n generalizing z with
  | zero => simp [payloadZone, FinTM.sweepFold]
  | succ n ih =>
    have he : z + (n + 1 : ℕ) = z + 1 + n := by omega
    simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih,
      FinTM.sweepFold, payloadBackward_row, List.append_nil]

/-- The two finite transductions realize one source action on the whole fixed
layout. This is the data-content invariant paired with the trajectory certificate. -/
private lemma payload_sweeps_source {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (z : ℤ) (n : ℕ) :
    FinTM.sweepFold (payloadBackward (sourceShift c a))
      (sourceWrittenPayload c a (z + n))
      (payloadZone (sourceWrittenPayload c a) z true n).reverse =
      (sourceWrittenPayload c a z, (payloadZone (sourcePayload (a.apply c)) z false n).reverse) := by
  have h := payloadBackward_zone (sourceWrittenPayload c a) (sourceShift c a) z n
  have he : (fun z i => sourceWrittenPayload c a (z + (sourceShift c a i : ℤ)) i) =
      sourcePayload (a.apply c) := by
    funext z i
    exact (sourcePayload_apply c a z i).symm
  rw [he] at h
  exact h

/-- Outside both virtual input boundaries, the head-centered payload is blank. -/
private lemma inputPayload_outside (x : List Bool) (z : ℤ)
    (hz : z < -1 ∨ (x.length : ℤ) < z) : inputPayload x z = blankPayload := by
  rcases hz with hz | hz
  · have hn : ¬0 ≤ z := by omega
    have hl : z ≠ -1 := by omega
    have hr : z ≠ x.length := by omega
    simp [inputPayload, FinTM.bufferTape, hn, hl, hr, blankPayload]
  · have hn : 0 ≤ z := by omega
    have hl : z ≠ -1 := by omega
    have hr : z ≠ x.length := by omega
    have hv : x.length ≤ z.toNat := by omega
    simp [inputPayload, FinTM.bufferTape, hn, hl, hr, List.getElem?_eq_none hv, blankPayload]

/-- The head-centered layout fits in the prescribed radius throughout the
entire padded source run. This uses initialized source bounds, rather than a
claim about arbitrary starting configurations.

**Proof sketch.** Both a source work head and every nonblank source cell lie
within distance `t` of the original origin, so their relative displacement has
magnitude at most `2t`. The copied input and both boundaries lie within its
length plus one of the virtual input head. Radius `3B` therefore contains every
payload whenever `t ≤ B` and input length plus one is at most `B`. -/
private lemma sourcePayload_support (M : FinTM Bool) (x : List Bool) (t B : ℕ)
    (ht : t ≤ B) (hn : x.length + 1 ≤ B) (z : ℤ)
    (hz : z < -3 * (B : ℤ) ∨ 3 * (B : ℤ) < z) (i : Fin (M.k + 1)) :
    sourcePayload (M.tm.runFrom (M.tm.initCfg x) t) z i = blankPayload := by
  let c := M.tm.runFrom (M.tm.initCfg x) t
  obtain ⟨hp, hc⟩ := FinTM.source_bounds M x t
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sourcePayload, Fin.addCases_left]
    have hpos := hp j
    have hout : c.workTapePos j + z < -(t : ℤ) ∨ (t : ℤ) < c.workTapePos j + z := by
      dsimp only [c] at *
      omega
    have hblank := hc j _ hout
    exact congrArg (fun v => (v, (0 : Fin 3))) hblank
  · simp only [sourcePayload, Fin.addCases_right]
    apply inputPayload_outside
    have hpos := c.inputPos.isLt
    dsimp only [c] at *
    omega

/-- Appending at most one source symbol updates a one-bit last-output register
by exactly `Option.getD`. This permits storing the answer in finite control. -/
private lemma lastOutput_append (w : List Bool) (b : Option Bool) :
    (w ++ b.toList).getLast?.getD false = b.getD (w.getLast?.getD false) := by
  cases b <;> simp

/-- At the padded source budget, the last-output register is the decision bit. -/
private lemma sourceAnswer_at_budget (M : FinTM Bool) (L : Language Bool)
    (T : ℕ → ℕ) (a : ℕ) (hM : M.DecidesInTime L (fun n => a * T n)) (x : List Bool) :
    (M.tm.runFrom (M.tm.initCfg x) ((a + 1) * (T x.length + 1))).output.getLast?.getD false =
      MultiTapeTM.indicator (L : Set (List Bool)) x := by
  have hle : a * T x.length ≤ (a + 1) * (T x.length + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have h := (FinTM.computesInTime_iff M _ _ _).mp ((hM x).mono hle)
  rw [h.2]
  rfl

/-- Captured clock bits begin at cell one, with a permanent origin sentinel. -/
private def clockTape (w : List Bool) (z : ℤ) : Option OblSymbol :=
  if z = 0 then some .origin else (FinTM.bufferTape w (z - 1)).map OblSymbol.bit

/-- The initial captured word contains only its sentinel. -/
private lemma clockTape_nil : clockTape [] = Function.update (fun _ : ℤ => none) 0 (some .origin) := by
  funext z
  simp [clockTape, Function.update_apply]

/-- Capturing one clock emission writes precisely the next buffer cell. -/
private lemma clockTape_append (w : List Bool) (b : Bool) :
    clockTape (w ++ [b]) = Function.update (clockTape w) (w.length + 1 : ℤ) (some (.bit b)) := by
  funext z
  by_cases hz : z = (w.length + 1 : ℤ)
  · subst z
    have hn : (w.length + 1 : ℤ) ≠ 0 := by omega
    simp [clockTape, hn]
  · rw [Function.update_of_ne hz]
    by_cases h0 : z = 0
    · simp [clockTape, h0]
    · have hne : z - 1 ≠ (w.length : ℤ) := by omega
      simp only [clockTape, if_neg h0, FinTM.bufferTape_append, Function.update_of_ne hne]

/-- A clock-stage configuration embeds the masked witness work block and
captures its entire append-only output on the budget tape. -/
private def clockStageCfg (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed) :=
  ⟨some ((c.state.map OblPhase.clock).getD .resetStart),
    ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩,
    Fin.addCases (fun i z => (c.workTapes i z).map OblSymbol.bit) (fun j =>
      if j.val = 0 then clockTape c.output else if j.val = 1 then clockTape [] else fun _ => none),
    Fin.addCases c.workTapePos (fun j => if j.val = 0 then c.output.length + 1 else if j.val = 1 then 1 else 0),
    []⟩

/-- The clock-stage input read agrees with the masked native read. -/
private lemma clockStageCfg_input (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) :
    (clockStageCfg W a c).inputSymbol.map (fun _ => false) = c.inputSymbol.map (fun _ => false) := by
  unfold Cfg.inputSymbol
  simp only [clockStageCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- The captured clock block reads the witness's work symbols exactly. -/
private lemma clockStageCfg_work (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) :
    (fun i => clockBit ((clockStageCfg W a c).workTapeSymbols (i.castAdd 3))) = c.workTapeSymbols := by
  funext i
  simp only [clockStageCfg, Cfg.workTapeSymbols, Fin.addCases_left]
  cases c.workTapes i (c.workTapePos i) <;> rfl

/-- One live witness transition, including its possible final emission, is one
captured clock transition. Administrative work begins only after that transition. -/
private lemma clockStageCfg_step (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) (q : W.State) (hs : c.state = some q) :
    (obliviousSchedule W a).tm.step (clockStageCfg W a c) =
      clockStageCfg W a ((maskedClock W false).tm.step c) := by
  have hstate : (clockStageCfg W a c).state = some (.clock q) := by
    simp only [clockStageCfg, hs, Option.map_some, Option.getD_some]
  unfold MultiTapeTM.step
  rw [hstate, hs]
  dsimp only [obliviousSchedule, maskedClock]
  rw [clockStageCfg_input, clockStageCfg_work]
  let act := W.tm.tr q (c.inputSymbol.map (fun _ => false)) c.workTapeSymbols
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp only [Action.apply, clockStageCfg, moveInputPos, List.length_map]
    split <;> rfl
  · funext i z
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Action.apply, clockStageCfg, Fin.addCases_left]
      cases hw : (act.workTapes j).1 with
      | none => simp only [act, Option.map_none]
      | some b =>
        by_cases hz : z = c.workTapePos j
        · subst z
          simp only [act, Option.map_some, Function.update_self]
        · simp only [act, Option.map_some, Function.update_of_ne hz]
    · simp only [Action.apply, clockStageCfg, Fin.addCases_right]
      by_cases h0 : j.val = 0
      · simp only [if_pos h0]
        cases ho : act.output with
        | none => simp only [act, Option.toList_none, List.append_nil]
        | some b =>
          simp only [act, Option.toList_some, clockTape_append]
      · by_cases h1 : j.val = 1 <;> simp [h0, h1]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Action.apply, clockStageCfg, Fin.addCases_left]
    · simp only [Action.apply, clockStageCfg, Fin.addCases_right]
      by_cases h0 : j.val = 0
      · simp only [if_pos h0]
        cases ho : act.output <;> simp [act, List.length_append, ho] <;> omega
      · by_cases h1 : j.val = 1 <;> simp [h0, h1]
  · rfl

/-- Exhaust the three administrative tape indices. -/
private lemma finThree_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  have hj := j.isLt
  have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- The first schedule transition initializes both sentinels and starts the
clock in its source initial configuration. -/
private lemma clockStageCfg_init (W : FinTM Bool) (a : ℕ) (x : List Bool) :
    (obliviousSchedule W a).tm.step ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) =
      clockStageCfg W a ((maskedClock W false).tm.initCfg x) := by
  change (oblAction (k := W.k) (some (OblPhase.clock (a := a) W.tm.q₀)) 0
    (some (some .origin), .pos) (some (some .origin), .pos) (none, 0)).apply _ = _
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp [oblAction, clockStageCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, clockStageCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;>
        simp [oblAction, clockStageCfg, clockTape_nil]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, clockStageCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, clockStageCfg]
  · rfl

/-- Up to the clock's first halt, its entire initialized computation and every
emitted budget bit are represented by the concrete schedule.
**Proof sketch.** Sentinel initialization costs one transition. Every live
source step is exactly one captured clock step; induction stops at the source
halt before administrative rewinding starts. -/
private lemma clockStageCfg_run (W : FinTM Bool) (a : ℕ) (x : List Bool) (τ : ℕ)
    (hlive : ∀ t < τ, ((maskedClock W false).tm.runFrom
      ((maskedClock W false).tm.initCfg x) t).state ≠ none) :
    ∀ t ≤ τ, (obliviousSchedule W a).tm.runFrom
      ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) (t + 1) =
      clockStageCfg W a ((maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) t) := by
  intro t
  induction t with
  | zero => intro _; exact clockStageCfg_init W a x
  | succ t ih =>
    intro ht
    obtain ⟨q, hs⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), clockStageCfg_step W a _ q hs,
      ← MultiTapeTM.runFrom_succ_eq_step']

/-- The actual schedule captures the prescribed budget and reaches its rewind
phase within the clock bound plus one. No assumption that the original witness
is oblivious is used. -/
private lemma clockStageCfg_captures (W : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1))) (x : List Bool) :
    ∃ τ ≤ b * (T x.length + 1), ∃ c : Cfg W.k Bool W.State x,
      c.state = none ∧ c.output = (T x.length).bits ∧
      (obliviousSchedule W a).tm.runFrom
        ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) (τ + 1) = clockStageCfg W a c := by
  classical
  have hm := maskedClock_computes W T b hW x
  have hhalt := ((FinTM.computesInTime_iff _ _ _ _).mp hm).1
  have hex : ∃ t, ((maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) t).state = none :=
    ⟨_, hhalt⟩
  let τ := Nat.find hex
  have hs : ((maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) τ).state = none :=
    Nat.find_spec hex
  have ht : τ ≤ b * (T x.length + 1) := Nat.find_min' hex hhalt
  have hlive : ∀ t < τ, ((maskedClock W false).tm.runFrom
      ((maskedClock W false).tm.initCfg x) t).state ≠ none := fun _ h => Nat.find_min hex h
  let c := (maskedClock W false).tm.runFrom ((maskedClock W false).tm.initCfg x) τ
  have hc : (maskedClock W false).ComputesInTime x c.output τ :=
    (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  exact ⟨τ, ht, c, hs, hc.output_unique hm, clockStageCfg_run W a x τ hlive τ (le_refl _)⟩

/-- The fixed sweep guide has one marked origin and two structural boundaries. -/
private def guideTape (R : ℕ) (z : ℤ) : Option OblSymbol :=
  if z = -(R : ℤ) - 1 then some (.edge false)
  else if z = (R : ℤ) + 1 then some (.edge true)
  else if z = 0 then some .origin
  else if -(R : ℤ) ≤ z ∧ z ≤ R then some .inside else none

/-- The guide's left tag occurs exactly at its left boundary. -/
private lemma guideTape_left (R : ℕ) (z : ℤ) :
    guideTape R z = some (.edge false) ↔ z = -(R : ℤ) - 1 := by
  unfold guideTape
  split_ifs <;> simp_all

/-- The guide's right tag occurs exactly at its right boundary. -/
private lemma guideTape_right (R : ℕ) (z : ℤ) :
    guideTape R z = some (.edge true) ↔ z = (R : ℤ) + 1 := by
  unfold guideTape
  split_ifs <;> simp_all <;> omega

/-- The guide's origin tag occurs exactly at coordinate zero. -/
private lemma guideTape_origin (R : ℕ) (z : ℤ) :
    guideTape R z = some .origin ↔ z = 0 := by
  unfold guideTape
  split_ifs <;> simp_all <;> omega

/-- A macrostep configuration keeps every tape and the native input fixed;
only its phase and the unary/guide head positions vary. -/
private def macroCfg (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (u g : ℤ) : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x :=
  ⟨q, base.inputPos, base.workTapes,
    Fin.addCases (fun i => base.workTapePos (i.castAdd 3)) (fun j =>
      if j.val = 0 then base.workTapePos (Fin.natAdd W.k (0 : Fin 3))
      else if j.val = 1 then u else g), base.output⟩

/-- Read the unary counter from a macrostep configuration. -/
private lemma macroCfg_unary (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (u g : ℤ) :
    (macroCfg W a base q u g).workTapeSymbols (Fin.natAdd W.k (1 : Fin 3)) =
      base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u := by
  simp [macroCfg, Cfg.workTapeSymbols]

/-- Read the guide from a macrostep configuration. -/
private lemma macroCfg_guide (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (u g : ℤ) :
    (macroCfg W a base q u g).workTapeSymbols (Fin.natAdd W.k (2 : Fin 3)) =
      base.workTapes (Fin.natAdd W.k (2 : Fin 3)) g := by
  simp [macroCfg, Cfg.workTapeSymbols]

/-- A read-only schedule action updates exactly the two macrostep heads. -/
private lemma macroCfg_apply (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (u g : ℤ) (du dg : SignType) :
    (oblAction (k := W.k) q' 0 (none, 0) (none, du) (none, dg)).apply
      (macroCfg W a base q u g) = macroCfg W a base q' (u + du) (g + dg) := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, macroCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, macroCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, macroCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, macroCfg]
  · exact List.append_nil _

/-- One counter test starts a full macrostep or finishes the fixed schedule. -/
private lemma macroCfg_check (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .macroCheck) u g) =
      macroCfg W a base
        (if base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit then some .seekLeft else none) u g := by
  change ((obliviousSchedule W a).tm.tr .macroCheck _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_unary]
  split <;> rw [macroCfg_apply] <;> simp

/-- The outward scan turns only at the guide's left boundary. -/
private lemma macroCfg_seek (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .seekLeft) u g) =
      if g = -(R : ℤ) - 1 then macroCfg W a base (some .forward) u (g + 1)
      else macroCfg W a base (some .seekLeft) u (g - 1) := by
  change ((obliviousSchedule W a).tm.tr .seekLeft _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_left]
  split <;> rw [macroCfg_apply] <;> simp [sub_eq_add_neg]

/-- The forward scan turns only at the guide's right boundary. -/
private lemma macroCfg_forward (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .forward) u g) =
      if g = (R : ℤ) + 1 then macroCfg W a base (some .backward) u (g - 1)
      else macroCfg W a base (some .forward) u (g + 1) := by
  change ((obliviousSchedule W a).tm.tr .forward _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_right]
  split <;> rw [macroCfg_apply] <;> simp [sub_eq_add_neg]

/-- The return data scan turns only at the guide's left boundary. -/
private lemma macroCfg_backward (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .backward) u g) =
      if g = -(R : ℤ) - 1 then macroCfg W a base (some .returnCenter) u (g + 1)
      else macroCfg W a base (some .backward) u (g - 1) := by
  change ((obliviousSchedule W a).tm.tr .backward _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_left]
  split <;> rw [macroCfg_apply] <;> simp [sub_eq_add_neg]

/-- The final scan commits at the origin and advances exactly one unary cell. -/
private lemma macroCfg_center (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u g : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (obliviousSchedule W a).tm.step (macroCfg W a base (some .returnCenter) u g) =
      if g = 0 then macroCfg W a base (some .macroCheck) (u + 1) g
      else macroCfg W a base (some .returnCenter) u (g + 1) := by
  change ((obliviousSchedule W a).tm.tr .returnCenter _ _).apply _ = _
  simp only [obliviousSchedule, macroCfg_guide, hg, guideTape_origin]
  split <;> rw [macroCfg_apply] <;> simp

/-- Exact prefix of the scan from the origin to the left boundary. -/
private lemma macroCfg_seek_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ R + 1) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .seekLeft) u 0) n =
      macroCfg W a base (some .seekLeft) u (-(n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_seek W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- Exact prefix of a full forward scan. -/
private lemma macroCfg_forward_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ 2 * R + 1) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .forward) u (-(R : ℤ))) n =
      macroCfg W a base (some .forward) u (-(R : ℤ) + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_forward W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- Exact prefix of a full backward scan. -/
private lemma macroCfg_backward_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ 2 * R + 1) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .backward) u R) n =
      macroCfg W a base (some .backward) u ((R : ℤ) - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_backward W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- Exact prefix of the scan returning to the origin. -/
private lemma macroCfg_center_run (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R n : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) (hn : n ≤ R) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .returnCenter) u (-(R : ℤ))) n =
      macroCfg W a base (some .returnCenter) u (-(R : ℤ) + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), macroCfg_center W a base u _ R hg,
      if_neg (by omega)]
    congr 1
    omega

/-- **Exact macrostep duration.** A positive counter cell executes the entire
fixed path in exactly `6R+8` transitions and advances the counter by one.

**Proof sketch.** The initial counter test costs one transition. The outward
scan and turn cost `R+2`, each full data scan and turn costs `2R+2`, and the
return-to-origin scan and counter advance cost `R+1`. The exact scan-prefix
lemmas compose to give the complete final configuration. -/
private lemma macroCfg_cycle (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ) (R : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit) :
    (obliviousSchedule W a).tm.runFrom (macroCfg W a base (some .macroCheck) u 0) (6 * R + 8) =
      macroCfg W a base (some .macroCheck) (u + 1) 0 := by
  have hcheck : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .macroCheck) u 0) 1 = macroCfg W a base (some .seekLeft) u 0 := by
    simpa only [hu, ↓reduceIte] using macroCfg_check W a base u 0
  have hseek : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .seekLeft) u 0) (R + 2) =
      macroCfg W a base (some .forward) u (-(R : ℤ)) := by
    rw [show R + 2 = (R + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      macroCfg_seek_run W a base u R _ hg (le_refl _), macroCfg_seek W a base u _ R hg,
      if_pos (by omega)]
    congr 1
    omega
  have hfwd : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .forward) u (-(R : ℤ))) (2 * R + 2) =
      macroCfg W a base (some .backward) u R := by
    rw [show 2 * R + 2 = (2 * R + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      macroCfg_forward_run W a base u R _ hg (le_refl _), macroCfg_forward W a base u _ R hg,
      if_pos (by omega)]
    congr 1
    omega
  have hback : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .backward) u R) (2 * R + 2) =
      macroCfg W a base (some .returnCenter) u (-(R : ℤ)) := by
    rw [show 2 * R + 2 = (2 * R + 1) + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
      macroCfg_backward_run W a base u R _ hg (le_refl _), macroCfg_backward W a base u _ R hg,
      if_pos (by omega)]
    congr 1
    omega
  have hcenter : (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .returnCenter) u (-(R : ℤ))) (R + 1) =
      macroCfg W a base (some .macroCheck) (u + 1) 0 := by
    rw [MultiTapeTM.runFrom_succ_eq_step', macroCfg_center_run W a base u R _ hg (le_refl _),
      macroCfg_center W a base u _ R hg, if_pos (by omega)]
    congr 1
    omega
  rw [show 6 * R + 8 = 1 + ((R + 2) + ((2 * R + 2) + ((2 * R + 2) + (R + 1)))) by omega,
    MultiTapeTM.runFrom_add, hcheck, MultiTapeTM.runFrom_add, hseek,
    MultiTapeTM.runFrom_add, hfwd, MultiTapeTM.runFrom_add, hback, hcenter]

/-- Any initialized unary segment executes its exact number of macrosteps,
regardless of all simulated data and source halting behavior. -/
private lemma macroCfg_repeat (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (R B : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : ∀ j < B, base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((j : ℤ) + 1) = some .unit) :
    ∀ j ≤ B, (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .macroCheck) 1 0) (j * (6 * R + 8)) =
      macroCfg W a base (some .macroCheck) ((j : ℤ) + 1) 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Nat.succ_mul, MultiTapeTM.runFrom_add, ih (by omega),
      macroCfg_cycle W a base _ R hg (hu j (by omega))]
    congr 1

/-- The empty cell immediately following the unary budget ends the schedule
after exactly the budgeted macrosteps plus its final test. -/
private lemma macroCfg_finish (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (R B : ℕ)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : ∀ j < B, base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((j : ℤ) + 1) = some .unit)
    (hend : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((B : ℤ) + 1) = none) :
    (obliviousSchedule W a).tm.runFrom
      (macroCfg W a base (some .macroCheck) 1 0) (B * (6 * R + 8) + 1) =
      macroCfg W a base none ((B : ℤ) + 1) 0 := by
  rw [MultiTapeTM.runFrom_succ_eq_step', macroCfg_repeat W a base R B hg hu B (le_refl _),
    macroCfg_check, hend]
  rfl

/-- An explicit setup configuration separates the captured clock work from
the three controller tapes. It is also used before the native input is parked. -/
private def setupCfg (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x :=
  ⟨q, p, Fin.addCases (fun i => base.workTapes (i.castAdd 3))
    (fun j => if j.val = 0 then bt else if j.val = 1 then ut else gt),
    Fin.addCases (fun i => base.workTapePos (i.castAdd 3))
    (fun j => if j.val = 0 then b else if j.val = 1 then u else g), base.output⟩

/-- Applying a controller write to one explicit setup tape. -/
private def setupWrite {A : Type} (t : ℤ → Option A) (z : ℤ)
    (w : Option (Option A)) : ℤ → Option A :=
  match w with | none => t | some s => Function.update t z s

/-- Setup actions update precisely the three explicit tapes and their heads. -/
private lemma setupCfg_apply (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) (di : SignType)
    (ba ua ga : Option (Option OblSymbol) × SignType) :
    (oblAction (k := W.k) q' di ba ua ga).apply (setupCfg W a base q p b u g bt ut gt) =
      setupCfg W a base q' (moveInputPos p di) (b + ba.2) (u + ua.2) (g + ga.2)
        (setupWrite bt b ba.1) (setupWrite ut u ua.1) (setupWrite gt g ga.1) := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl
      · cases hb : ba.1 <;> simp [oblAction, setupCfg, setupWrite, hb]
      · cases hu : ua.1 <;> simp [oblAction, setupCfg, setupWrite, hu]
      · cases hg : ga.1 <;> simp [oblAction, setupCfg, setupWrite, hg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oblAction, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [oblAction, setupCfg]
  · exact List.append_nil _

/-- The native input read depends on the explicit setup input coordinate. -/
private lemma setupCfg_input (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    (setupCfg W a base q p b u g bt ut gt).inputSymbol =
      if p.val = 0 then none else x[p.val - 1]? := by
  unfold Cfg.inputSymbol
  simp only [setupCfg, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- Read the three controller tapes in an explicit setup configuration. -/
private lemma setupCfg_reads (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    (fun j : Fin 3 => (setupCfg W a base q p b u g bt ut gt).workTapeSymbols (j.natAdd W.k)) =
      fun j => if j.val = 0 then bt b else if j.val = 1 then ut u else gt g := by
  funext j
  rcases finThree_cases j with rfl | rfl | rfl <;> simp [setupCfg, Cfg.workTapeSymbols]

/-- The input reset scans a known interior prefix to the left boundary in
exactly its length, preserving every work tape and work head. -/
private lemma setupCfg_reset_scan (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) (j : ℕ) (hj : j ≤ x.length) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .resetScan) ⟨j, by omega⟩ b u g bt ut gt) j =
      setupCfg W a base (some .resetScan) 0 b u g bt ut gt := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hin : (setupCfg W a base (some .resetScan) ⟨j + 1, by omega⟩ b u g bt ut gt).inputSymbol =
        some (x[j]'(by omega)) := by
      rw [setupCfg_input]
      simp
    change (obliviousSchedule W a).tm.runFrom
      (((obliviousSchedule W a).tm.tr .resetScan _ _).apply _) j = _
    rw [show (obliviousSchedule W a).tm.tr .resetScan
        (setupCfg W a base (some .resetScan) ⟨j + 1, by omega⟩ b u g bt ut gt).inputSymbol
        _ = oblAction (k := W.k) (some .resetScan) .neg (none, 0) (none, 0) (none, 0) by
      simp only [obliviousSchedule, hin]]
    rw [setupCfg_apply]
    simp only [setupWrite, SignType.coe_zero, add_zero]
    have hp : moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .neg =
        ⟨j, by omega⟩ := by
      apply Fin.ext
      simp [moveInputPos, show j < x.length + 2 by omega]
    rw [hp]
    exact ih (by omega)

/-- Reset begins with a mandatory left move, so even the right blank boundary
and the empty input reach the left boundary before the final right move. -/
private lemma setupCfg_reset (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .resetStart) p b u g bt ut gt) (p.val - 1 + 2) =
      setupCfg W a base (some .copyLeft) ⟨1, by omega⟩ b u g bt ut gt := by
  have hp : moveInputPos p .neg = (⟨p.val - 1, by have := p.isLt; omega⟩ : Fin (x.length + 2)) := by
    apply Fin.ext
    simp only [moveInputPos, SignType.cast]
    split <;> simp_all <;> have := p.isLt <;> omega
  have hs : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .resetStart) p b u g bt ut gt) =
      setupCfg W a base (some .resetScan) ⟨p.val - 1, by have := p.isLt; omega⟩ b u g bt ut gt := by
    change ((obliviousSchedule W a).tm.tr .resetStart _ _).apply _ = _
    simp only [obliviousSchedule]
    rw [setupCfg_apply, hp]
    simp [setupWrite]
  have hs1 : (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .resetStart) p b u g bt ut gt) 1 =
      setupCfg W a base (some .resetScan) ⟨p.val - 1, by have := p.isLt; omega⟩ b u g bt ut gt := by
    simpa only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero] using hs
  rw [show p.val - 1 + 2 = 1 + (p.val - 1) + 1 by omega,
    MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hs1,
    setupCfg_reset_scan W a base b u g bt ut gt _ (by have := p.isLt; omega)]
  change ((obliviousSchedule W a).tm.tr .resetScan _ _).apply _ = _
  simp only [obliviousSchedule, setupCfg_input, Fin.val_zero, if_true]
  rw [setupCfg_apply]
  simp [setupWrite, moveInputPos]

/-- The partial guide after copying `j` native symbols. The left virtual
boundary has already been marked, and the origin is written on the first read. -/
private def copyGuide (j : ℕ) (z : ℤ) : Option OblSymbol :=
  if z = -1 then some .inside else if 0 ≤ z ∧ z < j then
    some (if z = 0 then .origin else .inside) else none

/-- The next copied symbol extends the guide by one cell. -/
private lemma copyGuide_next (j : ℕ) :
    Function.update (copyGuide j) (j : ℤ) (some (if j = 0 then .origin else .inside)) =
      copyGuide (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z
    simp [copyGuide, show (j : ℤ) ≠ -1 by omega]
  · rw [Function.update_of_ne hz]
    have hh : (0 ≤ z ∧ z < (j : ℤ)) ↔ (0 ≤ z ∧ z < (j + 1 : ℕ)) := by omega
    simp only [copyGuide, hh]

/-- On a completed copied prefix, only the origin carries its special tag. -/
private lemma copyGuide_origin (j : ℕ) (z : ℤ) (hj : 0 < j) :
    copyGuide j z = some .origin ↔ z = 0 := by
  unfold copyGuide
  split_ifs <;> simp_all <;> omega

/-- The first input read marks the origin; subsequent reads use the same
copy loop without changing that mark. -/
private def copyPhase {S : Type} {a : ℕ} (j : ℕ) : OblPhase S a :=
  if j = 0 then .copyFirst else .copyMore

/-- The two left-boundary setup steps precede every copy, including empty input. -/
private lemma setupCfg_copy_left (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .copyLeft) p b u 0 bt ut (fun _ => none)) 2 =
      setupCfg W a base (some (copyPhase 0)) p b u 0 bt ut (copyGuide 0) := by
  have hc : Function.update (fun _ : ℤ => (none : Option OblSymbol)) (-1) (some .inside) =
      copyGuide 0 := by
    funext z
    simp only [Function.update_apply, copyGuide, Int.natCast_zero]
    split_ifs <;> first | rfl | omega
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (obliviousSchedule W a).tm.step
      (((obliviousSchedule W a).tm.tr .copyLeft _ _).apply _) = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero,
    SignType.coe_neg_one, zero_add]
  change ((obliviousSchedule W a).tm.tr .copyLeftWrite _ _).apply _ = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp [setupWrite, hc, copyPhase]

/-- After any prefix of the copy scan, the native and guide heads have made
exactly the same number of right moves. No data value selects a movement. -/
private lemma setupCfg_copy_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u : ℤ) (bt ut : ℤ → Option OblSymbol) (j : ℕ) (hj : j ≤ x.length) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (copyPhase 0)) ⟨1, by omega⟩ b u 0 bt ut (copyGuide 0)) j =
      setupCfg W a base (some (copyPhase j)) ⟨j + 1, by omega⟩ b u j bt ut (copyGuide j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (setupCfg W a base (some (copyPhase j)) ⟨j + 1, by omega⟩ b u j bt ut
        (copyGuide j)).inputSymbol = some (x[j]'(by omega)) := by
      rw [setupCfg_input]
      simp
    have htr : ∀ ws, (obliviousSchedule W a).tm.tr (copyPhase j)
        (setupCfg W a base (some (copyPhase j)) ⟨j + 1, by omega⟩ b u j bt ut
          (copyGuide j)).inputSymbol ws =
        oblAction (k := W.k) (some (copyPhase (j + 1))) .pos (none, 0) (none, 0)
          (some (some (if j = 0 then .origin else .inside)), .pos) := by
      intro ws
      rw [hin]
      by_cases hz : j = 0 <;> simp [copyPhase, hz, obliviousSchedule]
    change ((obliviousSchedule W a).tm.tr (copyPhase j) _ _).apply _ = _
    rw [htr, setupCfg_apply]
    simp only [setupWrite, SignType.coe_zero, add_zero, SignType.coe_one, copyGuide_next]
    have hp : moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .pos =
        ⟨j + 1 + 1, by omega⟩ := by
      apply Fin.ext
      simp only [moveInputPos, SignType.cast]
      split <;> simp_all <;> omega
    rw [hp]
    rfl

/-- The final blank read parks the input head and closes the copied guide. -/
private lemma setupCfg_copy_end (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u : ℤ) (bt ut : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (copyPhase x.length)) ⟨x.length + 1, by omega⟩
        b u x.length bt ut (copyGuide x.length)) =
      setupCfg W a base (some .copyReturn) ⟨x.length + 1, by omega⟩
        b u x.length bt ut (copyGuide (x.length + 1)) := by
  have hin : (setupCfg W a base (some (copyPhase x.length)) ⟨x.length + 1, by omega⟩
      b u x.length bt ut (copyGuide x.length)).inputSymbol = none := by
    rw [setupCfg_input]
    simp
  change ((obliviousSchedule W a).tm.tr (copyPhase x.length) _ _).apply _ = _
  have htr : ∀ ws, (obliviousSchedule W a).tm.tr (copyPhase x.length)
      (setupCfg W a base (some (copyPhase x.length)) ⟨x.length + 1, by omega⟩
        b u x.length bt ut (copyGuide x.length)).inputSymbol ws =
      oblAction (k := W.k) (some .copyReturn) 0 (none, 0) (none, 0)
        (some (some (if x.length = 0 then .origin else .inside)), 0) := by
    intro ws
    rw [hin]
    by_cases hz : x.length = 0 <;> simp [copyPhase, hz, obliviousSchedule]
  rw [htr, setupCfg_apply]
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, copyGuide_next]

/-- Returning across the copied guide costs exactly its current coordinate. -/
private lemma setupCfg_copy_return (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut : ℤ → Option OblSymbol) (n j : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .copyReturn) p b u j bt ut (copyGuide (n + 1))) (j + 1) =
      setupCfg W a base (some .budgetStart) p b u 0 bt ut (copyGuide (n + 1)) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((obliviousSchedule W a).tm.tr .copyReturn _ _).apply _ = _
    have hr : (setupCfg W a base (some .copyReturn) p b u 0 bt ut (copyGuide (n + 1))).workTapeSymbols
        (Fin.natAdd W.k (2 : Fin 3)) = copyGuide (n + 1) 0 := by
      simp [setupCfg, Cfg.workTapeSymbols]
    simp only [Int.natCast_zero, obliviousSchedule, hr,
      copyGuide_origin _ _ (Nat.succ_pos _), ite_true]
    rw [setupCfg_apply]
    simp [setupWrite]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    change (obliviousSchedule W a).tm.runFrom
      (((obliviousSchedule W a).tm.tr .copyReturn _ _).apply _) (j + 1) = _
    have hr : (setupCfg W a base (some .copyReturn) p b u (j + 1) bt ut (copyGuide (n + 1))).workTapeSymbols
        (Fin.natAdd W.k (2 : Fin 3)) = copyGuide (n + 1) (j + 1) := by
      simp [setupCfg, Cfg.workTapeSymbols]
    simp only [Nat.cast_add, Nat.cast_one, obliviousSchedule, hr,
      copyGuide_origin _ _ (Nat.succ_pos _),
      show (j : ℤ) + 1 ≠ 0 by omega, ite_false]
    rw [setupCfg_apply]
    simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero]
    convert ih using 1 <;> congr 1 <;> simp [SignType.cast] <;> omega

/-- The unary macrostep budget, with an origin sentinel and a blank end cell. -/
private def unaryTape (N : ℕ) (z : ℤ) : Option OblSymbol :=
  if z = 0 then some .origin else if 1 ≤ z ∧ z ≤ N then some .unit else none

/-- Appending one unary marker extends exactly the allocated prefix. -/
private lemma unaryTape_next (N : ℕ) :
    Function.update (unaryTape N) ((N : ℤ) + 1) (some .unit) = unaryTape (N + 1) := by
  funext z
  by_cases hz : z = (N : ℤ) + 1
  · subst z
    simp [unaryTape, show (N : ℤ) + 1 ≠ 0 by omega]
  · rw [Function.update_of_ne hz]
    have hh : (1 ≤ z ∧ z ≤ (N : ℤ)) ↔ (1 ≤ z ∧ z ≤ (N + 1 : ℕ)) := by omega
    simp only [unaryTape, hh]

/-- Only the origin sentinel terminates the backwards budget scan. -/
private lemma clockTape_origin (w : List Bool) (z : ℤ) :
    clockTape w z = some .origin ↔ z = 0 := by
  by_cases hz : z = 0
  · simp [clockTape, hz]
  · simp only [clockTape, if_neg hz]
    cases FinTM.bufferTape w (z - 1) <;> simp [hz]

/-- The captured budget's right blank is one cell after its full fixed width. -/
private lemma clockTape_end (w : List Bool) : clockTape w ((w.length : ℤ) + 1) = none := by
  simp [clockTape, show (w.length : ℤ) + 1 ≠ 0 by omega]

/-- Rewinding the captured budget reaches its sentinel in exactly the head
coordinate, then moves right once to begin unary generation. -/
private lemma setupCfg_budget_back (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol) (j : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .budgetBack) p j u g (clockTape w) ut gt) (j + 1) =
      setupCfg W a base (some (.append 0)) p 1 u g (clockTape w) ut gt := by
  have step (j : ℕ) : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .budgetBack) p j u g (clockTape w) ut gt) =
      if j = 0 then setupCfg W a base (some (.append 0)) p 1 u g (clockTape w) ut gt
      else setupCfg W a base (some .budgetBack) p ((j : ℤ) - 1) u g (clockTape w) ut gt := by
    have hr : (setupCfg W a base (some .budgetBack) p j u g (clockTape w) ut gt).workTapeSymbols
        (Fin.natAdd W.k (0 : Fin 3)) = clockTape w j := by
      simp [setupCfg, Cfg.workTapeSymbols]
    change ((obliviousSchedule W a).tm.tr .budgetBack _ _).apply _ = _
    simp only [obliviousSchedule, hr, clockTape_origin, Int.natCast_eq_zero]
    split <;> rw [setupCfg_apply] <;> simp_all [setupWrite, sub_eq_add_neg]
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step, if_pos rfl]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step, if_neg (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using ih

/-- A full rewind starts one cell beyond the captured word and costs its
width plus two, independently of all budget bits. -/
private lemma setupCfg_budget_start (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .budgetStart) p (w.length + 1) u g (clockTape w) ut gt)
      (w.length + 2) =
      setupCfg W a base (some (.append 0)) p 1 u g (clockTape w) ut gt := by
  have hs : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .budgetStart) p (w.length + 1) u g (clockTape w) ut gt) =
      setupCfg W a base (some .budgetBack) p w.length u g (clockTape w) ut gt := by
    change ((obliviousSchedule W a).tm.tr .budgetStart _ _).apply _ = _
    simp only [obliviousSchedule]
    rw [setupCfg_apply]
    simp [setupWrite]
  rw [show w.length + 2 = (w.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs, setupCfg_budget_back]

/-- Each finite append phase writes exactly one marker; the phase counter
and unary coordinate advance together through the prescribed constant block. -/
private lemma setupCfg_append_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N j : ℕ)
    (hj : j ≤ a + 1) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.append 0)) p b (N + 1) g bt (unaryTape N) gt) j =
      setupCfg W a base (some (.append ⟨j, by omega⟩)) p b (N + j + 1) g bt
        (unaryTape (N + j)) gt := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    change ((obliviousSchedule W a).tm.tr (.append ⟨j, by omega⟩) _ _).apply _ = _
    simp only [obliviousSchedule, show j < a + 1 by omega, dite_true]
    rw [setupCfg_apply]
    simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero]
    rw [show (N : ℤ) + j + 1 = ((N + j : ℕ) : ℤ) + 1 by omega, unaryTape_next]
    congr 1 <;> simp [SignType.cast] <;> omega

/-- Exactly `a+1` appended markers precede the next full-width borrow pass. -/
private lemma setupCfg_append (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.append 0)) p b (N + 1) g bt (unaryTape N) gt) (a + 2) =
      setupCfg W a base (some (.borrow true)) p b (N + (a + 1) + 1) g bt
        (unaryTape (N + (a + 1))) gt := by
  rw [MultiTapeTM.runFrom_succ_eq_step',
    setupCfg_append_prefix W a base p b g bt gt N (a + 1) (le_refl _)]
  change ((obliviousSchedule W a).tm.tr (.append ⟨a + 1, by omega⟩) _ _).apply _ = _
  simp only [obliviousSchedule, lt_self_iff_false, dite_false]
  rw [setupCfg_apply]
  simp [setupWrite]

/-- Moving a zipper frontier past an unchanged finite word preserves its tape. -/
private lemma sweepTape_shift {A : Type} (z : ℤ) (l w r : List (Option A)) :
    FinTM.sweepTape z l (w ++ r) =
      FinTM.sweepTape (z + w.length) (w.reverse ++ l) r := by
  induction w generalizing z l with
  | nil => simp
  | cons a w ih =>
    have hs : Function.update (FinTM.sweepTape z l (a :: (w ++ r))) z a =
        FinTM.sweepTape z l (a :: (w ++ r)) := by
      funext p
      by_cases hp : p = z
      · subst p
        simp [FinTM.sweepTape_read]
      · exact Function.update_of_ne hp _ _
    have hm := FinTM.sweepTape_right z l (w ++ r) a a
    rw [hs] at hm
    simp only [List.cons_append, List.length_cons, List.reverse_cons]
    rw [hm, ih]
    simp only [List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- A captured budget word is the same tape as its explicit bit zipper. -/
private lemma clockTape_zipper (w : List Bool) :
    clockTape w = FinTM.sweepTape 1 [some .origin] (w.map (fun b => some (.bit b))) := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [clockTape, FinTM.sweepTape]
  · by_cases hl : z < 1
    · have hn : ¬0 ≤ z - 1 := by omega
      have hi : 1 ≤ (1 - 1 - z).toNat := by omega
      have he : ([some OblSymbol.origin] : List (Option OblSymbol))[(1 - 1 - z).toNat]? = none :=
        List.getElem?_eq_none hi
      simp only [clockTape, if_neg hz, FinTM.bufferTape, if_neg hn, Option.map_none,
        FinTM.sweepTape, if_pos hl, he, Option.join_none]
    · have hn : 0 ≤ z - 1 := by omega
      simp only [clockTape, if_neg hz, FinTM.bufferTape, if_pos hn,
        FinTM.sweepTape, if_neg hl, List.getElem?_map]
      cases w[(z - 1).toNat]? <;> rfl

/-- The rewritten word's end zipper reconstructs the complete captured tape. -/
private lemma clockTape_zipper_end (w : List Bool) :
    FinTM.sweepTape (1 + (w.length : ℤ))
      ((w.map (fun b => some (.bit b))).reverse ++ [some .origin]) [] = clockTape w := by
  rw [clockTape_zipper]
  have h := sweepTape_shift (A := OblSymbol) 1 [some .origin]
    (w.map (fun b => some (.bit b))) []
  simpa only [List.append_nil, List.length_map] using h.symm

/-- Focusing the captured-budget lane preserves the explicit setup structure. -/
private lemma laneCfg_setup (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g z : ℤ) (bt ut gt : ℤ → Option OblSymbol) (l r : List (Option OblSymbol)) :
    laneCfg (setupCfg W a base q p b u g bt ut gt) (Fin.natAdd W.k (0 : Fin 3)) q' z l r =
      setupCfg W a base q' p z u g (FinTM.sweepTape z l r) ut gt := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hn : j.castAdd 3 ≠ Fin.natAdd W.k (0 : Fin 3) := by
        intro he
        have hh := congrArg Fin.val he
        change j.val = W.k + 0 at hh
        have := j.isLt
        omega
      simp [laneCfg, setupCfg, hn]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [laneCfg, setupCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hn : j.castAdd 3 ≠ Fin.natAdd W.k (0 : Fin 3) := by
        intro he
        have hh := congrArg Fin.val he
        change j.val = W.k + 0 at hh
        have := j.isLt
        omega
      simp [laneCfg, setupCfg, hn]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [laneCfg, setupCfg]
  · rfl

/-- The full-width borrow pass acts on the actual captured-budget tape while
all other setup tapes and the parked native input remain fixed. -/
private lemma setupCfg_borrow (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol)
    (carry : Bool) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.borrow carry)) p 1 u g (clockTape w) ut gt) w.length =
      setupCfg W a base (some (.borrow (budgetBorrow carry w).1)) p (1 + w.length) u g
        (clockTape (budgetBorrow carry w).2) ut gt := by
  have h := obliviousSchedule_borrow_run W a
    (setupCfg W a base (some (.borrow carry)) p 1 u g (clockTape w) ut gt)
    carry w 1 [some .origin] []
  rw [laneCfg_setup, laneCfg_setup] at h
  simp only [List.append_nil, ← clockTape_zipper] at h
  have he : (1 : ℤ) + w.length = 1 + (budgetBorrow carry w).2.length := by
    rw [budgetBorrow_length]
  rw [he, clockTape_zipper_end] at h
  simpa only [budgetBorrow_length] using h

/-- The blank after a full borrow selects either the next fixed-width pass
or the allocation stage, according only to the budget underflow flag. -/
private lemma setupCfg_borrow_end (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (u g : ℤ) (w : List Bool) (ut gt : ℤ → Option OblSymbol)
    (carry : Bool) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (.borrow carry)) p (w.length + 1) u g (clockTape w) ut gt) =
      setupCfg W a base (some (if carry then .unaryStart else .budgetStart)) p
        (w.length + 1) u g (clockTape w) ut gt := by
  have hr : (setupCfg W a base (some (.borrow carry)) p (w.length + 1) u g
      (clockTape w) ut gt).workTapeSymbols (Fin.natAdd W.k (0 : Fin 3)) = none := by
    simp [setupCfg, Cfg.workTapeSymbols, clockTape_end]
  change ((obliviousSchedule W a).tm.tr (.borrow carry) _ _).apply _ = _
  simp only [obliviousSchedule, hr]
  split <;> rw [setupCfg_apply] <;> simp_all [setupWrite]

/-- One complete controller round has a content-independent cost at the
captured word's fixed width: rewind, append a constant block, borrow, end test. -/
private lemma setupCfg_budget_round (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (g : ℤ) (w : List Bool) (gt : ℤ → Option OblSymbol) (N : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .budgetStart) p (w.length + 1) (N + 1) g
        (clockTape w) (unaryTape N) gt) (2 * w.length + (a + 1) + 4) =
      setupCfg W a base
        (some (if (budgetBorrow true w).1 then .unaryStart else .budgetStart)) p
        (w.length + 1) (N + (a + 1) + 1) g
        (clockTape (budgetBorrow true w).2) (unaryTape (N + (a + 1))) gt := by
  rw [show 2 * w.length + (a + 1) + 4 = (w.length + 2) + ((a + 2) + (w.length + 1)) by omega,
    MultiTapeTM.runFrom_add, setupCfg_budget_start, MultiTapeTM.runFrom_add, setupCfg_append,
    MultiTapeTM.runFrom_succ_eq_step', setupCfg_borrow]
  have h := setupCfg_borrow_end W a base p (N + (a + 1) + 1) g (budgetBorrow true w).2
    (unaryTape (N + (a + 1))) gt (budgetBorrow true w).1
  simpa only [budgetBorrow_length, add_comm (1 : ℤ)] using h

/-- The counter constructor executes exactly one round for each budget value
down to zero. Its final unary length is therefore `(a+1)(v+1)` plus the
previous prefix, with no width loss when the binary word acquires high zeros. -/
private lemma setupCfg_budget_all (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (g : ℤ) (gt : ℤ → Option OblSymbol) (v : ℕ) :
    ∀ (w : List Bool) (N : ℕ), budgetValue w = v →
      ∃ w' : List Bool, w'.length = w.length ∧
        (obliviousSchedule W a).tm.runFrom
          (setupCfg W a base (some .budgetStart) p (w.length + 1) (N + 1) g
            (clockTape w) (unaryTape N) gt)
          ((v + 1) * (2 * w.length + (a + 1) + 4)) =
          setupCfg W a base (some .unaryStart) p (w.length + 1)
            (N + (a + 1) * (v + 1) + 1) g
            (clockTape w') (unaryTape (N + (a + 1) * (v + 1))) gt := by
  induction v with
  | zero =>
    intro w N hv
    refine ⟨(budgetBorrow true w).2, budgetBorrow_length _ _, ?_⟩
    have hf := (budgetBorrow_underflow w).2 hv
    simpa only [Int.natCast_zero, zero_add, one_mul, Nat.mul_one, Int.natCast_one, mul_one, hf, if_true]
      using setupCfg_budget_round W a base p g w gt N
  | succ v ih =>
    intro w N hv
    have hpos : 0 < budgetValue w := by omega
    have hval : budgetValue (budgetBorrow true w).2 = v := by
      have := budgetBorrow_value w hpos
      omega
    have hf : (budgetBorrow true w).1 = false := by
      cases hh : (budgetBorrow true w).1
      · rfl
      · have := (budgetBorrow_underflow w).1 hh
        omega
    obtain ⟨w', hlen, hrun⟩ := ih (budgetBorrow true w).2 (N + (a + 1)) hval
    refine ⟨w', hlen.trans (budgetBorrow_length _ _), ?_⟩
    rw [show (v + 1 + 1) * (2 * w.length + (a + 1) + 4) =
        (2 * w.length + (a + 1) + 4) + (v + 1) * (2 * w.length + (a + 1) + 4) by ring,
      MultiTapeTM.runFrom_add, setupCfg_budget_round, hf]
    simp only [Bool.false_eq_true, ite_false]
    simp only [budgetBorrow_length, Nat.cast_add, Nat.cast_one] at hrun
    convert hrun using 1 <;> congr 1 <;> push_cast <;> ring

/-- Only the unary sentinel has the origin tag. -/
private lemma unaryTape_origin (N : ℕ) (z : ℤ) : unaryTape N z = some .origin ↔ z = 0 := by
  unfold unaryTape
  split_ifs <;> simp_all

/-- Every allocated unary marker is present, and the following cell is blank. -/
private lemma unaryTape_unit (N j : ℕ) (hj : j < N) : unaryTape N ((j : ℤ) + 1) = some .unit := by
  simp [unaryTape, show (j : ℤ) + 1 ≠ 0 by omega, show (j : ℤ) + 1 ≤ N by omega]

/-- The fixed unary segment is terminated by a blank cell. -/
private lemma unaryTape_end (N : ℕ) : unaryTape N ((N : ℤ) + 1) = none := by
  simp [unaryTape, show (N : ℤ) + 1 ≠ 0 by omega]

/-- Both unary rewinds use the same path; only their successor phase differs. -/
private def unaryRewindPhase {S : Type} {a : ℕ} (last : Bool) : OblPhase S a :=
  if last then .unaryReset else .unaryBack

/-- A unary rewind crosses exactly the prescribed number of cells and returns
to cell one. It does not inspect any simulated source data. -/
private lemma setupCfg_unary_rewind (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N j : ℕ) (last : Bool) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (unaryRewindPhase last)) p b j g bt (unaryTape N) gt) (j + 1) =
      setupCfg W a base (some (if last then .startCenter else .layoutRight 0)) p b 1 g bt (unaryTape N) gt := by
  have step (j : ℕ) : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (unaryRewindPhase last)) p b j g bt (unaryTape N) gt) =
      if j = 0 then
        setupCfg W a base (some (if last then .startCenter else .layoutRight 0)) p b 1 g bt (unaryTape N) gt
      else setupCfg W a base (some (unaryRewindPhase last)) p b ((j : ℤ) - 1) g bt (unaryTape N) gt := by
    have hr : (setupCfg W a base (some (unaryRewindPhase last)) p b j g bt (unaryTape N) gt).workTapeSymbols
        (Fin.natAdd W.k (1 : Fin 3)) = unaryTape N j := by
      simp [setupCfg, Cfg.workTapeSymbols]
    change ((obliviousSchedule W a).tm.tr (unaryRewindPhase last) _ _).apply _ = _
    have h0 : unaryTape N j = some .origin ↔ j = 0 := by
      rw [unaryTape_origin, Int.natCast_eq_zero]
    cases last <;> simp only [unaryRewindPhase, Bool.false_eq_true, ite_false, ite_true] at hr ⊢
    all_goals
      simp only [obliviousSchedule, hr, h0]
      split <;> rw [setupCfg_apply] <;> simp_all [setupWrite, sub_eq_add_neg]
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step, if_pos rfl]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step, if_neg (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using ih

/-- Allocation begins by rewinding the complete newly constructed unary segment. -/
private lemma setupCfg_unary_start (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (N : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .unaryStart) p b (N + 1) g bt (unaryTape N) gt) (N + 2) =
      setupCfg W a base (some (.layoutRight 0)) p b 1 g bt (unaryTape N) gt := by
  have hs : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .unaryStart) p b (N + 1) g bt (unaryTape N) gt) =
      setupCfg W a base (some (unaryRewindPhase false)) p b N g bt (unaryTape N) gt := by
    change ((obliviousSchedule W a).tm.tr .unaryStart _ _).apply _ = _
    simp only [obliviousSchedule]
    rw [setupCfg_apply]
    simp [setupWrite, unaryRewindPhase]
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, setupCfg_unary_rewind]
  rfl

/-- The guide's common interior mark, retaining its unique origin. -/
private def guideMark (z : ℤ) : OblSymbol := if z = 0 then .origin else .inside

/-- An allocation prefix overwrites the first `j` cells in the chosen direction.
Every overwritten cell receives a structural mark, independently of input bits. -/
private def guideFill (right : Bool) (gt : ℤ → Option OblSymbol) (j : ℕ) (z : ℤ) : Option OblSymbol :=
  if 0 ≤ (if right then z else -z) ∧ (if right then z else -z) < j
    then some (guideMark z) else gt z

/-- An empty allocation prefix leaves the copied guide unchanged. -/
private lemma guideFill_zero (right : Bool) (gt : ℤ → Option OblSymbol) : guideFill right gt 0 = gt := by
  funext z
  simp only [guideFill, Int.natCast_zero]
  rw [if_neg (by omega)]

/-- Allocating guide cells preserves uniqueness of the origin. -/
private lemma guideFill_origin (right : Bool) (gt : ℤ → Option OblSymbol)
    (hg : ∀ z, gt z = some .origin ↔ z = 0) (j : ℕ) (z : ℤ) :
    guideFill right gt j z = some .origin ↔ z = 0 := by
  unfold guideFill guideMark
  split_ifs <;> simp_all [hg]

/-- Each allocation write extends the prefix by exactly one cell. -/
private lemma guideFill_next (right : Bool) (gt : ℤ → Option OblSymbol) (j : ℕ) :
    Function.update (guideFill right gt j) (if right then (j : ℤ) else -(j : ℤ))
      (some (guideMark (if right then (j : ℤ) else -(j : ℤ)))) = guideFill right gt (j + 1) := by
  funext z
  by_cases hz : z = if right then (j : ℤ) else -(j : ℤ)
  · subst z
    cases right <;> simp [guideFill]
  · rw [Function.update_of_ne hz]
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hz ⊢
    all_goals
      unfold guideFill
      simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_add, Nat.cast_one]
      split_ifs <;> first | rfl | omega

/-- The two outward allocation passes have symmetric finite phases. -/
private def layoutPhase {S : Type} {a : ℕ} (right : Bool) (i : Fin 3) : OblPhase S a :=
  if right then .layoutRight i else .layoutLeft i

/-- Allocation movement direction, independent of the cell contents. -/
private def layoutMove (right : Bool) : SignType := if right then .pos else .neg

/-- A single allocation step follows the fixed three-cell-per-marker controller. -/
private lemma setupCfg_layout_step (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol)
    (right : Bool) (i : Fin 3) (hu : ut u = some .unit)
    (hg : gt g = some .origin ↔ g = 0) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (layoutPhase right i)) p b u g bt ut gt) =
      setupCfg W a base (some (layoutPhase right (nextThird i))) p b
        (u + (if i.val = 2 then (1 : ℤ) else 0)) (g + (layoutMove right : ℤ)) bt ut
        (Function.update gt g (some (guideMark g))) := by
  have hu' : (setupCfg W a base (some (layoutPhase right i)) p b u g bt ut gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = ut u := by simp [setupCfg, Cfg.workTapeSymbols]
  have hg' : (setupCfg W a base (some (layoutPhase right i)) p b u g bt ut gt).workTapeSymbols
      (Fin.natAdd W.k (2 : Fin 3)) = gt g := by simp [setupCfg, Cfg.workTapeSymbols]
  change ((obliviousSchedule W a).tm.tr (layoutPhase right i) _ _).apply _ = _
  cases right <;> simp only [layoutPhase, Bool.false_eq_true, ite_false, ite_true] at hu' hg' ⊢
  all_goals
    simp only [obliviousSchedule, hu', hg', hu, hg, ite_true]
    rw [setupCfg_apply]
    simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, guideMark]
    by_cases hi : i.val = 2 <;> simp [layoutPhase, layoutMove, hi]

/-- A local allocation write advances the explicit filled-guide invariant. -/
private lemma setupCfg_layout_fill (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut gt : ℤ → Option OblSymbol)
    (right : Bool) (i : Fin 3) (j : ℕ) (hu : ut u = some .unit)
    (hg : ∀ z, gt z = some .origin ↔ z = 0) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (layoutPhase right i)) p b u
        (if right then (j : ℤ) else -(j : ℤ)) bt ut (guideFill right gt j)) =
      setupCfg W a base (some (layoutPhase right (nextThird i))) p b
        (u + (if i.val = 2 then (1 : ℤ) else 0))
        (if right then ((j + 1 : ℕ) : ℤ) else -((j + 1 : ℕ) : ℤ)) bt ut (guideFill right gt (j + 1)) := by
  rw [setupCfg_layout_step W a base p b u _ bt ut _ right i hu (guideFill_origin right gt hg j _),
    guideFill_next]
  cases right <;> simp [layoutMove] <;> congr 1 <;> omega

/-- The finite allocation phase is the remainder modulo three of the number
of guide cells already written. -/
private lemma nextThird_mod (j : ℕ) :
    nextThird ⟨j % 3, Nat.mod_lt _ (by omega)⟩ =
      ⟨(j + 1) % 3, Nat.mod_lt _ (by omega)⟩ := by
  apply Fin.ext
  rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with h | h | h
  all_goals simp [nextThird, h] <;> omega

/-- Every prefix of an outward allocation pass has exact time equal to its
number of guide cells, with the unary head moving once every three cells. -/
private lemma setupCfg_layout_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt gt : ℤ → Option OblSymbol)
    (right : Bool) (B j : ℕ) (hj : j ≤ 3 * B)
    (hg : ∀ z, gt z = some .origin ↔ z = 0) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (layoutPhase right 0)) p b 1 0 bt (unaryTape B) gt) j =
      setupCfg W a base (some (layoutPhase right ⟨j % 3, Nat.mod_lt _ (by omega)⟩)) p b
        (((j / 3 : ℕ) : ℤ) + 1) (if right then (j : ℤ) else -(j : ℤ)) bt (unaryTape B) (guideFill right gt j) := by
  induction j with
  | zero => cases right <;> simp [guideFill_zero]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hu : unaryTape B ((j / 3 : ℕ) + 1) = some .unit := by
      have hh := unaryTape_unit B (j / 3) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    rw [setupCfg_layout_fill W a base p b _ bt (unaryTape B) gt right _ j hu hg, nextThird_mod]
    congr 1
    simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    split <;> omega

/-- At the fixed end of an allocation pass, the blank unary cell causes one
final interior write and moves to the outer boundary marker. -/
private lemma setupCfg_layout_end (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b g : ℤ) (bt gt : ℤ → Option OblSymbol) (right : Bool) (B : ℕ) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (layoutPhase right 0)) p b (B + 1) g bt (unaryTape B) gt) =
      setupCfg W a base (some (if right then .rightEdge else .leftEdge)) p b (B + 1)
        (g + (layoutMove right : ℤ)) bt (unaryTape B) (Function.update gt g (some .inside)) := by
  have hu : (setupCfg W a base (some (layoutPhase right 0)) p b (B + 1) g bt (unaryTape B) gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = none := by
    simp [setupCfg, Cfg.workTapeSymbols, unaryTape_end]
  change ((obliviousSchedule W a).tm.tr (layoutPhase right 0) _ _).apply _ = _
  cases right <;> simp only [layoutPhase, Bool.false_eq_true, ite_false, ite_true] at hu ⊢
  all_goals
    simp only [obliviousSchedule, hu, reduceCtorEq, ite_false]
    rw [setupCfg_apply]
    simp [setupWrite, layoutMove]

/-- The positive half of the guide, with its right outer boundary installed. -/
private def rightGuide (R : ℕ) : ℤ → Option OblSymbol :=
  Function.update (copyGuide (R + 1)) ((R : ℤ) + 1) (some (.edge true))

/-- Extending the copied guide to a radius containing the input overwrites
exactly its positive prefix. -/
private lemma guideFill_right_copy (n R : ℕ) (hn : n + 1 ≤ R) :
    guideFill true (copyGuide (n + 1)) R = copyGuide R := by
  funext z
  simp only [guideFill, ite_true, guideMark, copyGuide, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega

/-- The right-boundary write cannot alter the origin. -/
private lemma rightGuide_origin (R : ℕ) (z : ℤ) : rightGuide R z = some .origin ↔ z = 0 := by
  by_cases hz : z = (R : ℤ) + 1
  · subst z
    simp [rightGuide, show (R : ℤ) + 1 ≠ 0 by omega]
  · rw [rightGuide, Function.update_of_ne hz, copyGuide_origin _ _ (Nat.succ_pos _)]

/-- Filling the negative half and marking its boundary produces the complete
fixed guide, including the original left input boundary inside the interval. -/
private lemma guideFill_left_finish (R : ℕ) (hR : 0 < R) :
    Function.update
      (Function.update (guideFill false (rightGuide R) R) (-(R : ℤ)) (some .inside))
      (-(R : ℤ) - 1) (some (.edge false)) = guideTape R := by
  funext z
  simp only [Function.update_apply, guideFill, Bool.false_eq_true, ite_false,
    rightGuide, copyGuide, guideMark, guideTape, Nat.cast_add, Nat.cast_one]
  split_ifs <;> first | rfl | omega

/-- The right-boundary transition starts a read-only return across the newly
allocated half, decrementing the unary counter once before that return. -/
private lemma setupCfg_right_edge (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (B R : ℕ) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .rightEdge) p b (B + 1) (R + 1) bt (unaryTape B) (copyGuide (R + 1))) =
      setupCfg W a base (some (.layoutReturn 0)) p b B R bt (unaryTape B) (rightGuide R) := by
  change ((obliviousSchedule W a).tm.tr .rightEdge _ _).apply _ = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp [setupWrite, rightGuide]

/-- A return-allocation step does not write any tape and moves the unary head
left once per three guide cells. -/
private lemma setupCfg_layout_return_step (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u g : ℤ) (bt ut gt : ℤ → Option OblSymbol)
    (i : Fin 3) (hu : ut u ≠ some .origin) :
    (obliviousSchedule W a).tm.step
      (setupCfg W a base (some (.layoutReturn i)) p b u g bt ut gt) =
      setupCfg W a base (some (.layoutReturn (nextThird i))) p b
        (u - (if i.val = 2 then (1 : ℤ) else 0)) (g - 1) bt ut gt := by
  have hr : (setupCfg W a base (some (.layoutReturn i)) p b u g bt ut gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = ut u := by simp [setupCfg, Cfg.workTapeSymbols]
  change ((obliviousSchedule W a).tm.tr (.layoutReturn i) _ _).apply _ = _
  simp only [obliviousSchedule, hr, if_neg hu]
  rw [setupCfg_apply]
  by_cases hi : i.val = 2 <;> simp [setupWrite, hi, sub_eq_add_neg]

/-- Every prefix of the return allocation has its exact deterministic state
and head positions, with all guide marks unchanged. -/
private lemma setupCfg_layout_return_prefix (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt gt : ℤ → Option OblSymbol) (B j : ℕ) (hj : j ≤ 3 * B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutReturn 0)) p b B (3 * B) bt (unaryTape B) gt) j =
      setupCfg W a base (some (.layoutReturn ⟨j % 3, Nat.mod_lt _ (by omega)⟩)) p b
        ((B : ℤ) - ((j / 3 : ℕ) : ℤ)) (3 * (B : ℤ) - j) bt (unaryTape B) gt := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hu : unaryTape B ((B : ℤ) - ((j / 3 : ℕ) : ℤ)) ≠ some .origin := by
      intro hh
      have := (unaryTape_origin B _).1 hh
      omega
    rw [setupCfg_layout_return_step W a base p b _ _ bt (unaryTape B) gt _ hu, nextThird_mod]
    congr 1
    · simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
      split <;> omega
    · push_cast
      omega

/-- The completed return allocation reaches the origin and starts the left
allocation pass, restoring the unary counter to cell one. -/
private lemma setupCfg_layout_return (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt gt : ℤ → Option OblSymbol) (B : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutReturn 0)) p b B (3 * B) bt (unaryTape B) gt) (3 * B + 1) =
      setupCfg W a base (some (.layoutLeft 0)) p b 1 0 bt (unaryTape B) gt := by
  rw [MultiTapeTM.runFrom_succ_eq_step', setupCfg_layout_return_prefix W a base p b bt gt B _ (le_refl _)]
  simp only [Nat.mul_mod_right, show 3 * B / 3 = B by omega,
    Nat.cast_mul, Nat.cast_ofNat, sub_self, Fin.mk_zero]
  have hr : (setupCfg W a base (some (.layoutReturn 0)) p b 0 0 bt (unaryTape B) gt).workTapeSymbols
      (Fin.natAdd W.k (1 : Fin 3)) = some .origin := by simp [setupCfg, Cfg.workTapeSymbols, unaryTape]
  change ((obliviousSchedule W a).tm.tr (.layoutReturn 0) _ _).apply _ = _
  simp only [obliviousSchedule, hr, ite_true]
  rw [setupCfg_apply]
  simp [setupWrite]

/-- The positive allocation pass reaches radius `3B`, installs its outer
boundary, and starts the read-only return in exactly `3B+2` transitions. -/
private lemma setupCfg_layout_right (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (n B : ℕ) (hn : n + 1 ≤ B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutRight 0)) p b 1 0 bt (unaryTape B) (copyGuide (n + 1)))
      (3 * B + 2) =
      setupCfg W a base (some (.layoutReturn 0)) p b B (3 * B) bt (unaryTape B) (rightGuide (3 * B)) := by
  have hprefix := setupCfg_layout_prefix W a base p b bt (copyGuide (n + 1)) true B (3 * B)
    (le_refl _) (fun z => copyGuide_origin _ z (Nat.succ_pos _))
  simp only [layoutPhase, ite_true, Nat.mul_mod_right, show 3 * B / 3 = B by omega,
    guideFill_right_copy n (3 * B) (by omega), Nat.cast_mul, Nat.cast_ofNat, Fin.mk_zero] at hprefix
  have hput := setupCfg_layout_end W a base p b (3 * B) bt (copyGuide (3 * B)) true B
  have he : Function.update (copyGuide (3 * B)) (3 * (B : ℤ)) (some .inside) = copyGuide (3 * B + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, if_neg (show 3 * B ≠ 0 by omega)] using copyGuide_next (3 * B)
  simp only [layoutPhase, layoutMove, ite_true, SignType.cast, he] at hput
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', hprefix, hput]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using setupCfg_right_edge W a base p b bt B (3 * B)

/-- The negative allocation pass completes the fixed guide and leaves its
head at the left outer boundary, ready for the final unary rewind. -/
private lemma setupCfg_layout_left (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (B : ℕ) (hB : 0 < B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some (.layoutLeft 0)) p b 1 0 bt (unaryTape B) (rightGuide (3 * B)))
      (3 * B + 2) =
      setupCfg W a base (some .unaryReset) p b B (-(3 * (B : ℤ)) - 1) bt (unaryTape B) (guideTape (3 * B)) := by
  have hprefix := setupCfg_layout_prefix W a base p b bt (rightGuide (3 * B)) false B (3 * B)
    (le_refl _) (rightGuide_origin (3 * B))
  simp only [layoutPhase, Bool.false_eq_true, ite_false, Nat.mul_mod_right,
    show 3 * B / 3 = B by omega, Nat.cast_mul, Nat.cast_ofNat, Fin.mk_zero] at hprefix
  have hput := setupCfg_layout_end W a base p b (-(3 * (B : ℤ))) bt
    (guideFill false (rightGuide (3 * B)) (3 * B)) false B
  simp only [layoutPhase, layoutMove, Bool.false_eq_true, ite_false, SignType.cast, ← sub_eq_add_neg] at hput
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', hprefix, hput]
  change ((obliviousSchedule W a).tm.tr .leftEdge _ _).apply _ = _
  simp only [obliviousSchedule]
  rw [setupCfg_apply]
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero]
  have hg := guideFill_left_finish (3 * B) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hg
  rw [hg]
  congr 1
  simp [SignType.cast]

/-- The final allocation scan reaches the origin in its coordinate distance,
then enters the macrostep controller in one additional transition. -/
private lemma setupCfg_start_center (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b u : ℤ) (bt ut : ℤ → Option OblSymbol) (R j : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .startCenter) p b u (-(j : ℤ)) bt ut (guideTape R)) (j + 1) =
      setupCfg W a base (some .macroCheck) p b u 0 bt ut (guideTape R) := by
  have step (j : ℕ) : (obliviousSchedule W a).tm.step
      (setupCfg W a base (some .startCenter) p b u (-(j : ℤ)) bt ut (guideTape R)) =
      if j = 0 then setupCfg W a base (some .macroCheck) p b u 0 bt ut (guideTape R)
      else setupCfg W a base (some .startCenter) p b u (-(j : ℤ) + 1) bt ut (guideTape R) := by
    have hr : (setupCfg W a base (some .startCenter) p b u (-(j : ℤ)) bt ut (guideTape R)).workTapeSymbols
        (Fin.natAdd W.k (2 : Fin 3)) = guideTape R (-(j : ℤ)) := by
      simp [setupCfg, Cfg.workTapeSymbols]
    change ((obliviousSchedule W a).tm.tr .startCenter _ _).apply _ = _
    simp only [obliviousSchedule, hr, guideTape_origin, neg_eq_zero, Int.natCast_eq_zero]
    split <;> rw [setupCfg_apply] <;> simp_all [setupWrite]
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step, if_pos rfl]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step, if_neg (by omega)]
    rw [show -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) by omega]
    exact ih

/-- **Complete allocation ledger.** Starting with the copied guide and a unary
budget of `B`, exactly `14B+10` transitions produce the radius-`3B` guide and
position the unary and guide heads for the first macrostep. -/
private lemma setupCfg_allocation (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (n B : ℕ) (hn : n + 1 ≤ B) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .unaryStart) p b (B + 1) 0 bt (unaryTape B) (copyGuide (n + 1)))
      (14 * B + 10) =
      setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B)) := by
  have hc := setupCfg_start_center W a base p b 1 bt (unaryTape B) (3 * B) (3 * B + 1)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, neg_add_rev] at hc
  have hc' : (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .startCenter) p b 1 (-(3 * (B : ℤ)) - 1) bt (unaryTape B) (guideTape (3 * B)))
      (3 * B + 2) =
      setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B)) := by
    rw [show -(1 : ℤ) + -(3 * (B : ℤ)) = -(3 * (B : ℤ)) - 1 by omega] at hc
    exact hc
  rw [show 14 * B + 10 = (B + 2) + ((3 * B + 2) + ((3 * B + 1) +
      ((3 * B + 2) + ((B + 1) + (3 * B + 2))))) by omega,
    MultiTapeTM.runFrom_add, setupCfg_unary_start, MultiTapeTM.runFrom_add,
    setupCfg_layout_right W a base p b bt n B hn, MultiTapeTM.runFrom_add,
    setupCfg_layout_return, MultiTapeTM.runFrom_add, setupCfg_layout_left W a base p b bt B (by omega),
    MultiTapeTM.runFrom_add]
  have hr := setupCfg_unary_rewind W a base p b (-(3 * (B : ℤ)) - 1) bt (guideTape (3 * B)) B B true
  simp only [unaryRewindPhase, ite_true] at hr
  rw [hr, hc']

/-- The full input-copy schedule includes both virtual boundary cells and the
return to the origin. Its exact cost is `2n+4`; the native input then stays parked. -/
private lemma setupCfg_copy (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (b u : ℤ) (bt ut : ℤ → Option OblSymbol) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .copyLeft) ⟨1, by omega⟩ b u 0 bt ut (fun _ => none))
      (2 * x.length + 4) =
      setupCfg W a base (some .budgetStart) ⟨x.length + 1, by omega⟩ b u 0 bt ut (copyGuide (x.length + 1)) := by
  have hscan := congrArg (obliviousSchedule W a).tm.step
    (setupCfg_copy_prefix W a base b u bt ut x.length (le_refl _))
  rw [← MultiTapeTM.runFrom_succ_eq_step', setupCfg_copy_end] at hscan
  rw [show 2 * x.length + 4 = 2 + ((x.length + 1) + (x.length + 1)) by omega,
    MultiTapeTM.runFrom_add, setupCfg_copy_left, MultiTapeTM.runFrom_add,
    hscan, setupCfg_copy_return]

/-- The empty binary capture and empty unary budget share the initial sentinel. -/
private lemma clockTape_unary_zero : clockTape [] = unaryTape 0 := by
  funext z
  simp only [clockTape, FinTM.bufferTape_nil, Option.map_none, unaryTape, Int.natCast_zero]
  split_ifs <;> first | rfl | omega

/-- A halted captured clock configuration has the exact setup representation. -/
private lemma clockStageCfg_setup (W : FinTM Bool) (a : ℕ) {x : List Bool}
    (c : Cfg W.k Bool W.State x) (hs : c.state = none) :
    clockStageCfg W a c = setupCfg W a (clockStageCfg W a c) (some .resetStart)
      (clockStageCfg W a c).inputPos (c.output.length + 1) 1 0
      (clockTape c.output) (unaryTape 0) (fun _ => none) := by
  apply Cfg.ext
  · simp [clockStageCfg, setupCfg, hs]
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [clockStageCfg, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [clockStageCfg, setupCfg, clockTape_unary_zero]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [clockStageCfg, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [clockStageCfg, setupCfg]
  · rfl

/-- Changing only the macrostep phase and two heads preserves a completed
setup configuration's explicit tape representation. -/
private lemma macroCfg_setup (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q q' : Option (OblPhase W.State a)) (p : Fin (x.length + 2))
    (b u g u' g' : ℤ) (bt ut gt : ℤ → Option OblSymbol) :
    macroCfg W a (setupCfg W a base q p b u g bt ut gt) q' u' g' =
      setupCfg W a base q' p b u' g' bt ut gt := by
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [macroCfg, setupCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [macroCfg, setupCfg]
  · rfl

/-- The completely allocated setup executes precisely its unary budget and
then halts at the fixed final counter test. -/
private lemma setupCfg_finish (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (b : ℤ) (bt : ℤ → Option OblSymbol) (B : ℕ) :
    (obliviousSchedule W a).tm.runFrom
      (setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B)))
      (B * (6 * (3 * B) + 8) + 1) =
      setupCfg W a base none p b (B + 1) 0 bt (unaryTape B) (guideTape (3 * B)) := by
  have h := macroCfg_finish W a
    (setupCfg W a base (some .macroCheck) p b 1 0 bt (unaryTape B) (guideTape (3 * B))) (3 * B) B
    (by simp [setupCfg])
    (fun j hj => by simpa [setupCfg] using unaryTape_unit B j hj)
    (by simpa [setupCfg] using unaryTape_end B)
  simpa only [macroCfg_setup] using h

/-- Initialization connects the arbitrary clock endpoint to the completely
allocated macrostep configuration. The binary counter retains its full width. -/
private lemma setupCfg_initializes (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (p : Fin (x.length + 2)) (w : List Bool) (v : ℕ) (hv : budgetValue w = v)
    (hn : x.length + 1 ≤ (a + 1) * (v + 1)) :
    ∃ w', w'.length = w.length ∧
      (obliviousSchedule W a).tm.runFrom
        (setupCfg W a base (some .resetStart) p (w.length + 1) 1 0
          (clockTape w) (unaryTape 0) (fun _ => none))
        ((p.val - 1 + 2) + ((2 * x.length + 4) +
          ((v + 1) * (2 * w.length + (a + 1) + 4) + (14 * ((a + 1) * (v + 1)) + 10)))) =
        setupCfg W a base (some .macroCheck) ⟨x.length + 1, by omega⟩ (w.length + 1) 1 0
          (clockTape w') (unaryTape ((a + 1) * (v + 1))) (guideTape (3 * ((a + 1) * (v + 1)))) := by
  obtain ⟨w', hlen, hcounter⟩ := setupCfg_budget_all W a base ⟨x.length + 1, by omega⟩
    0 (copyGuide (x.length + 1)) v w 0 hv
  refine ⟨w', hlen, ?_⟩
  simp only [Nat.cast_zero, zero_add] at hcounter
  rw [MultiTapeTM.runFrom_add, setupCfg_reset, MultiTapeTM.runFrom_add, setupCfg_copy,
    MultiTapeTM.runFrom_add, hcounter]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    setupCfg_allocation W a base ⟨x.length + 1, by omega⟩ (w.length + 1) (clockTape w')
      x.length ((a + 1) * (v + 1)) hn

/-- Arithmetic bound for the schedule's operational ledger. The clock,
initialization, and macrostep run identities above supply its individual costs.
The data-output correctness proof is a separate invariant. -/
private lemma obliviousLedger_bound (a b u n τ width : ℕ)
    (hn : n ≤ u) (hτ : τ ≤ b * (u + 1)) (hw : width ≤ b * (u + 1)) :
    τ + 3 * n + 18 + (u + 1) * (2 * width + (a + 1) + 4) +
        22 * ((a + 1) * (u + 1)) + 18 * ((a + 1) * (u + 1)) ^ 2 ≤
      (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (u + 1) ^ 2 := by
  have hv : u + 1 ≤ (u + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hv1 : 1 ≤ (u + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  have ht : τ ≤ b * (u + 1) ^ 2 := hτ.trans (Nat.mul_le_mul_left _ hv)
  have hthree : 3 * n ≤ 3 * (u + 1) ^ 2 :=
    Nat.mul_le_mul_left _ ((hn.trans (Nat.le_succ _)).trans hv)
  have hconst : 18 ≤ 18 * (u + 1) ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 18 hv1
  have hcounter : (u + 1) * (2 * width + (a + 1) + 4) ≤
      2 * b * (u + 1) ^ 2 + ((a + 1) + 4) * (u + 1) ^ 2 := by
    calc
      _ ≤ (u + 1) * (2 * (b * (u + 1)) + (a + 1) + 4) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 2 * b * (u + 1) ^ 2 + ((a + 1) + 4) * (u + 1) := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hv) _
  have hsetup : 22 * ((a + 1) * (u + 1)) ≤ 22 * (a + 1) * (u + 1) ^ 2 := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hv
  have he : (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (u + 1) ^ 2 =
      b * (u + 1) ^ 2 + 3 * (u + 1) ^ 2 + 18 * (u + 1) ^ 2 +
      (2 * b * (u + 1) ^ 2 + ((a + 1) + 4) * (u + 1) ^ 2) +
      22 * (a + 1) * (u + 1) ^ 2 + 18 * ((a + 1) * (u + 1)) ^ 2 := by ring
  rw [he]
  omega

/-- The concrete schedule halts within a uniform quadratic bound. This theorem
includes clock capture, arbitrary input reset, copying, fixed-width budget
conversion, full guide allocation, all macrosteps, and the final counter test.
The decorated answer-bit invariant is proved separately below. -/
private lemma obliviousSchedule_halts (W : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ t ≤ (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (T x.length + 1) ^ 2,
      ((obliviousSchedule W a).tm.runFrom
        ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t).state = none := by
  obtain ⟨τ, hτ, c, hs, ho, hclock⟩ := clockStageCfg_captures W a b T hW x
  have hv : budgetValue c.output = T x.length := by rw [ho, budgetValue_bits]
  have hn : (x.map oblEmbed).length + 1 ≤ (a + 1) * (T x.length + 1) := by
    simp only [List.length_map]
    calc
      x.length + 1 ≤ T x.length + 1 := Nat.add_le_add_right (hT x.length) 1
      _ = 1 * (T x.length + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨w', hlen, hinit⟩ := setupCfg_initializes W a (clockStageCfg W a c)
    (clockStageCfg W a c).inputPos c.output (T x.length) hv hn
  rw [← clockStageCfg_setup W a c hs] at hinit
  let B := (a + 1) * (T x.length + 1)
  let initTime := ((clockStageCfg W a c).inputPos.val - 1 + 2) +
    ((2 * (x.map oblEmbed).length + 4) +
      ((T x.length + 1) * (2 * c.output.length + (a + 1) + 4) + (14 * B + 10)))
  let finishTime := B * (6 * (3 * B) + 8) + 1
  let t := (τ + 1) + (initTime + finishTime)
  refine ⟨t, ?_, ?_⟩
  · have hwidth : c.output.length ≤ b * (T x.length + 1) := by
      have hw := (FinTM.computesInTime_iff W _ _ _).mp (hW x)
      have hl := MultiTapeTM.output_length_le W.tm x (b * (T x.length + 1))
      rw [hw.2] at hl
      simpa only [ho] using hl
    have hp : (clockStageCfg W a c).inputPos.val - 1 ≤ x.length := by
      have hh := c.inputPos.isLt
      change c.inputPos.val - 1 ≤ x.length
      omega
    have ht : t = τ + ((clockStageCfg W a c).inputPos.val - 1) + 2 * x.length + 18 +
        (T x.length + 1) * (2 * c.output.length + (a + 1) + 4) + 22 * B + 18 * B ^ 2 := by
      dsimp only [t, initTime, finishTime]
      simp only [List.length_map]
      ring
    rw [ht]
    apply le_trans _ (obliviousLedger_bound a b (T x.length) x.length τ c.output.length
      (hT x.length) hτ hwidth)
    dsimp only [B]
    omega
  · change ((obliviousSchedule W a).tm.runFrom
        ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) ((τ + 1) + (initTime + finishTime))).state = none
    rw [MultiTapeTM.runFrom_add, hclock, MultiTapeTM.runFrom_add, hinit]
    have hf := setupCfg_finish W a (clockStageCfg W a c)
      ⟨(x.map oblEmbed).length + 1, by omega⟩ (c.output.length + 1) (clockTape w') B
    rw [hf]
    rfl

/-- The exact binary coding and schedule decoration preserve the schedule's
quadratic halting bound. Source-dependent data cannot stop or prolong this run. -/
private lemma obliviousCandidate_halts (W M : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ t ≤ (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (T x.length + 1) ^ 2,
      ((obliviousCandidate W M a).tm.runFrom ((obliviousCandidate W M a).tm.initCfg x) t).state = none := by
  classical
  obtain ⟨t, ht, hs⟩ := obliviousSchedule_halts W a b T hW hT x
  refine ⟨t, ht, ?_⟩
  unfold obliviousCandidate
  rw [parallelTM_run]
  have h := congrArg Cfg.state (decorateTM_run (obliviousSchedule W a) (M.k + 1)
    (Fin.natAdd W.k (2 : Fin 3)) (obliviousDataInit M) (obliviousVisit W M a)
    (obliviousSchedule_output W a) (x.map oblEmbed) t)
  rw [hs] at h
  change Option.map Prod.fst _ = none at h
  change _ = none
  exact Option.map_eq_none_iff.mp h

/-- Extend an arbitrary schedule configuration by aligned data tapes and
finite registers. The output is maintained separately from the silent schedule. -/
private def decoratedCfg {A S D : Type} {k l : ℕ} {x : List A} (head : Fin k)
    (c : Cfg k A S x) (d : D) (tapes : Fin l → ℤ → Option A) (out : List A) :
    Cfg (k + l) A (S × D) x :=
  ⟨c.state.map (fun q => (q, d)), c.inputPos, Fin.addCases c.workTapes tapes,
    Fin.addCases c.workTapePos (fun _ => c.workTapePos head), out⟩

/-- The extra data tapes begin blank and aligned with the schedule's origin. -/
private lemma decoratedCfg_init {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A) (x : List A) :
    (decorateTM P l head initial visit).tm.initCfg x =
      decoratedCfg head (P.tm.initCfg x) initial (fun _ _ => none) [] := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i z
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [decoratedCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [decoratedCfg]
  · rfl

/-- One decorated transition consists of exactly the prescribed schedule step
and the local data visit. This identity exposes data writes without changing
the already proved physical trajectory or timing. -/
private lemma decoratedCfg_step {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A)
    {x : List A} (c : Cfg P.k A P.State x) (q : P.State) (hs : c.state = some q)
    (d : D) (tapes : Fin l → ℤ → Option A) (out : List A) :
    let v := visit q d c.inputSymbol c.workTapeSymbols (fun i => tapes i (c.workTapePos head))
    (decorateTM P l head initial visit).tm.step (decoratedCfg head c d tapes out) =
      decoratedCfg head (P.tm.step c) v.1
        (fun i => setupWrite (tapes i) (c.workTapePos head) (v.2.1 i)) (out ++ v.2.2.toList) := by
  dsimp only
  have hstate : (decoratedCfg head c d tapes out).state = some (q, d) := by
    simp only [decoratedCfg, hs, Option.map_some]
  have hi : (decoratedCfg head c d tapes out).inputSymbol = c.inputSymbol := rfl
  have hl : (fun i => (decoratedCfg head c d tapes out).workTapeSymbols (i.castAdd l)) =
      c.workTapeSymbols := by
    funext i
    simp only [decoratedCfg, Cfg.workTapeSymbols, Fin.addCases_left]
  have hr : (fun i => (decoratedCfg head c d tapes out).workTapeSymbols (i.natAdd P.k)) =
      fun i => tapes i (c.workTapePos head) := by
    funext i
    simp only [decoratedCfg, Cfg.workTapeSymbols, Fin.addCases_right]
  unfold MultiTapeTM.step
  rw [hstate, hs]
  dsimp only [decorateTM]
  rw [hi, hl, hr]
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [decoratedCfg, Action.apply, Fin.addCases_left]
    · simp only [decoratedCfg, Action.apply, Fin.addCases_right, setupWrite]
      rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [decoratedCfg, Action.apply, Fin.addCases_left]
    · simp only [decoratedCfg, Action.apply, Fin.addCases_right]
  · rfl

/-- Logical simulator before the fixed-duration binary representation. -/
private noncomputable def dataTM (W M : FinTM Bool) (a : ℕ) : FinTM OblSymbol := by
  classical
  exact decorateTM (obliviousSchedule W a) (M.k + 1) (Fin.natAdd W.k (2 : Fin 3))
    (obliviousDataInit M) (obliviousVisit W M a)

/-- Macrostep configurations with explicit finite data registers and tapes. -/
private def dataCfg (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : OblPhase W.State a) (u g : ℤ) (d : OblData M)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) :=
  decoratedCfg (Fin.natAdd W.k (2 : Fin 3)) (macroCfg W a base (some q) u g) d tapes out

/-- One data step over a macrostep configuration, retaining the exact schedule
configuration produced by the independently verified controller. -/
private lemma dataCfg_step (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (q : OblPhase W.State a) (u g : ℤ) (d : OblData M)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) :
    let c := macroCfg W a base (some q) u g
    let v := obliviousVisit W M a q d c.inputSymbol c.workTapeSymbols (fun i => tapes i g)
    (dataTM W M a).tm.step (dataCfg W M a base q u g d tapes out) =
      decoratedCfg (Fin.natAdd W.k (2 : Fin 3)) ((obliviousSchedule W a).tm.step c) v.1
        (fun i => setupWrite (tapes i) g (v.2.1 i)) (out ++ v.2.2.toList) := by
  classical
  simpa only [macroCfg, Fin.addCases_right, Fin.reduceFinMk, ↓reduceIte] using
    decoratedCfg_step (obliviousSchedule W a) (M.k + 1) (Fin.natAdd W.k (2 : Fin 3))
      (obliviousDataInit M) (obliviousVisit W M a)
      (macroCfg W a base (some q) u g) q rfl d tapes out

/-- An interior forward visit preserves every current payload and caches the
incoming left-neighbor register. Its movement is the schedule's right move. -/
private lemma dataCfg_forward_step (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u g : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hn : g ≠ (R : ℤ) + 1) :
    (dataTM W M a).tm.step (dataCfg W M a base .forward u g (q,b,read,carry) tapes out) =
      dataCfg W M a base .forward u (g + 1)
        (q,b,read,fun i => (dataCell (tapes i g)).1)
        (fun i => Function.update (tapes i) g (some (.cell (dataCell (tapes i g)).1 (carry i)))) out := by
  rw [dataCfg_step, macroCfg_forward W a base u g R hg, if_neg hn]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_right, hn, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]

/-- The forward turn clears the neighbor register without altering data tapes. -/
private lemma dataCfg_forward_turn (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.step
      (dataCfg W M a base .forward u ((R : ℤ) + 1) (q,b,read,carry) tapes out) =
      dataCfg W M a base .backward u R (q,b,read,fun _ => blankPayload) tapes out := by
  rw [dataCfg_step, macroCfg_forward W a base u _ R hg, if_pos rfl]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_right, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rw [show (R : ℤ) + 1 - 1 = R by omega]

/-- An interior backward visit chooses the requested neighbor and carries the
old current payload to the next cell on the left. -/
private lemma dataCfg_backward_step (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u g : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hn : g ≠ -(R : ℤ) - 1) :
    (dataTM W M a).tm.step (dataCfg W M a base .backward u g (q,b,read,carry) tapes out) =
      dataCfg W M a base .backward u (g - 1)
        (q,b,read,fun i => (dataCell (tapes i g)).1)
        (fun i => Function.update (tapes i) g (some (.cell
          (match obliviousSourceMove M q read i with
            | .neg => (dataCell (tapes i g)).2
            | .zero => (dataCell (tapes i g)).1
            | .pos => carry i) blankPayload))) out := by
  rw [dataCfg_step, macroCfg_backward W a base u g R hg, if_neg hn]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left, hn, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]

/-- The left boundary turn preserves the completed data sweep. -/
private lemma dataCfg_backward_turn (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (d : OblData M)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.step
      (dataCfg W M a base .backward u (-(R : ℤ) - 1) d tapes out) =
      dataCfg W M a base .returnCenter u (-(R : ℤ)) d tapes out := by
  rw [dataCfg_step, macroCfg_backward W a base u _ R hg, if_pos rfl]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rw [show -(R : ℤ) - 1 + 1 = -(R : ℤ) by omega]

/-- Every prefix of the actual forward scan preserves all current payloads
and installs the correct left-neighbor cache at every visited coordinate.
**Proof sketch.** Induct on the physical scan length. The next current payload
is unchanged, and updating one cell extends the cached interval by one. -/
private lemma dataCfg_forward_prefix (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read : Fin (M.k + 1) → OblPayload) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = f z i) (n : ℕ) (hn : n ≤ 2 * R + 1) :
    ∃ tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .forward u (-(R : ℤ)) (q,b,read,f (-(R : ℤ) - 1)) tapes out) n =
        dataCfg W M a base .forward u (-(R : ℤ) + n)
          (q,b,read,f (-(R : ℤ) + n - 1)) tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 = f z i) ∧
      (∀ i z, -(R : ℤ) ≤ z → z < -(R : ℤ) + n → (dataCell (tapes' i z)).2 = f (z - 1) i) := by
  induction n with
  | zero =>
    refine ⟨tapes, ?_, hf, ?_⟩
    · simp only [Nat.cast_zero, add_zero, MultiTapeTM.runFrom_zero]
    · intro i z hl hr
      omega
  | succ n ih =>
    obtain ⟨ts, hrun, hfirst, hleft⟩ := ih (by omega)
    let g : ℤ := -(R : ℤ) + n
    let ts' := fun i => Function.update (ts i) g (some (.cell (f g i) (f (g - 1) i)))
    have hc : (fun i => (dataCell (ts i g)).1) = f g := funext (fun i => hfirst i g)
    refine ⟨ts', ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hrun,
        dataCfg_forward_step W M a base u _ R q b read _ ts out hg (by omega)]
      change dataCfg W M a base .forward u (g + 1)
        (q,b,read,fun i => (dataCell (ts i g)).1)
        (fun i => Function.update (ts i) g (some (.cell (dataCell (ts i g)).1 (f (g - 1) i)))) out = _
      simp only [hfirst, hc]
      have hp : -(R : ℤ) + (n + 1 : ℕ) = g + 1 := by omega
      rw [hp, show g + 1 - 1 = g by omega]
    · intro i z
      by_cases hz : z = g
      · subst z
        simp only [ts', Function.update_self, dataCell]
      · simp only [ts', Function.update_of_ne hz, hfirst]
    · intro i z hl hr
      by_cases hz : z = g
      · subst z
        simp only [ts', Function.update_self, dataCell]
      · simp only [ts', Function.update_of_ne hz]
        exact hleft i z hl (by dsimp only [g] at hz; omega)

/-- Every prefix of the actual backward scan shifts exactly the visited cells.
Unvisited current payloads and their cached left neighbors remain available.
**Proof sketch.** The carry is the old right neighbor. At the next cell the
three direction cases select the cached left, current, or carried right payload;
then the old current becomes the carry for the following cell. -/
private lemma dataCfg_backward_prefix (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read : Fin (M.k + 1) → OblPayload) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = f z i)
    (hl : ∀ i z, -(R : ℤ) ≤ z → z ≤ R → (dataCell (tapes i z)).2 = f (z - 1) i)
    (n : ℕ) (hn : n ≤ 2 * R + 1) :
    ∃ tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .backward u R (q,b,read,f ((R : ℤ) + 1)) tapes out) n =
        dataCfg W M a base .backward u ((R : ℤ) - n)
          (q,b,read,f ((R : ℤ) - n + 1)) tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 =
        if (R : ℤ) - n < z ∧ z ≤ R then f (z + (obliviousSourceMove M q read i : ℤ)) i else f z i) ∧
      (∀ i z, -(R : ℤ) ≤ z → z ≤ (R : ℤ) - n → (dataCell (tapes' i z)).2 = f (z - 1) i) := by
  induction n with
  | zero =>
    refine ⟨tapes, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero, sub_zero, MultiTapeTM.runFrom_zero]
    · intro i z
      simp only [Nat.cast_zero, sub_zero, show ¬((R : ℤ) < z ∧ z ≤ R) by omega, if_false, hf]
    · simpa only [Nat.cast_zero, sub_zero] using hl
  | succ n ih =>
    obtain ⟨ts, hrun, hfirst, hleft⟩ := ih (by omega)
    let g : ℤ := (R : ℤ) - n
    let ts' := fun i => Function.update (ts i) g
      (some (.cell (f (g + (obliviousSourceMove M q read i : ℤ)) i) blankPayload))
    have hc (i) : (dataCell (ts i g)).1 = f g i := by
      rw [hfirst, if_neg (by omega)]
    have hc' : (fun i => (dataCell (ts i g)).1) = f g := funext hc
    have hnbr (i) : (match obliviousSourceMove M q read i with
        | .neg => (dataCell (ts i g)).2
        | .zero => (dataCell (ts i g)).1
        | .pos => f (g + 1) i) = f (g + (obliviousSourceMove M q read i : ℤ)) i := by
      have hleft' := hleft i g (by omega) (le_refl _)
      cases hd : obliviousSourceMove M q read i <;>
        simp only [hd, SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]
    refine ⟨ts', ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hrun,
        dataCfg_backward_step W M a base u _ R q b read _ ts out hg (by omega)]
      change dataCfg W M a base .backward u (g - 1)
        (q,b,read,fun i => (dataCell (ts i g)).1)
        (fun i => Function.update (ts i) g (some (.cell
          (match obliviousSourceMove M q read i with
            | .neg => (dataCell (ts i g)).2
            | .zero => (dataCell (ts i g)).1
            | .pos => f (g + 1) i) blankPayload))) out = _
      simp only [hc', hnbr]
      have hp : (R : ℤ) - (n + 1 : ℕ) = g - 1 := by omega
      rw [hp, show g - 1 + 1 = g by omega]
    · intro i z
      by_cases hz : z = g
      · subst z
        simp only [ts', Function.update_self, dataCell]
        rw [if_pos (show (R : ℤ) - (n + 1 : ℕ) < g ∧ g ≤ R by dsimp only [g]; omega)]
      · simp only [ts', Function.update_of_ne hz, hfirst]
        have he : ((R : ℤ) - n < z ∧ z ≤ R) ↔ ((R : ℤ) - (n + 1 : ℕ) < z ∧ z ≤ R) := by
          dsimp only [g] at hz
          omega
        simp only [he]
    · intro i z hlow hhigh
      have hz : z ≠ g := by omega
      simp only [ts', Function.update_of_ne hz]
      exact hleft i z hlow (by omega)

/-- The outward positioning scan leaves all data and saved source reads intact.
**Proof sketch.** Induct through the read-only positioning prefix, then take the
left-boundary turn, which resets the already blank neighbor register. -/
private lemma dataCfg_seek_run (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool) (read : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.runFrom
      (dataCfg W M a base .seekLeft u 0 (q,b,read,fun _ => blankPayload) tapes out) (R + 2) =
      dataCfg W M a base .forward u (-(R : ℤ)) (q,b,read,fun _ => blankPayload) tapes out := by
  have hp : ∀ n, n ≤ R + 1 → (dataTM W M a).tm.runFrom
      (dataCfg W M a base .seekLeft u 0 (q,b,read,fun _ => blankPayload) tapes out) n =
      dataCfg W M a base .seekLeft u (-(n : ℤ)) (q,b,read,fun _ => blankPayload) tapes out := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero, neg_zero, MultiTapeTM.runFrom_zero]
    | succ n ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), dataCfg_step,
        macroCfg_seek W a base u _ R hg, if_neg (by omega)]
      simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left,
        show -(n : ℤ) ≠ -(R : ℤ) - 1 by omega, ↓reduceIte,
        setupWrite, Option.toList_none, List.append_nil, dataCfg]
      rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', hp _ (le_refl _), dataCfg_step,
    macroCfg_seek W a base u _ R hg, if_pos (by omega)]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_left,
    show -((R + 1 : ℕ) : ℤ) = -(R : ℤ) - 1 by omega, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]
  rw [show -(R : ℤ) - 1 + 1 = -(R : ℤ) by omega]

/-- Returning from the left boundary preserves the shifted tapes and commits
exactly the saved source transition at the marked origin.
**Proof sketch.** Every step before the origin preserves the registers and tapes;
at the origin the saved reads select the successor state and the counter advances. -/
private lemma dataCfg_center_run (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R) :
    (dataTM W M a).tm.runFrom
      (dataCfg W M a base .returnCenter u (-(R : ℤ)) (q,b,read,carry) tapes out) (R + 1) =
      dataCfg W M a base .macroCheck (u + 1) 0
        ((obliviousSourceAction M q read).state,b,read,carry) tapes out := by
  have hp : ∀ n, n ≤ R → (dataTM W M a).tm.runFrom
      (dataCfg W M a base .returnCenter u (-(R : ℤ)) (q,b,read,carry) tapes out) n =
      dataCfg W M a base .returnCenter u (-(R : ℤ) + n) (q,b,read,carry) tapes out := by
    intro n hn
    induction n with
    | zero => simp only [Nat.cast_zero, add_zero, MultiTapeTM.runFrom_zero]
    | succ n ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), dataCfg_step,
        macroCfg_center W a base u _ R hg, if_neg (by omega)]
      simp only [obliviousVisit, macroCfg_guide, hg, guideTape_origin,
        show -(R : ℤ) + n ≠ 0 by omega, ↓reduceIte,
        setupWrite, Option.toList_none, List.append_nil, dataCfg]
      rw [show -(R : ℤ) + n + 1 = -(R : ℤ) + (n + 1 : ℕ) by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', hp _ (le_refl _),
    show -(R : ℤ) + R = 0 by omega, dataCfg_step,
    macroCfg_center W a base u _ R hg, if_pos rfl]
  simp only [obliviousVisit, macroCfg_guide, hg, guideTape_origin, ↓reduceIte,
    setupWrite, Option.toList_none, List.append_nil, dataCfg]

/-- The initial counter test saves the source reads, performs its origin writes,
updates its answer register, and starts a full sweep without emitting output. -/
private lemma dataCfg_check (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (out : List OblSymbol)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit) :
    let read := fun i => (dataCell (tapes i 0)).1
    let act := obliviousSourceAction M d.1 read
    (dataTM W M a).tm.step (dataCfg W M a base .macroCheck u 0 d tapes out) =
      dataCfg W M a base .seekLeft u 0 (d.1,act.output.getD d.2.1,read,fun _ => blankPayload)
        (fun i => setupWrite (tapes i) 0
          (Fin.addCases (fun j => (act.workTapes j).1.map (fun p => some (.cell (p,0) blankPayload)))
            (fun _ : Fin 1 => none) i)) out := by
  dsimp only
  rw [dataCfg_step, macroCfg_check, if_pos hu]
  simp only [obliviousVisit, macroCfg_unary, hu, ↓reduceIte,
    Option.toList_none, List.append_nil, dataCfg]

/-- Decoding the origin writes gives exactly the source's written payloads,
including an explicit blank write and the identity action of a halted source.
**Proof sketch.** Separate work lanes from the read-only input lane. On a work
lane only coordinate zero can change; the optional-write cases give exactly the
source write or the old payload. Every other coordinate is unchanged. -/
private lemma dataCfg_written (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = sourcePayload c z i) :
    ∀ i z, (dataCell (setupWrite (tapes i) 0
      (Fin.addCases (fun j => ((sourceTotalAction M c).workTapes j).1.map
        (fun p => some (.cell (p,0) blankPayload))) (fun _ : Fin 1 => none) i) z)).1 =
      sourceWrittenPayload c (sourceTotalAction M c) z i := by
  intro i z
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left, sourceWrittenPayload]
    by_cases hz : z = 0
    · subst z
      have h := hf (j.castAdd 1) 0
      simp only [sourcePayload, Fin.addCases_left, add_zero] at h
      cases hw : ((sourceTotalAction M c).workTapes j).1 <;>
        simp only [setupWrite, Option.map_none, Option.map_some, Function.update_self,
          if_true, Option.getD_none, Option.getD_some]
      · exact h
      · rfl
    · have h := hf (j.castAdd 1) z
      simp only [sourcePayload, Fin.addCases_left] at h
      cases hw : ((sourceTotalAction M c).workTapes j).1 <;>
        simp [setupWrite, hw, Function.update_of_ne hz, h, hz]
  · simpa only [Fin.addCases_right, setupWrite, sourceWrittenPayload, sourcePayload] using hf (j.natAdd M.k) z

/-- The two actual data sweeps implement the prescribed neighbor selection on
the whole marked interval. Positioning scans and turns only maintain registers.
**Proof sketch.** Compose the four exact scan paths. The forward invariant
supplies every cached left neighbor to the backward invariant; blank boundary
registers are justified by the two endpoint hypotheses. -/
private lemma dataCfg_sweeps (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) (q : Option M.State) (b : Bool)
    (read : Fin (M.k + 1) → OblPayload) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = f z i)
    (hleft : f (-(R : ℤ) - 1) = fun _ => blankPayload)
    (hright : f ((R : ℤ) + 1) = fun _ => blankPayload) :
    ∃ tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .seekLeft u 0 (q,b,read,fun _ => blankPayload) tapes out) (6 * R + 7) =
        dataCfg W M a base .macroCheck (u + 1) 0
          ((obliviousSourceAction M q read).state,b,read,f (-(R : ℤ))) tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 =
        if -(R : ℤ) ≤ z ∧ z ≤ R then f (z + (obliviousSourceMove M q read i : ℤ)) i else f z i) := by
  obtain ⟨tf, hforward, hfirst, hcache⟩ :=
    dataCfg_forward_prefix W M a base u R q b read f tapes out hg hf (2 * R + 1) (le_refl _)
  have hfpos : -(R : ℤ) + (2 * R + 1 : ℕ) = (R : ℤ) + 1 := by omega
  rw [hfpos, hleft] at hforward
  have hcache' : ∀ i z, -(R : ℤ) ≤ z → z ≤ R → (dataCell (tf i z)).2 = f (z - 1) i := by
    intro i z hl hr
    exact hcache i z hl (by omega)
  obtain ⟨tb, hback, hshift, _⟩ :=
    dataCfg_backward_prefix W M a base u R q b read f tf out hg hfirst hcache'
      (2 * R + 1) (le_refl _)
  have hbpos : (R : ℤ) - (2 * R + 1 : ℕ) = -(R : ℤ) - 1 := by omega
  rw [hbpos, hright, show -(R : ℤ) - 1 + 1 = -(R : ℤ) by omega] at hback
  refine ⟨tb, ?_, ?_⟩
  · rw [show 6 * R + 7 = (R + 2) + ((2 * R + 1) + (((2 * R + 1) + ((R + 1) + 1)) + 1)) by omega,
      MultiTapeTM.runFrom_add, dataCfg_seek_run W M a base u R q b read tapes out hg,
      MultiTapeTM.runFrom_add, hforward, MultiTapeTM.runFrom_succ_eq_step,
      dataCfg_forward_turn W M a base u R q b read _ tf out hg,
      MultiTapeTM.runFrom_add, hback, MultiTapeTM.runFrom_succ_eq_step,
      dataCfg_backward_turn W M a base u R _ tb out hg,
      dataCfg_center_run W M a base u R q b read _ tb out hg]
  · intro i z
    rw [hshift]
    have he : ((R : ℤ) - (2 * R + 1 : ℕ) < z ∧ z ≤ R) ↔ (-(R : ℤ) ≤ z ∧ z ≤ R) := by omega
    simp only [he]

/-- An origin write cannot affect a different relative coordinate. -/
private lemma sourceWrittenPayload_away (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (z : ℤ) (hz : z ≠ 0) :
    sourceWrittenPayload c (sourceTotalAction M c) z = sourcePayload c z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [sourceWrittenPayload, sourcePayload, hz]

/-- One complete actual macrostep simulates one totalized source step. Its
output stream is unchanged, even when the source emits or has already halted.
**Proof sketch.** The origin update selects the source action from the represented
reads. The operational sweep theorem shifts its written payloads by the native
head displacements. Both old and new source support are inside the marked zone,
so the unchanged exterior is also correct. The return scan commits the successor
state, and the finite answer register remembers the source's last output. -/
private lemma dataCfg_simulates (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x)
    (u : ℤ) (R : ℕ) {word : List Bool} (c : Cfg M.k Bool M.State word)
    (read carry : Fin (M.k + 1) → OblPayload)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (hg : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape R)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u = some .unit)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = sourcePayload c z i)
    (hs : ∀ z, z < -(R : ℤ) ∨ (R : ℤ) < z → sourcePayload c z = fun _ => blankPayload)
    (hs' : ∀ z, z < -(R : ℤ) ∨ (R : ℤ) < z → sourcePayload (M.tm.step c) z = fun _ => blankPayload) :
    ∃ read' carry' tapes',
      (dataTM W M a).tm.runFrom
        (dataCfg W M a base .macroCheck u 0 (c.state,c.output.getLast?.getD false,read,carry) tapes out)
        (6 * R + 8) =
        dataCfg W M a base .macroCheck (u + 1) 0
          ((M.tm.step c).state,(M.tm.step c).output.getLast?.getD false,read',carry') tapes' out ∧
      (∀ i z, (dataCell (tapes' i z)).1 = sourcePayload (M.tm.step c) z i) := by
  let act := sourceTotalAction M c
  let f := sourceWrittenPayload c act
  let written := fun i => setupWrite (tapes i) 0
    (Fin.addCases (fun j => (act.workTapes j).1.map (fun p => some (.cell (p,0) blankPayload)))
      (fun _ : Fin 1 => none) i)
  have hread : (fun i => (dataCell (tapes i 0)).1) = sourcePayload c 0 := funext (fun i => hf i 0)
  have hboundary (z : ℤ) (hz : z < -(R : ℤ) ∨ (R : ℤ) < z) : f z = fun _ => blankPayload := by
    dsimp only [f, act]
    rw [sourceWrittenPayload_away M c z (by omega)]
    exact hs z hz
  obtain ⟨ts, hrun, hts⟩ := dataCfg_sweeps W M a base u R c.state
    (act.output.getD (c.output.getLast?.getD false)) (sourcePayload c 0) f written out hg
    (dataCfg_written M c tapes hf)
    (hboundary _ (by omega)) (hboundary _ (by omega))
  have hstate : act.state = (M.tm.step c).state :=
    congrArg Cfg.state (sourceTotalAction_apply M c)
  have hanswer : act.output.getD (c.output.getLast?.getD false) =
      (M.tm.step c).output.getLast?.getD false := by
    rw [← sourceTotalAction_apply M c]
    exact (lastOutput_append c.output act.output).symm
  refine ⟨sourcePayload c 0, f (-(R : ℤ)), ts, ?_, ?_⟩
  · rw [show 6 * R + 8 = (6 * R + 7) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, dataCfg_check W M a base u _ tapes out hu]
    dsimp only
    rw [hread, obliviousSourceAction_correct]
    change (dataTM W M a).tm.runFrom
      (dataCfg W M a base .seekLeft u 0
        (c.state,act.output.getD (c.output.getLast?.getD false),sourcePayload c 0,fun _ => blankPayload)
        written out) (6 * R + 7) = _
    rw [hrun, obliviousSourceAction_correct, hstate, hanswer]
  · intro i z
    rw [hts, obliviousSourceMove_correct]
    by_cases hz : -(R : ℤ) ≤ z ∧ z ≤ R
    · rw [if_pos hz]
      dsimp only [f, act]
      rw [← sourcePayload_apply c (sourceTotalAction M c) z i, sourceTotalAction_apply M c]
    · rw [if_neg hz]
      have ho : z < -(R : ℤ) ∨ (R : ℤ) < z := by omega
      rw [hboundary z ho, hs' z ho]

/-- Payloads after copying the left input boundary and `j` following cells. -/
private def copiedPayload (M : FinTM Bool) (x : List Bool) (j : ℕ) (z : ℤ) :
    Fin (M.k + 1) → OblPayload :=
  Fin.addCases (fun _ => blankPayload) (fun _ =>
    if z = -1 ∨ (0 ≤ z ∧ z < j) then inputPayload x z else blankPayload)

/-- The copied input, including both blank boundary tags, represents the initial
source configuration exactly; every source work tape is still blank. -/
private lemma copiedPayload_full (M : FinTM Bool) (x : List Bool) :
    copiedPayload M x (x.length + 1) = sourcePayload (M.tm.initCfg x) := by
  funext z i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [copiedPayload, sourcePayload, blankPayload]
  · simp only [copiedPayload, sourcePayload, Fin.addCases_right, MultiTapeTM.initCfg,
      Cfg.init, Fin.val_one, Int.natCast_one, sub_self, zero_add]
    split_ifs with h
    · rfl
    · exact (inputPayload_outside x z (by omega)).symm

/-- The input-lane write used by every copy transition. -/
private def copyDataWrite (M : FinTM Bool) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (z : ℤ) (p : OblPayload) : Fin (M.k + 1) → ℤ → Option OblSymbol :=
  fun i => setupWrite (tapes i) z
    (Fin.addCases (fun _ => none) (fun _ : Fin 1 => some (some (.cell p blankPayload))) i)

/-- Copying the left boundary creates precisely the zero-length copy prefix. -/
private lemma copyDataWrite_left (M : FinTM Bool) (x : List Bool)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = blankPayload) :
    ∀ i z, (dataCell (copyDataWrite M tapes (-1) (none,1) i z)).1 = copiedPayload M x 0 z i := by
  intro i z
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [copyDataWrite, copiedPayload, Fin.addCases_left, setupWrite, hf]
  · simp only [copyDataWrite, copiedPayload, Fin.addCases_right, setupWrite]
    by_cases hz : z = -1
    · subst z
      simp [Function.update_self, dataCell, inputPayload, FinTM.bufferTape]
    · rw [Function.update_of_ne hz, hf]
      rw [if_neg (by omega)]

/-- A copy transition extends the represented prefix by exactly one cell. -/
private lemma copyDataWrite_next (M : FinTM Bool) (x : List Bool) (j : ℕ)
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = copiedPayload M x j z i) :
    ∀ i z, (dataCell (copyDataWrite M tapes j (inputPayload x j) i z)).1 =
      copiedPayload M x (j + 1) z i := by
  intro i z
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simpa only [copyDataWrite, copiedPayload, Fin.addCases_left, setupWrite] using hf (k.castAdd 1) z
  · simp only [copyDataWrite, copiedPayload, Fin.addCases_right, setupWrite]
    by_cases hz : z = (j : ℤ)
    · subst z
      simp only [Function.update_self, dataCell, if_pos (show (j : ℤ) = -1 ∨ (0 ≤ (j : ℤ) ∧ (j : ℤ) < (j + 1 : ℕ)) by omega)]
    · rw [Function.update_of_ne hz, hf]
      simp only [copiedPayload, Fin.addCases_right]
      have he : (z = -1 ∨ 0 ≤ z ∧ z < (j : ℤ)) ↔ (z = -1 ∨ 0 ≤ z ∧ z < (j + 1 : ℕ)) := by omega
      simp only [he]

/-- Data assertions used during initialization: the finite registers and output
remain initial, while the first payloads have the supplied tape interpretation. -/
private def initialContent (M : FinTM Bool) (f : ℤ → Fin (M.k + 1) → OblPayload)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) : Prop :=
  d = obliviousDataInit M ∧ out = [] ∧ ∀ i z, (dataCell (tapes i z)).1 = f z i

/-- The initialization invariant retains full data information until the first
macrostep. Later macrosteps have a strictly larger unary-head position, so they
cannot re-enter the first-macrostep clause. The unary origin is unique. -/
private def prepCondition {S : Type} {a : ℕ} (M : FinTM Bool) (x : List Bool)
    (phase : Option (OblPhase S a)) (p : ℕ) (u g : ℤ) (ut : ℤ → Option OblSymbol)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) : Prop :=
  let sentinel := ∀ z, ut z = some .origin ↔ z = 0
  let blank := initialContent M (fun _ _ => blankPayload) d tapes out
  let full := initialContent M (copiedPayload M x (x.length + 1)) d tapes out
  match phase with
  | none => True
  | some .init => u = 0 ∧ g = 0 ∧ (∀ z, ut z = none) ∧ blank
  | some (.clock _) | some .resetStart => sentinel ∧ u = 1 ∧ g = 0 ∧ blank
  | some .resetScan => sentinel ∧ u = 1 ∧ g = 0 ∧ p ≤ x.length ∧ blank
  | some .copyLeft => sentinel ∧ u = 1 ∧ g = 0 ∧ p = 1 ∧ blank
  | some .copyLeftWrite => sentinel ∧ u = 1 ∧ g = -1 ∧ p = 1 ∧ blank
  | some .copyFirst | some .copyMore => sentinel ∧ u = 1 ∧
      ∃ j, j ≤ x.length ∧ p = j + 1 ∧ g = j ∧ initialContent M (copiedPayload M x j) d tapes out
  | some .copyReturn | some .budgetStart | some .budgetBack | some (.append _) | some (.borrow _) =>
      sentinel ∧ 1 ≤ u ∧ full
  | some .startCenter => sentinel ∧ u = 1 ∧ full
  | some .macroCheck => sentinel ∧ 1 ≤ u ∧ (u = 1 → full)
  | some .seekLeft | some .forward | some .backward | some .returnCenter => sentinel ∧ 1 ≤ u
  | _ => sentinel ∧ full

/-- Configuration form of the initialization invariant. -/
private def prepInvariant (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) : Prop :=
  prepCondition M x c.state c.inputPos.val
    (c.workTapePos (Fin.natAdd W.k (1 : Fin 3))) (c.workTapePos (Fin.natAdd W.k (2 : Fin 3)))
    (c.workTapes (Fin.natAdd W.k (1 : Fin 3))) d tapes out

/-- The input reads blank exactly at one of the two native boundaries. -/
private lemma inputSymbol_blank {A S : Type} {k : ℕ} {x : List A} (c : Cfg k A S x) :
    c.inputSymbol = none ↔ c.inputPos.val = 0 ∨ c.inputPos.val = x.length + 1 := by
  unfold Cfg.inputSymbol
  simp only [Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

/-- At the copy position, an embedded native input read gives the next bit or
its right blank boundary. This includes an empty input. -/
private lemma copy_input_read {S : Type} {k : ℕ} (x : List Bool)
    (c : Cfg k OblSymbol S (x.map oblEmbed)) (j : ℕ) (hj : j ≤ x.length)
    (hp : c.inputPos.val = j + 1) :
    c.inputSymbol = (x[j]?).map OblSymbol.bit := by
  by_cases h : j < x.length
  · rw [inputSymbolInner j (by omega) (by simpa only [List.length_map] using h)]
    simp only [List.getElem_map, oblEmbed, Function.Embedding.coeFn_mk, List.getElem?_eq_getElem h,
      Option.map_some]
  · have he : j = x.length := by omega
    have hb := (inputSymbol_blank c).mpr (Or.inr (by simp only [List.length_map]; omega))
    rw [hb, List.getElem?_eq_none (by omega), Option.map_none]

/-- Copying an embedded read writes the exact virtual input payload. -/
private lemma copy_input_payload {S : Type} {k : ℕ} (x : List Bool)
    (c : Cfg k OblSymbol S (x.map oblEmbed)) (j : ℕ) (hj : j ≤ x.length)
    (hp : c.inputPos.val = j + 1) :
    (clockBit c.inputSymbol, if c.inputSymbol.isNone then 2 else 0) = inputPayload x j := by
  rw [copy_input_read x c j hj hp]
  by_cases h : j < x.length
  · rw [List.getElem?_eq_getElem h]
    simp [clockBit, inputPayload, FinTM.bufferTape, show (j : ℤ) ≠ -1 by omega, show j ≠ x.length by omega]
  · have he : j = x.length := by omega
    subst j
    simp [clockBit, inputPayload, FinTM.bufferTape, show (x.length : ℤ) ≠ -1 by omega]

/-- Evaluating the preparation invariant after a non-clock schedule action
exposes only its input move, unary tape update, and two distinguished heads. -/
private lemma prepInvariant_action (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
    (q : Option (OblPhase W.State a)) (inp : SignType)
    (b u g : Option (Option OblSymbol) × SignType)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol) :
    prepInvariant W M a x ((oblAction q inp b u g).apply c) d tapes out =
      prepCondition M x q (moveInputPos c.inputPos inp).val
        (c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) + u.2)
        (c.workTapePos (Fin.natAdd W.k (2 : Fin 3)) + g.2)
        (setupWrite (c.workTapes (Fin.natAdd W.k (1 : Fin 3)))
          (c.workTapePos (Fin.natAdd W.k (1 : Fin 3))) u.1) d tapes out := by
  cases hu : u.1 <;> simp [prepInvariant, oblAction, setupWrite, hu]

/-- The unique unary origin survives writing a unit at a positive coordinate. -/
private lemma unaryOrigin_update (ut : ℤ → Option OblSymbol) (u : ℤ) (hu : 1 ≤ u)
    (h : ∀ z, ut z = some .origin ↔ z = 0) :
    ∀ z, Function.update ut u (some .unit) z = some .origin ↔ z = 0 := by
  intro z
  by_cases hz : z = u
  · subst z
    simp [show u ≠ 0 by omega]
  · rw [Function.update_of_ne hz, h]

/-- Preparation is invariant under every decorated transition. Once simulation
has begun, the unary head only increases, so the first macrostep still carries
the completely copied input when initialization's schedule theorem reaches it.
**Proof sketch.** Clock and reset phases preserve blank data. Copy phases extend
the represented input prefix; allocation preserves that complete copy. The
unique unary origin forces entry at counter position one. Each later return to
the macrostep controller increments that position. -/
private lemma prepInvariant_step (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
    (q : OblPhase W.State a) (hs : c.state = some q)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol) (out : List OblSymbol)
    (h : prepInvariant W M a x c d tapes out) :
    let v := obliviousVisit W M a q d c.inputSymbol c.workTapeSymbols
      (fun i => tapes i (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))))
    prepInvariant W M a x ((obliviousSchedule W a).tm.step c) v.1
      (fun i => setupWrite (tapes i) (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))) (v.2.1 i))
      (out ++ v.2.2.toList) := by
  dsimp only
  simp only [MultiTapeTM.step, hs]
  simp only [prepInvariant, hs] at h
  cases q with
  | init =>
    rcases h with ⟨hu, hg, hut, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    simp only [prepCondition, setupWrite, hu, hg, SignType.cast, zero_add, add_zero]
    refine ⟨?_, trivial, trivial, hd⟩
    intro z
    change (Function.update (c.workTapes (Fin.natAdd W.k (1 : Fin 3)))
      (c.workTapePos (Fin.natAdd W.k (1 : Fin 3))) (some .origin) z = some .origin) ↔ z = 0
    rw [hu]
    by_cases hz : z = 0
    · subst z
      exact ⟨fun _ => rfl, fun _ => Function.update_self _ _ _⟩
    · rw [Function.update_of_ne hz, hut]
      simp [hz]
  | clock s =>
    rcases h with ⟨hut, hu, hg, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one, Nat.one_ne_zero, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
      SignType.coe_zero, add_zero]
    cases hn : (W.tm.tr s (c.inputSymbol.map (fun _ => false))
      (fun i => clockBit (c.workTapeSymbols (i.castAdd 3)))).state <;>
      simpa [hn, prepCondition] using
        (show (∀ z, c.workTapes (Fin.natAdd W.k (1 : Fin 3)) z = some .origin ↔ z = 0) ∧
          c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) = 1 ∧
          c.workTapePos (Fin.natAdd W.k (2 : Fin 3)) = 0 ∧
          initialContent M (fun _ _ => blankPayload) d tapes out from ⟨hut,hu,hg,hd⟩)
  | resetStart =>
    rcases h with ⟨hut, hu, hg, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    simp only [prepCondition, setupWrite, SignType.coe_zero, add_zero, FinTM.moveInputPos_neg_val]
    refine ⟨hut, hu, hg, ?_, hd⟩
    have hp := c.inputPos.isLt
    simp only [List.length_map] at hp
    omega
  | resetScan =>
    rcases h with ⟨hut, hu, hg, hp, hd⟩
    cases hi : c.inputSymbol with
    | none =>
      have hp0 : c.inputPos.val = 0 := by
        have hb := (inputSymbol_blank c).mp hi
        simp only [List.length_map] at hb
        omega
      have hmove : (moveInputPos c.inputPos .pos).val = 1 := by
        rw [moveInputPos_pos_of_ne_right _ (by simp only [List.length_map]; omega)]
        change c.inputPos.val + 1 = 1
        omega
      simp only [obliviousSchedule, obliviousVisit, hi, setupWrite, Option.toList_none, List.append_nil]
      rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, by simpa using hg, hmove, hd⟩
    | some bit =>
      simp only [obliviousSchedule, obliviousVisit, hi, setupWrite, Option.toList_none, List.append_nil]
      rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, by simpa using hg,
        by simpa only [FinTM.moveInputPos_neg_val] using (Nat.sub_le c.inputPos.val 1).trans hp, hd⟩
  | copyLeft =>
    rcases h with ⟨hut, hu, hg, hp, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    exact ⟨hut, by simpa using hu, by simpa [hg, SignType.cast], by simpa using hp, hd⟩
  | copyLeftWrite =>
    rcases h with ⟨hut, hu, hg, hp, hd, ho, ht⟩
    simp only [obliviousSchedule, obliviousVisit, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    refine ⟨hut, by simpa using hu, 0, Nat.zero_le _, by simpa using hp, ?_, hd, ho, ?_⟩
    · simpa [hg, SignType.cast]
    · simpa only [hg, copyDataWrite] using copyDataWrite_left M x tapes ht
  | copyFirst | copyMore =>
    all_goals
      rcases h with ⟨hut, hu, j, hj, hp, hg, hd, ho, ht⟩
      have hpay := copy_input_payload x c j hj hp
      have hwrite := copyDataWrite_next M x j tapes ht
      by_cases hjn : j = x.length
      · have hi : c.inputSymbol = none := by
          rw [copy_input_read x c j hj hp, List.getElem?_eq_none (by omega), Option.map_none]
        simp only [obliviousSchedule, obliviousVisit, hi, Option.isNone_none, ↓reduceIte,
          Option.toList_none, List.append_nil]
        rw [prepInvariant_action]
        refine ⟨hut, by simpa [hu], hd, ho, ?_⟩
        rw [hi] at hpay
        simp only [Option.isNone_none, ite_true] at hpay
        rw [← hpay] at hwrite
        simpa only [hg, hjn, copyDataWrite] using hwrite
      · have hjlt : j < x.length := by omega
        have hi : c.inputSymbol = some (.bit (x[j]'hjlt)) := by
          rw [copy_input_read x c j hj hp, List.getElem?_eq_getElem hjlt, Option.map_some]
        have hmove : (moveInputPos c.inputPos .pos).val = j + 1 + 1 := by
          rw [moveInputPos_pos_of_ne_right _ (by simp only [List.length_map]; omega)]
          change c.inputPos.val + 1 = j + 1 + 1
          omega
        simp only [obliviousSchedule, obliviousVisit, hi, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
          Option.toList_none, List.append_nil]
        rw [prepInvariant_action]
        refine ⟨hut, by simpa using hu, j + 1, by omega, hmove, ?_, hd, ho, ?_⟩
        · simp [hg, SignType.cast]
        · rw [hi] at hpay
          simp only [Option.isNone_some, Bool.false_eq_true, ite_false] at hpay
          rw [← hpay] at hwrite
          simpa only [hg, copyDataWrite] using hwrite
  | copyReturn =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split <;> rw [prepInvariant_action] <;> exact ⟨hut, by simpa using hu, hd⟩
  | budgetStart =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    exact ⟨hut, by simpa using hu, hd⟩
  | budgetBack =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split <;> rw [prepInvariant_action] <;> exact ⟨hut, by simpa using hu, hd⟩
  | append i =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split
    · rw [prepInvariant_action]
      exact ⟨unaryOrigin_update _ _ hu hut, by simpa [SignType.cast] using (by omega : 1 ≤ c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) + 1), hd⟩
    · rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, hd⟩
  | borrow carry =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split
    · rw [prepInvariant_action]
      exact ⟨hut, by simpa using hu, hd⟩
    · split <;> rw [prepInvariant_action]
      · exact ⟨hut, hd⟩
      · exact ⟨hut, by simpa using hu, hd⟩
  | unaryStart =>
    rcases h with ⟨hut, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    rw [prepInvariant_action]
    exact ⟨hut, hd⟩
  | unaryBack | layoutRight i | layoutReturn i | layoutLeft i =>
    all_goals
      rcases h with ⟨hut, hd⟩
      simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
      split <;> rw [prepInvariant_action] <;> exact ⟨hut, hd⟩
  | rightEdge | leftEdge =>
    all_goals
      rcases h with ⟨hut, hd⟩
      simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
      rw [prepInvariant_action]
      exact ⟨hut, hd⟩
  | unaryReset =>
    rcases h with ⟨hut, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split
    · rename_i he
      rw [prepInvariant_action]
      refine ⟨hut, ?_, hd⟩
      have hu := (hut _).mp he
      simp [hu, SignType.cast]
    · rw [prepInvariant_action]
      exact ⟨hut, hd⟩
  | startCenter =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit, setupWrite, Option.toList_none, List.append_nil]
    split <;> rw [prepInvariant_action]
    · exact ⟨hut, by simp [hu], fun _ => hd⟩
    · exact ⟨hut, by simpa using hu, hd⟩
  | macroCheck =>
    rcases h with ⟨hut, hu, hd⟩
    simp only [obliviousSchedule, obliviousVisit]
    split <;> rw [prepInvariant_action]
    · exact ⟨hut, by simpa using hu⟩
    · trivial
  | seekLeft | forward | backward =>
    all_goals
      rcases h with ⟨hut, hu⟩
      simp only [obliviousSchedule, obliviousVisit]
      split <;> rw [prepInvariant_action] <;> exact ⟨hut, by simpa using hu⟩
  | returnCenter =>
    rcases h with ⟨hut, hu⟩
    simp only [obliviousSchedule, obliviousVisit]
    split <;> rw [prepInvariant_action]
    · refine ⟨hut, by simpa [SignType.cast] using (by omega : 1 ≤ c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) + 1), ?_⟩
      intro he
      simp only [SignType.cast] at he
      omega
    · exact ⟨hut, by simpa using hu⟩

/-- The preparation invariant holds at every actual logical time. This also
retains an exact decomposition into schedule, data registers, tapes, and output.
**Proof sketch.** The initial configuration has blank data. Each live transition
uses the local invariant and the exact decorated-step identity. A halted
configuration is fixed, so the same representation remains valid thereafter. -/
private lemma prepInvariant_run (W M : FinTM Bool) (a : ℕ) (x : List Bool) (t : ℕ) :
    ∃ d tapes out,
      (dataTM W M a).tm.runFrom ((dataTM W M a).tm.initCfg (x.map oblEmbed)) t =
        decoratedCfg (Fin.natAdd W.k (2 : Fin 3))
          ((obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t)
          d tapes out ∧
      prepInvariant W M a x
        ((obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t)
        d tapes out := by
  classical
  induction t with
  | zero =>
    refine ⟨obliviousDataInit M, fun _ _ => none, [], ?_, ?_⟩
    · exact decoratedCfg_init _ _ _ _ _ _
    · simp [prepInvariant, prepCondition, obliviousSchedule, initialContent, dataCell]
  | succ t ih =>
    obtain ⟨d, tapes, out, hrun, hinv⟩ := ih
    let c := (obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t
    change prepInvariant W M a x c d tapes out at hinv
    cases hs : c.state with
    | none =>
      refine ⟨d, tapes, out, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.runFrom_succ_eq_step']
        change (dataTM W M a).tm.step (decoratedCfg _ c d tapes out) =
          decoratedCfg _ ((obliviousSchedule W a).tm.step c) d tapes out
        rw [MultiTapeTM.step_of_halt (show (decoratedCfg _ c d tapes out).state = none by simp [decoratedCfg, hs]),
          MultiTapeTM.step_of_halt hs]
      · rw [MultiTapeTM.runFrom_succ_eq_step']
        change prepInvariant W M a x ((obliviousSchedule W a).tm.step c) d tapes out
        rw [MultiTapeTM.step_of_halt hs]
        exact hinv
    | some q =>
      let v := obliviousVisit W M a q d c.inputSymbol c.workTapeSymbols
        (fun i => tapes i (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))))
      refine ⟨v.1, fun i => setupWrite (tapes i) (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))) (v.2.1 i),
        out ++ v.2.2.toList, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.runFrom_succ_eq_step']
        exact decoratedCfg_step (obliviousSchedule W a) _ _ _ _ c q hs d tapes out
      · rw [MultiTapeTM.runFrom_succ_eq_step']
        exact prepInvariant_step W M a x c q hs d tapes out hinv

/-- Restating a configuration using its current macrostep heads changes nothing. -/
private lemma macroCfg_self (W : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (c : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) :
    macroCfg W a c c.state (c.workTapePos (Fin.natAdd W.k (1 : Fin 3)))
      (c.workTapePos (Fin.natAdd W.k (2 : Fin 3))) = c := by
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [macroCfg]
    · rcases finThree_cases j with rfl | rfl | rfl <;> simp [macroCfg]
  · rfl

/-- The initialized schedule reaches a fully allocated first macrostep. This
extracts the endpoint of clock capture and the exact initialization ledger.
**Proof sketch.** The captured bits have value `T(n)`. The input-length bound
justifies allocation, and composition of the clock and initialization run identities
gives the required unary tape, guide, state, and initial macrostep head positions. -/
private lemma obliviousSchedule_ready (W : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ t,
      let c := (obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t
      c.state = some .macroCheck ∧
      c.workTapePos (Fin.natAdd W.k (1 : Fin 3)) = 1 ∧
      c.workTapePos (Fin.natAdd W.k (2 : Fin 3)) = 0 ∧
      c.workTapes (Fin.natAdd W.k (1 : Fin 3)) = unaryTape ((a + 1) * (T x.length + 1)) ∧
      c.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape (3 * ((a + 1) * (T x.length + 1))) := by
  obtain ⟨τ, _, c, hs, ho, hclock⟩ := clockStageCfg_captures W a b T hW x
  have hv : budgetValue c.output = T x.length := by rw [ho, budgetValue_bits]
  have hn : (x.map oblEmbed).length + 1 ≤ (a + 1) * (T x.length + 1) := by
    simp only [List.length_map]
    exact (Nat.add_le_add_right (hT x.length) 1).trans (by
      simpa only [one_mul] using Nat.mul_le_mul_right (T x.length + 1) (show 1 ≤ a + 1 by omega))
  obtain ⟨w', _, hinit⟩ := setupCfg_initializes W a (clockStageCfg W a c)
    (clockStageCfg W a c).inputPos c.output (T x.length) hv hn
  rw [← clockStageCfg_setup W a c hs] at hinit
  refine ⟨(τ + 1) + (((clockStageCfg W a c).inputPos.val - 1 + 2) +
    ((2 * (x.map oblEmbed).length + 4) + ((T x.length + 1) * (2 * c.output.length + (a + 1) + 4) +
      (14 * ((a + 1) * (T x.length + 1)) + 10)))), ?_⟩
  dsimp only
  rw [MultiTapeTM.runFrom_add, hclock, hinit]
  simp [setupCfg]

/-- The actual logical machine reaches the first macrostep with the initial
source configuration represented on its data tapes and with no output yet.
**Proof sketch.** Apply the invariant at the time supplied by the schedule endpoint.
The unary head is at one, so the first-macrostep clause yields the original source
state and complete input copy. Re-express the same schedule configuration in the
macrostep representation. -/
private lemma dataTM_ready (W M : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ (t : ℕ) (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed))
      (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol),
      base.workTapes (Fin.natAdd W.k (1 : Fin 3)) = unaryTape ((a + 1) * (T x.length + 1)) ∧
      base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape (3 * ((a + 1) * (T x.length + 1))) ∧
      (dataTM W M a).tm.runFrom ((dataTM W M a).tm.initCfg (x.map oblEmbed)) t =
        dataCfg W M a base .macroCheck 1 0 (obliviousDataInit M) tapes [] ∧
      (∀ i z, (dataCell (tapes i z)).1 = sourcePayload (M.tm.initCfg x) z i) := by
  obtain ⟨t, hs, hu, hg, hut, hgt⟩ := obliviousSchedule_ready W a b T hW hT x
  obtain ⟨d, tapes, out, hrun, hinv⟩ := prepInvariant_run W M a x t
  let base := (obliviousSchedule W a).tm.runFrom ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t
  change prepInvariant W M a x base d tapes out at hinv
  change base.state = some .macroCheck at hs
  change base.workTapePos (Fin.natAdd W.k (1 : Fin 3)) = 1 at hu
  change base.workTapePos (Fin.natAdd W.k (2 : Fin 3)) = 0 at hg
  simp only [prepInvariant, hs, hu, prepCondition] at hinv
  obtain ⟨hd, ho, ht⟩ := hinv.2.2 trivial
  subst d
  subst out
  refine ⟨t, base, tapes, hut, hgt, ?_, ?_⟩
  · rw [hrun]
    have hm := macroCfg_self W a base
    rw [hs, hu, hg] at hm
    simp only [dataCfg, hm]
    rfl
  · simpa only [copiedPayload_full] using ht

/-- The padded sequence of actual macrosteps represents the source run at every
macrostep boundary, while emitting no output. Early source halting is handled
by the same totalized one-step simulation at every remaining budget cell.
**Proof sketch.** Induct on the macrostep index. The unary tape supplies a live
budget cell, source bounds justify both old and new support, and the operational
macrostep theorem advances exactly one source step at the fixed cost. -/
private lemma dataCfg_iterates (W M : FinTM Bool) (a : ℕ) (x : List Bool)
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) (x.map oblEmbed)) (B : ℕ)
    (hn : x.length + 1 ≤ B)
    (hut : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) = unaryTape B)
    (hgt : base.workTapes (Fin.natAdd W.k (2 : Fin 3)) = guideTape (3 * B))
    (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hf : ∀ i z, (dataCell (tapes i z)).1 = sourcePayload (M.tm.initCfg x) z i)
    (j : ℕ) (hj : j ≤ B) :
    ∃ read carry tapes',
      (dataTM W M a).tm.runFrom (dataCfg W M a base .macroCheck 1 0 (obliviousDataInit M) tapes [])
        (j * (6 * (3 * B) + 8)) =
        dataCfg W M a base .macroCheck ((j : ℤ) + 1) 0
          ((M.tm.runFrom (M.tm.initCfg x) j).state,
            (M.tm.runFrom (M.tm.initCfg x) j).output.getLast?.getD false,read,carry) tapes' [] ∧
      (∀ i z, (dataCell (tapes' i z)).1 = sourcePayload (M.tm.runFrom (M.tm.initCfg x) j) z i) := by
  induction j with
  | zero =>
    refine ⟨fun _ => blankPayload, fun _ => blankPayload, tapes, ?_, hf⟩
    simp [obliviousDataInit]
  | succ j ih =>
    obtain ⟨read, carry, ts, hrun, hrep⟩ := ih (by omega)
    have hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((j : ℤ) + 1) = some .unit := by
      rw [hut]
      exact unaryTape_unit B j (by omega)
    have hs (t : ℕ) (ht : t ≤ B) (z : ℤ) (hz : z < -((3 * B : ℕ) : ℤ) ∨ ((3 * B : ℕ) : ℤ) < z) :
        sourcePayload (M.tm.runFrom (M.tm.initCfg x) t) z = fun _ => blankPayload := by
      funext i
      exact sourcePayload_support M x t B ht hn z (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hz) i
    obtain ⟨read', carry', ts', hstep, hrep'⟩ := dataCfg_simulates W M a base ((j : ℤ) + 1)
      (3 * B) (M.tm.runFrom (M.tm.initCfg x) j) read carry ts [] hgt hu hrep
      (hs j (by omega)) (by simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hs (j + 1) hj)
    refine ⟨read', carry', ts', ?_, ?_⟩
    · rw [Nat.succ_mul, MultiTapeTM.runFrom_add, hrun, hstep, MultiTapeTM.runFrom_succ_eq_step']
      rw [show ((j + 1 : ℕ) : ℤ) + 1 = (j : ℤ) + 1 + 1 by omega]
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hrep'

/-- A failed final counter test emits exactly the saved answer and halts in one
transition; it does not inspect the represented source's acceptance state. -/
private lemma dataCfg_finish (W M : FinTM Bool) (a : ℕ) {x : List OblSymbol}
    (base : Cfg (W.k + 3) OblSymbol (OblPhase W.State a) x) (u : ℤ)
    (d : OblData M) (tapes : Fin (M.k + 1) → ℤ → Option OblSymbol)
    (hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) u ≠ some .unit) :
    ((dataTM W M a).tm.step (dataCfg W M a base .macroCheck u 0 d tapes [])).state = none ∧
    ((dataTM W M a).tm.step (dataCfg W M a base .macroCheck u 0 d tapes [])).output = [.bit d.2.1] := by
  rw [dataCfg_step, macroCfg_check, if_neg hu]
  simp only [obliviousVisit, macroCfg_unary, if_neg hu]
  simp only [decoratedCfg, macroCfg, Option.map_none, Option.toList_some, List.nil_append, and_self]

/-- The logical simulator eventually produces precisely the decision bit.
Its separately proved schedule ledger will supply the quadratic time bound.
**Proof sketch.** Compose initialization with all `B` operational macrosteps and
the final counter test. The padded source run has already halted with its decision
bit, so the last-output register makes the sole emitted bit correct. -/
private lemma dataTM_computes (W M : FinTM Bool) (L : Language Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (hM : M.DecidesInTime L (fun n => a * T n)) (x : List Bool) :
    ∃ t, (dataTM W M a).ComputesInTime (x.map oblEmbed)
      [OblSymbol.bit (MultiTapeTM.indicator (L : Set (List Bool)) x)] t := by
  obtain ⟨t, base, tapes, hut, hgt, hready, hrep⟩ := dataTM_ready W M a b T hW hT x
  let B := (a + 1) * (T x.length + 1)
  have hn : x.length + 1 ≤ B := by
    apply (Nat.add_le_add_right (hT x.length) 1).trans
    simpa only [one_mul] using Nat.mul_le_mul_right (T x.length + 1) (show 1 ≤ a + 1 by omega)
  obtain ⟨read, carry, ts, hrun, _⟩ := dataCfg_iterates W M a x base B hn hut hgt tapes hrep B (le_refl _)
  have hu : base.workTapes (Fin.natAdd W.k (1 : Fin 3)) ((B : ℤ) + 1) ≠ some .unit := by
    rw [hut, unaryTape_end]
    exact Option.noConfusion
  have hfinish := dataCfg_finish W M a base ((B : ℤ) + 1)
    ((M.tm.runFrom (M.tm.initCfg x) B).state,
      (M.tm.runFrom (M.tm.initCfg x) B).output.getLast?.getD false,read,carry) ts hu
  refine ⟨(t + B * (6 * (3 * B) + 8)) + 1, ?_⟩
  rw [FinTM.computesInTime_iff, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hready, hrun]
  exact ⟨hfinish.1, hfinish.2.trans (congrArg (fun bit => [OblSymbol.bit bit])
    (sourceAnswer_at_budget M L T a hM x))⟩

/-- Correctness and the independent quadratic halting certificate refer to the
same deterministic binary simulator, so they give the decision bit at the
quadratic deadline. No unproved simulation theorem enters this argument. -/
private lemma obliviousCandidate_decides (W M : FinTM Bool) (L : Language Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (hM : M.DecidesInTime L (fun n => a * T n)) :
    (obliviousCandidate W M a).DecidesInTime L
      (fun n => (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (T n + 1) ^ 2) := by
  classical
  intro x
  obtain ⟨t, ht⟩ := dataTM_computes W M L a b T hW hT hM x
  have hcorrect : (obliviousCandidate W M a).ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] t :=
    parallelTM_computes (dataTM W M a) oblEmbed x [_] t ht
  obtain ⟨s, hs, hhalt⟩ := obliviousCandidate_halts W M a b T hW hT x
  have hbounded : (obliviousCandidate W M a).ComputesInTime x
      ((obliviousCandidate W M a).tm.runFrom ((obliviousCandidate W M a).tm.initCfg x) s).output s :=
    (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩
  rw [hbounded.output_unique hcorrect] at hbounded
  exact hbounded.mono hs

/-- **Oblivious simulation** — the first assertion of [AB09, Exercise 1.5], adapted
to this model: for time-constructible `T`, every language in `DTIME T` is decided by
an *oblivious* machine within `c · (T n + 1)²`. (The exercise's additional two-tape
normal form is not part of this statement.)

**Proof sketch** (corrected per the phase-2 audit, finding 2: the construction must
not invoke `one_work_tape_binary` per simulated step — that composes quadratics into
a quartic — must not run the constructibility witness verbatim, which need not be
oblivious, and must park the real input head). Take a decider for `L` within
`a · T n` and a constructibility witness within `b · (T n + 1)`.

1. Run the witness with every non-blank input symbol *read as `false`* (substituted
   in its transition table): its entire run — trajectories, emissions, halting time —
   then coincides with its run on the all-`false` input of length `n`, hence depends
   only on `n`, and it still computes `⌞T n⌟`; store the budget on a work tape.
2. Copy the real input to a work tape in one fixed scan and rewind (cost
   `O(n + 1)`, absorbed since `n ≤ T n`), then park the real input head for good.
3. Set `B n = (a + 1) · (T n + 1)` macrosteps and prepare a marked layout of size
   `O(B n)` holding the decider's work tapes, the virtual input copy, virtual head
   markers, and a step counter.
4. Each macrostep simulates one step of the decider by a fixed number of full sweeps
   of the layout — tape data affects writes, simulated state, and markers, never the
   sweep path or its duration — idling identically once the simulated machine halts,
   for exactly `B n` macrosteps (counter maintenance within the per-macrostep linear
   allowance; fixed-duration binary block coding throughout, so no appeal to the
   existential `alphabet_reduction` is needed to stay binary and oblivious).
5. Emit the stored answer bit at a fixed final time and halt.

Every head trajectory and the halting time are then functions of `n` and `t` alone,
and the total cost is `O(b · (T n + 1) + (B n)²) = O((T n + 1)²)`.

**Implementation notes — Epoch 3, Batch C.** The private construction above
provides the concrete binary simulator and its complete computation, trajectory,
and quadratic-time certificates. Logical alphabet codes are transverse fixed-width
binary blocks on synchronized tracks, so each logical transition costs one physical
transition. Virtual tapes are represented relative to their heads at the marked
origin; the two data sweeps implement virtual movement by shifting payloads. These
choices use the statement's unrestricted finite work-tape count.

The preparation invariant preserves the copied input through initialization. Its
first-macrostep clause is protected by the unique unary origin and the strictly
increasing macrostep counter. The operational forward and backward scan invariants
prove the source simulation, including blank writes, clamped input moves, and idle
steps after source halting. Exactly the prescribed budget is simulated, followed
by one answer emission. Determinism connects this complete output certificate to
the independent quadratic halting ledger, with constant
`18(a+1)^2 + 23(a+1) + 3b + 25`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  classical
  rcases hT with ⟨hlinear, b, _, W, hW⟩
  rcases hL with ⟨a, M, hM⟩
  exact ⟨obliviousCandidate W M a, 18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25,
    obliviousCandidate_oblivious W M a, obliviousCandidate_decides W M L a b T hW hlinear hM⟩

end Complexity
