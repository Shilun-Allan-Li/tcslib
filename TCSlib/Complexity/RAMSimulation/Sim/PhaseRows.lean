/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseInvariant
import TCSlib.Complexity.TuringMachine.Build.InputBit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Word rows on the simulation's tape bank

The five-tape word rows use the simulation's two operand registers and result register, or its
key register and input-length tape, while tapes six and seven provide their blank scratch.
The finite machines are independent of the word width and input.

## Main definitions

* `WordRAM.Sim.PhaseFrame.write`: write one word while preserving the other frame fields.

## Main results

* `WordRAM.Sim.phase_wordRow`: place a native word-writing contract on eight tapes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The frame after overwriting a word register, with its input head, work heads and output
unchanged. -/
def PhaseFrame.write {x : List Bool} (r : Fin 8) (w : List Bool) (F : PhaseFrame x) :
    PhaseFrame x :=
  { F with workTapes := wordWrite (F.cfg ()) r w }

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.write

/-- A register write changes just the frame's tapes by `wordWrite` at unit control. -/
theorem PhaseFrame.write_eq {x : List Bool} (r : Fin 8) (w : List Bool) (F : PhaseFrame x) :
    F.write r w = { F with workTapes := wordWrite (F.cfg ()) r w } := rfl

/-- A native five-tape contract gives a finite frame row whenever its embedded endpoint is
the prescribed result frame and its work heads are restored. -/
theorem phase_nativeRow {I : List Bool → Type}
    (P : ∀ {x : List Bool}, I x → PhaseFrame x → Prop)
    (f : ∀ {x : List Bool}, I x → PhaseFrame x → PhaseFrame x)
    (B E : ∀ {x : List Bool}, I x → ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (M : MultiTapeTM 5 Bool S) (entry exit : S)
    (σ : Fin 5 ↪ Fin 8) (post : ∀ {x : List Bool}, I x → PhaseFrame x → Turing.Cfg 5 Bool S x)
    (h : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      ReachesWithin M ((F.cfg entry).select σ) {some exit} (B i) (E i) (post i F))
    (he : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      embedEmitCfg σ F.workTapes F.workTapePos F.output (post i F) = (f i F).cfg exit)
    (hh : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      (f i F).workTapePos = F.workTapePos) : Nonempty (PhaseRow I P f B E) := by
  refine ⟨⟨S, inferInstance, inferInstance, embedEmitTM σ M, entry, exit, hh, ?_⟩⟩
  intro x i F hp
  have hr := phase_reaches_embed σ M (F.cfg entry) {some exit} (B i) (E i) _ (h i F hp)
  have he' := he i F hp
  simpa only [PhaseFrame.cfg_eq, he'] using hr

/-- Placing a native five-tape word-writing row gives a finite row over frames on eight tapes.
The source precondition may be any predicate that supplies the native contract.

**Proof sketch.** Apply `phase_reaches_embed` to the selected native contract and
`phase_embed_wordWrite` to its endpoint. `phase_wordWrite_as_update` identifies that endpoint
with `PhaseFrame.write` independently of the installed control state. -/
theorem phase_wordRow {I : List Bool → Type}
    (P : ∀ {x : List Bool}, I x → PhaseFrame x → Prop)
    (v : ∀ {x : List Bool}, I x → List Bool) (B E : ∀ {x : List Bool}, I x → ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (M : MultiTapeTM 5 Bool S) (entry exit : S)
    (σ : Fin 5 ↪ Fin 8) (r : Fin 5)
    (h : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      ReachesWithin M ((F.cfg entry).select σ) {some exit} (B i) (E i)
        { ((F.cfg entry).select σ) with
          state := some exit
          workTapes := wordWrite ((F.cfg entry).select σ) r (v i) }) :
    Nonempty (PhaseRow I P (fun i F => F.write (σ r) (v i)) B E) := by
  apply phase_nativeRow (I := I) P _ B E S M entry exit σ _ h
  · intro x i F hp
    simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq, Cfg.select_eq,
      phase_wordWrite_as_update] using
      phase_embed_wordWrite σ (F.cfg entry) (some exit) F.inputPos r (v i)
  · intro x i F hp
    rfl

/-- A delimited word of the specified width is available at a register. -/
def PhaseReady {x : List Bool} (W : ℕ) (r : Fin 8) (F : PhaseFrame x) : Prop :=
  ∃ w, WordAt (F.cfg ()) r w ∧ w.length = W

/-- Register readiness means that a word of the specified width is delimited at its head. -/
theorem phaseReady_iff {x : List Bool} (W : ℕ) (r : Fin 8) (F : PhaseFrame x) :
    PhaseReady W r F ↔ ∃ w, WordAt (F.cfg ()) r w ∧ w.length = W := Iff.rfl

/-- The two dedicated scratch tapes of a frame are blank everywhere. -/
def PhaseScratch {x : List Bool} (F : PhaseFrame x) : Prop :=
  ∀ r : Fin 8, 6 ≤ r.val → ∀ z : ℤ, F.workTapes r z = none

/-- Scratch blankness is pointwise blankness of tapes six and seven. -/
theorem phaseScratch_iff {x : List Bool} (F : PhaseFrame x) :
    PhaseScratch F ↔ ∀ r : Fin 8, 6 ≤ r.val → ∀ z : ℤ, F.workTapes r z = none := Iff.rfl

/-- The operand/result bank: source tapes two and three, result tape four, scratch six and seven. -/
def phaseArithBank : Fin 5 ↪ Fin 8 :=
  ⟨![2, 3, 4, 6, 7], by decide⟩

/-- The arithmetic bank sends its five indices to `2, 3, 4, 6, 7`, respectively. -/
theorem phaseArithBank_apply (r : Fin 5) : phaseArithBank r = ![2, 3, 4, 6, 7] r := rfl

/-- Installing a different control state does not change a frame's word layouts. -/
theorem phase_wordAt_frame {S : Type} {x : List Bool} (F : PhaseFrame x) (q : S)
    (r : Fin 8) (w : List Bool) : WordAt (F.cfg q) r w ↔ WordAt (F.cfg ()) r w := by
  apply phase_wordAt_congr
  · simp only [PhaseFrame.cfg_eq]
  · simp only [PhaseFrame.cfg_eq]

/-- A bank whose last two source tapes lie on the dedicated scratch tapes satisfies the native
blank-scratch precondition of the word rows. -/
theorem phase_scratch_select {S : Type} {x : List Bool} (σ : Fin 5 ↪ Fin 8)
    (F : PhaseFrame x) (q : S) (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val)
    (hF : PhaseScratch F) : ScratchBlank ((F.cfg q).select σ) := by
  apply (scratchBlank_iff _).mpr
  intro r hr z
  simpa only [Cfg.select_eq, PhaseFrame.cfg_eq] using
    (phaseScratch_iff F).mp hF (σ r) (hσ r hr) z

/-- An integer-constant writer on a selected register is a finite frame row, uniform in the
width supplied by its index and linear in that width.

**Proof sketch.** Choose `exists_wordIntTM` once for the constant and extension amount. Read
register readiness, transport its word to the selection, and supply the native blank scratch
with `phase_scratch_select`. `phase_wordRow` places the contract without changing its bounds. -/
theorem phase_intRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (c : ℤ) (a : ℕ) (σ : Fin 5 ↪ Fin 8)
    (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => PhaseReady (width i + a) (σ 2) F ∧ PhaseScratch F)
      (fun i F => F.write (σ 2) (bvBits (BitVec.ofInt (width i + a) c)))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_wordIntTM c a
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := I) _ _ _ _ S M entry exit σ 2
  intro x i F hp
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff (width i + a) (σ 2) F).mp hp.1
  apply hM (W := width i) w ((F.cfg entry).select σ)
  · simp only [Cfg.select_eq, PhaseFrame.cfg_eq]
  · exact (phase_wordAt_select σ (F.cfg entry) 2 w).mpr
      ((phase_wordAt_frame F entry (σ 2) w).mpr hw)
  · exact hwidth
  · exact phase_scratch_select σ F entry hσ hp.2

/-- The three binary arithmetic instructions use the same two-source register interface. -/
inductive PhaseArith where
  | add
  | sub
  | mul

/-- The word result of a binary arithmetic instruction. -/
def PhaseArith.value {W : ℕ} (op : PhaseArith) (u v : BitVec W) : BitVec W :=
  match op with
  | .add => u + v
  | .sub => u - v
  | .mul => u * v

/-- Binary arithmetic returns the sum, difference or product selected by its instruction. -/
theorem PhaseArith.value_eq {W : ℕ} (op : PhaseArith) (u v : BitVec W) :
    op.value u v = match op with
      | .add => u + v
      | .sub => u - v
      | .mul => u * v := rfl

/-- The native time allowance is quadratic for multiplication and linear for addition/subtraction. -/
def PhaseArith.steps (op : PhaseArith) (W : ℕ) : ℕ :=
  match op with
  | .mul => (W + 1) ^ 2
  | _ => W + 1

/-- The binary arithmetic time allowance is `(W+1)^2` for multiplication and `W+1` otherwise. -/
theorem PhaseArith.steps_eq (op : PhaseArith) (W : ℕ) :
    op.steps W = match op with
      | .mul => (W + 1) ^ 2
      | _ => W + 1 := rfl

/-- Each binary arithmetic instruction has the common native five-tape contract, with its
own uniform constant and the appropriate linear or quadratic time allowance. -/
theorem PhaseArith.native (op : PhaseArith) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 5 Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Turing.Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) →
        WordAt d 2 w → w.length = W → ScratchBlank d →
        ReachesWithin M d {some exit} (C * op.steps W) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (op.value u v)) } := by
  cases op with
  | add => exact exists_wordAddTM
  | sub => exact exists_wordSubTM
  | mul => exact exists_wordMulTM

/-- Binary arithmetic reads registers two and three and writes register four, uniformly in
the indexed word width. Addition/subtraction take linear time; multiplication takes quadratic
time; the radius is always linear.

**Proof sketch.** Choose the shared contract `PhaseArith.native` and place it with
`phase_wordRow` on `phaseArithBank`. Word preconditions are transported by
`phase_wordAt_select` and `phase_wordAt_frame`; `phase_scratch_select` supplies blank scratch. -/
theorem phase_arithRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u v : ∀ {x : List Bool} (i : I x), BitVec (width i)) (op : PhaseArith) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
        WordAt (F.cfg ()) 3 (bvBits (v i)) ∧ PhaseReady (width i) 4 F ∧ PhaseScratch F)
      (fun i F => F.write 4 (bvBits (op.value (u i) (v i))))
      (fun i => C * op.steps (width i)) (fun i => C * (width i + 1))) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := op.native
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := I) _ _ _ _ S M entry exit phaseArithBank 2
  intro x i F hp
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff (width i) 4 F).mp hp.2.2.1
  apply hM (u i) (v i) w ((F.cfg entry).select phaseArithBank)
  · simp only [Cfg.select_eq, PhaseFrame.cfg_eq]
  · exact (phase_wordAt_select phaseArithBank (F.cfg entry) 0 _).mpr
      ((phase_wordAt_frame F entry 2 _).mpr hp.1)
  · exact (phase_wordAt_select phaseArithBank (F.cfg entry) 1 _).mpr
      ((phase_wordAt_frame F entry 3 _).mpr hp.2.1)
  · exact (phase_wordAt_select phaseArithBank (F.cfg entry) 2 w).mpr
      ((phase_wordAt_frame F entry 4 w).mpr hw)
  · exact hwidth
  · exact phase_scratch_select phaseArithBank F entry (by decide) hp.2.2.2

/-- The key-writing bank reads register two and writes register one, using scratch six/seven. -/
def phaseKeyBank : Fin 5 ↪ Fin 8 :=
  ⟨![2, 3, 1, 6, 7], by decide⟩

/-- The key bank sends its five indices to `2, 3, 1, 6, 7`, respectively. -/
theorem phaseKeyBank_apply (r : Fin 5) : phaseKeyBank r = ![2, 3, 1, 6, 7] r := rfl

/-- A native one-source word row with a fixed width extension lifts to the selected source and
destination registers of a frame, with unchanged linear time and radius allowances.

**Proof sketch.** Choose the supplied native contract, read destination readiness, transport the
source and destination words, and obtain blank scratch with `phase_scratch_select`.
`phase_wordRow` then supplies the finite eight-tape machine. This adapter is shared by arithmetic
halving and sign extension. -/
theorem phase_unaryRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) (a : ℕ)
    (f : ∀ W : ℕ, BitVec W → BitVec (W + a)) (σ : Fin 5 ↪ Fin 8)
    (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val)
    (hnative : ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 5 Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (v : BitVec W) (w : List Bool) (d : Turing.Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits v) → WordAt d 2 w → w.length = W + a →
        ScratchBlank d → ReachesWithin M d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (f W v)) }) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) (σ 0) (bvBits (u i)) ∧
        PhaseReady (width i + a) (σ 2) F ∧ PhaseScratch F)
      (fun i F => F.write (σ 2) (bvBits (f (width i) (u i))))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := hnative
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := I) _ _ _ _ S M entry exit σ 2
  intro x i F hp
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff (width i + a) (σ 2) F).mp hp.2.1
  apply hM (u i) w ((F.cfg entry).select σ)
  · simp only [Cfg.select_eq, PhaseFrame.cfg_eq]
  · exact (phase_wordAt_select σ (F.cfg entry) 0 _).mpr
      ((phase_wordAt_frame F entry (σ 0) _).mpr hp.1)
  · exact (phase_wordAt_select σ (F.cfg entry) 2 w).mpr
      ((phase_wordAt_frame F entry (σ 2) w).mpr hw)
  · exact hwidth
  · exact phase_scratch_select σ F entry hσ hp.2.2

/-- Arithmetic halving reads register two and writes register four, preserving the other frame
fields within linear time and radius. -/
theorem phase_halfRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
        PhaseReady (width i) 4 F ∧ PhaseScratch F)
      (fun i F => F.write 4 (bvBits ((u i).sshiftRight 1)))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  simpa only [phaseArithBank_apply, Nat.add_zero] using
    phase_unaryRow width u 0 (fun _ v => v.sshiftRight 1) phaseArithBank (by decide)
      exists_wordHalfTM

/-- Sign extension reads register two and writes the extended address word to key register one,
within linear time and radius with a constant depending on the extension amount. -/
theorem phase_signExtendRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) (a : ℕ) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
        PhaseReady (width i + a) 1 F ∧ PhaseScratch F)
      (fun i F => F.write 1 (bvBits ((u i).signExtend (width i + a))))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  simpa only [phaseKeyBank_apply] using
    phase_unaryRow width u a (fun W v => v.signExtend (W + a)) phaseKeyBank (by decide)
      (exists_wordSignExtendTM a)

end WordRAM.Sim
