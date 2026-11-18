/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Certified instruction blocks

The component rows use different native allowances and exact frame transformations. A block
retains their finite control and bounded run, with a precondition and postcondition on frames
and a single uniform phase constant. Blocks compose through the existing seam contract.

## Main definitions

* `WordRAM.Sim.PhaseBlock`: a finite deterministic block with a uniform phase allowance.
* `WordRAM.Sim.PhaseState`: the RAM encoding together with known register words.

## Main results

* `WordRAM.Sim.PhaseBlock.seq`: sequence blocks while adding their constants and one dispatch.
* `WordRAM.Sim.phase_state_write`: retain the encoding and known words after a register write.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A finite deterministic block takes a frame satisfying its precondition to a frame satisfying
its postcondition, restores all work heads and obeys a uniform instruction-phase allowance. -/
structure PhaseBlock
    (P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : MultiTapeTM 8 Bool State
  entry : State
  exit : State
  constant : ℕ
  run : ∀ (x : List Bool) (i : PhaseData) (F : PhaseFrame x), P x i F →
    ∃ G : PhaseFrame x, Q x i G ∧ G.workTapePos = F.workTapePos ∧
      ReachesWithin machine (F.cfg entry) {some exit}
        (constant * phaseTime i x) (constant * phaseSpace i x) (G.cfg exit)

/-- A row whose precondition follows from `P`, whose result satisfies `Q`, and whose allowances
fit the common phase units gives a block with the same finite machine. -/
theorem PhaseBlock.ofRow
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {pre : ∀ {x : List Bool}, PhaseData → PhaseFrame x → Prop}
    {f : ∀ {x : List Bool}, PhaseData → PhaseFrame x → PhaseFrame x}
    {B E : ∀ {x : List Bool}, PhaseData → ℕ}
    (R : PhaseRow (fun _ => PhaseData) @pre @f @B @E) (C : ℕ)
    (hP : ∀ x i F, P x i F → pre i F)
    (hQ : ∀ x i F, P x i F → Q x i (f i F))
    (hB : ∀ x i, B (x := x) i ≤ C * phaseTime i x)
    (hE : ∀ x i, E (x := x) i ≤ C * phaseSpace i x) : Nonempty (PhaseBlock P Q) := by
  refine ⟨⟨R.State, R.finite, R.decEq, R.machine, R.entry, R.exit, C, ?_⟩⟩
  intro x i F hp
  exact ⟨f i F, hQ x i F hp, R.heads i F (hP x i F hp),
    (R.run i F (hP x i F hp)).mono (hB x i) (hE x i)⟩

/-- Changing a block's precondition to a stronger one and its postcondition to a weaker one
retains its machine and allowance. -/
theorem PhaseBlock.weaken
    {P Q P' Q' : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    (R : PhaseBlock P Q) (hP : ∀ x i F, P' x i F → P x i F)
    (hQ : ∀ x i F, Q x i F → Q' x i F) : Nonempty (PhaseBlock P' Q') := by
  refine ⟨⟨R.State, R.finite, R.decEq, R.machine, R.entry, R.exit, R.constant, ?_⟩⟩
  intro x i F hp
  obtain ⟨G, hq, hh, hr⟩ := R.run x i F (hP x i F hp)
  exact ⟨G, hQ x i G hq, hh, hr⟩

/-- Two blocks compose through their seam. Their constants add, with one further unit for the
dispatch step.

**Proof sketch.** Run the first block and use its postcondition as the second block's
precondition. `phase_reaches_seq` composes the bounded runs through `Contract.seq`; the restored
intermediate heads give a common center. The phase units are positive, so their sum plus the
one dispatch step is bounded by the sum of constants plus one. -/
theorem PhaseBlock.seq
    {P Q R : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    (A : PhaseBlock P Q) (B : PhaseBlock Q R) : Nonempty (PhaseBlock P R) := by
  classical
  letI := A.finite
  letI := A.decEq
  letI := B.finite
  letI := B.decEq
  refine ⟨⟨A.State ⊕ B.State, inferInstance, inferInstance,
    seamCompTM A.machine A.exit B.machine B.entry, Sum.inl A.entry, Sum.inr B.exit,
    A.constant + B.constant + 1, ?_⟩⟩
  intro x i F hp
  obtain ⟨G, hq, hhG, hrA⟩ := A.run x i F hp
  obtain ⟨H, hr, hhH, hrB⟩ := B.run x i G hq
  refine ⟨H, hr, hhH.trans hhG, ?_⟩
  have hrun := phase_reaches_seq A.machine B.machine A.entry A.exit B.entry B.exit
    {some B.exit} F G H _ _ _ _ hrA hrB (Set.mem_singleton_iff.mpr rfl) hhG
  have ht : A.constant * phaseTime i x + 1 + B.constant * phaseTime i x ≤
      (A.constant + B.constant + 1) * phaseTime i x := by
    have hu := (phase_units i x).1
    nlinarith
  have he : A.constant * phaseSpace i x + B.constant * phaseSpace i x ≤
      (A.constant + B.constant + 1) * phaseSpace i x := by nlinarith
  simpa only [Set.image_singleton, Option.map_some] using hrun.mono ht he

/-- The encoding together with the specified known words in any registers. A `none` register
specification imposes no additional word condition. -/
def PhaseState (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) : Prop :=
  Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
    ∀ r w, regs x i r = some w → WordAt (F.cfg ()) r w

/-- A register state consists of its RAM encoding and each specified exact register word. -/
theorem phaseState_iff (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) :
    PhaseState a fn regs x i F ↔
      Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
        ∀ r w, regs x i r = some w → WordAt (F.cfg ()) r w := Iff.rfl

/-- Overwriting a correctly sized register preserves the encoding and every known word on
other registers, and records the new exact word at its destination.

**Proof sketch.** Use `phase_frame_write_encodes` for the encoding. At the written register,
`phase_frame_write_word` uses the readiness supplied by the encoding; elsewhere,
`phase_frame_write_other` preserves the prior word. `Function.update` describes these two cases. -/
theorem phase_state_write (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) (hp : PhaseState a fn regs x i F)
    (r : Fin 8) (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) (w : List Bool)
    (hw : w.length = if r = 1 then i.width + a else i.width) :
    PhaseState a fn (fun y j => Function.update (regs y j) r (some w)) x i (F.write r w) := by
  obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
  apply (phaseState_iff a fn _ x i (F.write r w)).mpr
  refine ⟨phase_frame_write_encodes fn i.cells i.cfg i.origins F he r hr₀ hr₁ w hw, ?_⟩
  intro j v hj
  by_cases h : j = r
  · subst j
    simp only [Function.update_self, Option.some.injEq] at hj
    subst v
    exact phase_frame_write_word F r _ w (phase_frame_ready fn i.cells i.cfg i.origins F he
      r hr₀ hr₁) hw
  · exact phase_frame_write_other F r j w v h (hregs j v
      (by simpa only [Function.update_of_ne h] using hj))

/-- Moving only the input head preserves the RAM encoding and all known register words. -/
theorem phase_state_inputPos (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) (hp : PhaseState a fn regs x i F)
    (ip : Fin (x.length + 2)) : PhaseState a fn regs x i { F with inputPos := ip } := by
  obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
  apply (phaseState_iff a fn regs x i _).mpr
  refine ⟨?_, ?_⟩
  · exact (phase_encodes_congr fn i.cells i.cfg i.cfg (Function.Embedding.refl _) i.origins
      (F.cfg ()) (({ F with inputPos := ip } : PhaseFrame x).cfg ())
      (by simp only [PhaseFrame.cfg_eq]) (by simp only [PhaseFrame.cfg_eq])
      (by simp only [PhaseFrame.cfg_eq]) rfl rfl).mp he
  · intro r w hr
    exact (phase_wordAt_congr (F.cfg ()) (({ F with inputPos := ip } : PhaseFrame x).cfg ()) r w
      (by simp only [PhaseFrame.cfg_eq]) (by simp only [PhaseFrame.cfg_eq])).mp (hregs r w hr)

end WordRAM.Sim
