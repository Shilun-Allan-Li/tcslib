/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRows

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register invariants between instruction rows

The RAM encoding supplies correctly sized registers and dedicated blank scratch. These lemmas
keep the encoding and previously loaded operand words available as the frame rows are sequenced.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_frame_scratch`: an encoded frame supplies the row scratch precondition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The dedicated scratch tapes in an encoded frame satisfy the row scratch precondition. -/
theorem phase_frame_scratch {a W : ℕ} {x : List Bool} (fn : Bool) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) : PhaseScratch F := by
  apply (phaseScratch_iff F).mpr
  intro r hr z
  have hh := ((encodes_iff a fn T c (Function.Embedding.refl _) o (F.cfg ())).mp he).2.2.2.2.2.1
    r hr z
  simpa only [PhaseFrame.cfg_eq] using hh

/-- Each encoded register is ready at its prescribed width: the key width on tape one and
the word width on tapes two through four. -/
theorem phase_frame_ready {a W : ℕ} {x : List Bool} (fn : Bool) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) (r : Fin 8)
    (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) :
    PhaseReady (if r = 1 then W + a else W) r F := by
  have hh := (encodes_iff a fn T c (Function.Embedding.refl _) o (F.cfg ())).mp he
  by_cases hr : r = 1
  · subst r
    rw [if_pos rfl, phaseReady_iff]
    exact hh.2.2.1
  · rw [if_neg hr, phaseReady_iff]
    have hv : r.val ≠ 1 := by
      intro hv
      exact hr (Fin.ext hv)
    exact hh.2.2.2.1 r (by omega) hr₁

/-- A frame word write of the register's prescribed width preserves its RAM encoding. -/
theorem phase_frame_write_encodes {a W : ℕ} {x : List Bool} (fn : Bool) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) (r : Fin 8)
    (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) (w : List Bool)
    (hw : w.length = if r = 1 then W + a else W) :
    Encodes a fn T c (Function.Embedding.refl _) o ((F.write r w).cfg ()) := by
  simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq] using
    phase_encodes_wordWrite fn T c o (F.cfg ()) he r hr₀ hr₁ w hw

/-- Writing a word of the ready register's width establishes that exact word in the result
frame. -/
theorem phase_frame_write_word {x : List Bool} (F : PhaseFrame x) (r : Fin 8)
    (W : ℕ) (w : List Bool) (hr : PhaseReady W r F) (hw : w.length = W) :
    WordAt ((F.write r w).cfg ()) r w := by
  obtain ⟨old, hold, hwidth⟩ := (phaseReady_iff W r F).mp hr
  simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq] using
    phase_wordAt_write (F.cfg ()) r old w hold (hw.trans hwidth.symm)

/-- Writing one frame register preserves every word held on another register. -/
theorem phase_frame_write_other {x : List Bool} (F : PhaseFrame x) (r j : Fin 8)
    (w v : List Bool) (hj : j ≠ r) (hv : WordAt (F.cfg ()) j v) :
    WordAt ((F.write r w).cfg ()) j v := by
  apply (phase_wordAt_congr (F.cfg ()) ((F.write r w).cfg ()) j v ?_ ?_).mp hv
  · simp only [PhaseFrame.write_eq, PhaseFrame.cfg_eq, phase_wordWrite_as_update,
      Function.update_of_ne hj]
  · simp only [PhaseFrame.write_eq, PhaseFrame.cfg_eq]

/-- Removing a configuration's control and reinstalling unit control preserves its RAM
encoding, because every work tape, head and output is unchanged. -/
theorem phase_frame_ofCfg_encodes {a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o d) :
    Encodes a fn T c (Function.Embedding.refl _) o ((PhaseFrame.ofCfg d).cfg ()) := by
  apply (phase_encodes_congr fn T c c (Function.Embedding.refl _) o d
    ((PhaseFrame.ofCfg d).cfg ()) ?_ ?_ ?_ rfl rfl).mp he
  · simp only [PhaseFrame.cfg_eq, PhaseFrame.ofCfg_eq]
  · simp only [PhaseFrame.cfg_eq, PhaseFrame.ofCfg_eq]
  · simp only [PhaseFrame.cfg_eq, PhaseFrame.ofCfg_eq]

end WordRAM.Sim
