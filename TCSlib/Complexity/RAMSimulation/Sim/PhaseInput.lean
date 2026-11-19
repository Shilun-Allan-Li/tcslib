/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseMemory

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Input-bit rows of an instruction phase

The input row reads a position from word register two, uses the input-length word on tape five,
and writes the resulting bit word to register four. Its input-head endpoint may vary, while all
work heads return to their origins.

## Main definitions

* `WordRAM.Sim.phaseInputBank`: the position, length, result and scratch tape bank.

## Main results

* `WordRAM.Sim.phase_inputRow`: place the native input-bit row on eight tapes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The input-bit bank reads the position on tape two and length on tape five, writes tape four,
and uses scratch tapes six and seven. -/
def phaseInputBank : Fin 5 ↪ Fin 8 := ⟨![2, 5, 4, 6, 7], by decide⟩

/-- The input bank sends its five source indices to `2, 5, 4, 6, 7`, respectively. -/
theorem phaseInputBank_apply (r : Fin 5) : phaseInputBank r = ![2, 5, 4, 6, 7] r := rfl

/-- The input-bit row writes the bit word to register four, with linear input-length time and
logarithmic input-length radius. Its existential input-head function records the native row's
unconstrained final input-head location.

**Proof sketch.** Choose `exists_inputBitTM`. Register readiness supplies the old destination
word, and the selection lemmas supply the position, input-length and scratch layouts. Choose
its final input position under the precondition, with the original position as a total default.
`phase_nativeRow` and `phase_embed_wordWrite` place the exact native endpoint. -/
theorem phase_inputRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) :
    ∃ (C : ℕ) (ip : ∀ {x : List Bool}, I x → PhaseFrame x → Fin (x.length + 2)),
      Nonempty (PhaseRow I
        (fun {x} i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
          WordAt (F.cfg ()) 5 (Nat.bits x.length) ∧ PhaseReady (width i) 4 F ∧ PhaseScratch F)
        (fun {x} i F => { F.write 4 (bvBits (inBitWord (width i) x (u i).toInt)) with
          inputPos := ip i F })
        (fun {x} i => C * (width i + x.length + 1))
        (fun {x} i => C * (width i + (Nat.bits x.length).length + 1))) := by
  classical
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_inputBitTM
  letI := hfin
  letI := hdec
  let pre : ∀ {x : List Bool}, I x → PhaseFrame x → Prop := fun {x} i F =>
    WordAt (F.cfg ()) 2 (bvBits (u i)) ∧ WordAt (F.cfg ()) 5 (Nat.bits x.length) ∧
      PhaseReady (width i) 4 F ∧ PhaseScratch F
  have hn : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), pre i F →
      ∃ ip : Fin (x.length + 2),
        ReachesWithin M ((F.cfg entry).select phaseInputBank) {some exit}
          (C * (width i + x.length + 1)) (C * (width i + (Nat.bits x.length).length + 1))
          { ((F.cfg entry).select phaseInputBank) with
            state := some exit
            inputPos := ip
            workTapes := wordWrite ((F.cfg entry).select phaseInputBank) 2
              (bvBits (inBitWord (width i) x (u i).toInt)) } := by
    intro x i F hp
    obtain ⟨w, hw, hwlen⟩ := (phaseReady_iff (width i) 4 F).mp hp.2.2.1
    obtain ⟨ip, hr⟩ := hM (u i) w ((F.cfg entry).select phaseInputBank)
      (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq])
      ((phase_wordAt_select phaseInputBank (F.cfg entry) 0 _).mpr
        ((phase_wordAt_frame F entry 2 _).mpr hp.1))
      ((phase_wordAt_select phaseInputBank (F.cfg entry) 1 _).mpr
        ((phase_wordAt_frame F entry 5 _).mpr hp.2.1))
      ((phase_wordAt_select phaseInputBank (F.cfg entry) 2 w).mpr
        ((phase_wordAt_frame F entry 4 w).mpr hw))
      hwlen (phase_scratch_select phaseInputBank F entry (by decide) hp.2.2.2)
    exact ⟨ip, by simpa only [inBitWord_def] using hr⟩
  let ip : ∀ {x : List Bool}, I x → PhaseFrame x → Fin (x.length + 2) :=
    fun i F => if hp : pre i F then Classical.choose (hn i F hp) else F.inputPos
  refine ⟨C, ip, ?_⟩
  apply phase_nativeRow (I := I) pre _ _ _ S M entry exit phaseInputBank
    (fun {x} i F => { ((F.cfg entry).select phaseInputBank) with
      state := some exit
      inputPos := ip i F
      workTapes := wordWrite ((F.cfg entry).select phaseInputBank) 2
        (bvBits (inBitWord (width i) x (u i).toInt)) })
  · intro x i F hp
    simpa only [ip, dif_pos hp] using Classical.choose_spec (hn i F hp)
  · intro x i F hp
    simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq, Cfg.select_eq,
      phase_wordWrite_as_update, phaseInputBank_apply] using
      phase_embed_wordWrite phaseInputBank (F.cfg entry) (some exit) (ip i F) 2
        (bvBits (inBitWord (width i) x (u i).toInt))
  · intro x i F hp
    simp only [PhaseFrame.write_eq]

end WordRAM.Sim
