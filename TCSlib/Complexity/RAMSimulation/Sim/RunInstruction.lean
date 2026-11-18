/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunStep
import TCSlib.Complexity.RAMSimulation.Sim.RunDriver
import TCSlib.Complexity.RAMSimulation.Sim.RunCosts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One instruction under either choice driver

This is the common step interface for the master execution induction. An ordinary phase
dispatches and restores all heads; a verdict phase halts. Both cases have the same uniform
time and radius bounds, and words from a timed schedule remain actual slices of that schedule.

## Main definitions

No further machine is constructed here.

## Main results

* `WordRAM.Sim.RunSetup.instruction_run`: the uniform driven instruction step.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2; Definition 4.1.)
-/

namespace WordRAM.Sim.RunSetup

open Turing

variable {P : XProgram} {fn : Bool} {Mw : FinTM Bool} (A : RunSetup P fn Mw)

/-- Execute one source instruction using driver `D` at absolute time `s`. The supplied stream
agrees with the driver's coin at this instruction. A continuing endpoint restores all heads
and encodes its successor; a verdict endpoint is halted with the correct output. If the driver
follows a schedule, the entire word, including a dispatch when present, is its timed slice.

**Proof sketch.** Case on the source step and use `host_ordinary` or `host_verdict` with the
driver's words and entry bit. The finite maximum coefficient gives `blockTime` and
`blockRadius` by `phase_time_le` and `phase_radius_le`. In the ordinary case, concatenate the
phase slice and its one-bit dispatch by `runChoices_append`; the verdict case is one slice. -/
theorem instruction_run {x ρ : List Bool} {W : ℕ} (D : RunDriver W) (s : ℕ) (par : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
    (d : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
    (hd : d.state = some ⟨some (runPosition P c.pc, par),
      (A.phases (runPosition P c.pc)).entry⟩)
    (he : Encodes A.width fn T c (Fin.castAddEmb A.extraTapes) o d)
    (hcoin : isCoin (P.getD c.pc (.base .reject)) = true →
      ρ.getD c.rd false = D.coin s c) :
    ∃ (w : List Bool) (d' : Turing.Cfg (8 + A.extraTapes) Bool A.State x),
      w.length ≤ A.blockTime x.length W T.card ∧ A.host.runWith w d = d' ∧
      (∀ u ≤ w.length, ∀ j,
        |(A.host.runWith (w.take u) d).workTapePos j - d.workTapePos j| ≤
          (A.blockRadius x.length W T.card : ℕ)) ∧
      (∀ χ, D.Follows χ → w = runChoices χ s w.length) ∧
      match xstep P x ρ c with
      | .inl c' => Encodes A.width fn (T ∪ (P.getD c.pc (.base .reject)).touches c.mem) c'
          (Fin.castAddEmb A.extraTapes) o d' ∧
          d'.state = some ⟨some (runPosition P c'.pc, !par),
            (A.phases (runPosition P c'.pc)).entry⟩ ∧ d'.workTapePos = d.workTapePos
      | .inr v => d'.state = none ∧ d'.output = (if fn then c.out else [v]) := by
  cases hs : xstep P x ρ c with
  | inl c' =>
    obtain ⟨t, e, ht, hr, hd', he', hh, henv⟩ :=
      A.host_ordinary par (D.coin s c) T c c' o d hd he hs hcoin
        (D.word s c) (D.word_length s c) (D.word_head s c) (fun t => D.dispatch (s + t))
    let w := D.word s c t ++ [D.dispatch (s + t)]
    have hw : w.length = t + 1 := by
      rw [List.length_append, D.word_length, List.length_singleton]
    refine ⟨w, e, ?_, hr, ?_, ?_, ⟨he', hd', hh⟩⟩
    · rw [hw]
      exact (Nat.succ_le_succ ht).trans (A.phase_time_le _ _ _ _)
    · intro u hu j
      exact (henv u (by omega) j).trans (by exact_mod_cast (A.phase_radius_le
        (runPosition P c.pc) x.length W T.card))
    · intro χ hD
      obtain ⟨hword, hdispatch⟩ := (RunDriver.follows_iff D χ).mp hD
      rw [hw]
      change D.word s c t ++ [D.dispatch (s + t)] = runChoices χ s (t + 1)
      rw [hword s c t, hdispatch (s + t), runChoices_append χ s t 1, runChoices_one]
  | inr v =>
    obtain ⟨t, e, ht, hr, hd', ho, henv⟩ :=
      A.host_verdict par (D.coin s c) T c v o d hd he hs
        (D.word s c) (D.word_length s c) (D.word_head s c)
    let w := D.word s c t
    have hw : w.length = t := D.word_length s c t
    refine ⟨w, e, ?_, hr, ?_, ?_, ⟨hd', ho⟩⟩
    · rw [hw]
      exact ht.trans ((Nat.le_succ _).trans (A.phase_time_le _ _ _ _))
    · intro u hu j
      exact (henv u (by omega) j).trans (by exact_mod_cast (A.phase_radius_le
        (runPosition P c.pc) x.length W T.card))
    · intro χ hD
      rw [hw]
      exact ((RunDriver.follows_iff D χ).mp hD).1 s c t

end WordRAM.Sim.RunSetup
