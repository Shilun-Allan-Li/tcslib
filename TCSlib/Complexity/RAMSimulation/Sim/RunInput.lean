/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunInduction
import TCSlib.Complexity.RAMSimulation.Sim.RunStartup
import TCSlib.Complexity.RAMSimulation.Sim.RunBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From the input configuration to a completed simulation

Start-up is followed by the shared execution induction. A halting source stream agreeing
with the consumed coins closes the live-cutoff alternative and supplies the source output.
The branch and its bounds apply to both timed schedules and prescribed coin streams.

## Main definitions

No further machine is introduced.

## Main results

* `WordRAM.Sim.RunSetup.input_run`: a complete, bounded driven branch from the input.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2; Definition 4.1.)
-/

namespace WordRAM.Sim.RunSetup

open Turing

/-- A driver respecting a coin predicate realizes a bounded complete source run whenever
every permitted consumed prefix has an agreeing halting stream. A schedule-following driver
also makes the resulting word an initial slice of that schedule.
[AB09, Exercise 1.9], with explicit additive startup costs and visited-cell space.

**Proof sketch.** `startup_run` reaches the first encoded instruction with one stationary
dispatch. Apply `run_execution` with the RAM time bound as fuel. The supplied halting stream
and `RunExecution.completed` rule out a live cutoff, bound the exact touched cells by `f`,
and identify the output. Concatenate the actual branch words. `runSpace_append_le` counts
startup once and one common head interval per tape; `time_total_le` and `space_total_le`
absorb the fixed coefficients into the stated polynomials. -/
theorem input_run {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} (x : List Bool) (tw sw t f : ℕ)
    (hW : Mw.ComputesInTime x (Nat.bits W) tw)
    (hS : Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw)
    (D : RunDriver W) (B : ℕ → Bool → Prop) (hD : D.Respects B)
    (Q : List Bool → Bool → List Bool → Prop)
    (hhalt : ∀ coins, RunCoinsSatisfy B coins →
      ∃ ρ, RunCoinsAgree coins ρ ∧ ∃ v out, HaltsWithin P x ρ W t v out f ∧ Q ρ v out) :
    ∃ (w : List Bool) (e : Turing.Cfg (8 + A.extraTapes) Bool A.State x)
      (ρ : List Bool) (v : Bool) (out : List Bool),
      HaltsWithin P x ρ W t v out f ∧ Q ρ v out ∧ A.host.runWith w (A.host.initCfg x) = e ∧
      e.state = none ∧ e.output = (if fn then out else [v]) ∧
      w.length ≤ tw + A.boundCost * (t + 1) * (f * (W + 1) + W ^ 2 + x.length + 1) ∧
      A.host.spaceUsedWith w (A.host.initCfg x) ≤
        sw + A.boundCost * (f * (W + 1) + W + Complexity.logSpace x.length + 1) ∧
      (∀ χ, D.Follows χ → w = runChoices χ 0 w.length) := by
  let c := XCfg.init W x.length
  obtain ⟨t₀, o, d, ht₀, hr₀, hd, he, hs₀⟩ :=
    A.startup_run x W tw sw hW hS (D.word 0 c) (D.word_length 0 c) D.dispatch
  let w₀ := D.word 0 c t₀ ++ [D.dispatch t₀]
  have hw₀ : w₀.length = t₀ + 1 := by
    rw [List.length_append, D.word_length, List.length_singleton]
  have hpos : runPosition P c.pc = 0 := by
    apply Fin.ext
    rw [runPosition_val]
    dsimp only [c]
    rw [XCfg.init_def]
    exact Nat.zero_min _
  have hrd : c.rd = ([] : List Bool).length := by dsimp only [c]; rw [XCfg.init_def]; rfl
  obtain ⟨R⟩ := A.run_execution D B hD w₀.length t {-1} c o d [] false hrd
    (runCoinsSatisfy_nil B) (by rw [hpos]; exact hd) he
  obtain ⟨ρ, ha, v, out, hsource, hQ⟩ := hhalt R.outCoins R.coins_ok
  obtain ⟨hlt, hc, hdone, hout⟩ := R.completed hsource ha
  have hcard : ({-1} ∪ R.cells).card ≤ f + 1 := by
    have hu := Finset.card_union_le ({-1} : Finset ℤ) R.cells
    rw [Finset.card_singleton] at hu
    omega
  refine ⟨w₀ ++ R.word, R.finish, ρ, v, out, hsource, hQ, ?_, hdone, hout, ?_, ?_, ?_⟩
  · rw [NDTM.runWith_append, hr₀, R.run]
  · rw [List.length_append]
    have hraw : w₀.length + R.word.length ≤
        tw + A.startCost * (x.length + W ^ 2 + 1) + 1 +
          (R.steps + 1) * A.blockTime x.length W ({-1} ∪ R.cells).card := by
      have ht := R.time_bound
      omega
    exact hraw.trans (A.time_total_le x.length W tw t f _ R.steps hcard hlt)
  · have hspace := runSpace_append_le A.host w₀ R.word (A.host.initCfg x) d
      (A.blockRadius x.length W ({-1} ∪ R.cells).card) hr₀ R.envelope
    exact hspace.trans ((Nat.add_le_add_right hs₀ _).trans
      (A.space_total_le x.length W sw f _ hcard))
  · intro χ hDχ
    obtain ⟨hw, hdispatch⟩ := (RunDriver.follows_iff D χ).mp hDχ
    have hstart : w₀ = runChoices χ 0 w₀.length := by
      rw [hw₀]
      change D.word 0 c t₀ ++ [D.dispatch t₀] = runChoices χ 0 (t₀ + 1)
      rw [hw 0 c t₀, hdispatch t₀, runChoices_append χ 0 t₀ 1, Nat.zero_add, runChoices_one]
    calc
      w₀ ++ R.word = runChoices χ 0 w₀.length ++ runChoices χ w₀.length R.word.length :=
        congrArg₂ List.append hstart (R.follows χ hDχ)
      _ = runChoices χ 0 (w₀.length + R.word.length) := by
        rw [runChoices_append, Nat.zero_add]
      _ = runChoices χ 0 (w₀ ++ R.word).length :=
        congrArg (runChoices χ 0) (List.length_append (as := w₀) (bs := R.word)).symm

end WordRAM.Sim.RunSetup
