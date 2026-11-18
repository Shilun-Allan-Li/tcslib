/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Arbitrary branches of the finite RAM simulation

A finite word supplies an absolute-time schedule by its defaulted reads. The shared input
run follows that schedule until it halts. Uniform source halting bounds that prefix, so every
sufficiently long branch is the halted prefix followed by irrelevant choices.

## Main definitions

No new machine is introduced.

## Main results

* `WordRAM.Sim.RunSetup.branch_run`: every sufficiently long branch is a bounded source run.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2; Definition 4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim.RunSetup

open Turing

/-- Under uniform source halting, each sufficiently long host branch halts with the output
of some source stream and satisfies the common space bound.
[AB09, §2.1.2 and Exercise 1.9], with a visited-cell bound on every branch.

**Proof sketch.** Run `input_run` with the defaulted-read schedule of the given word and the
unrestricted coin predicate. Its consumed prefix itself is an agreeing source stream. The
schedule clause identifies the constructed word with a prefix of the given branch; the time
bound puts that prefix within the branch. `NDTM.runWith_of_halt` absorbs the remaining choices,
and `NDTM.spaceUsedWith_append_of_halt` preserves the prefix's visited-cell bound. -/
theorem branch_run {P : XProgram} {fn : Bool} {Mw : FinTM Bool}
    (A : RunSetup P fn Mw) {W : ℕ} (x : List Bool) (tw sw t f : ℕ)
    (hW : Mw.ComputesInTime x (Nat.bits W) tw)
    (hS : Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw)
    (hhalt : ∀ ρ, ∃ v out, HaltsWithin P x ρ W t v out f)
    (w : List Bool)
    (hw : tw + A.boundCost * (t + 1) * (f * (W + 1) + W ^ 2 + x.length + 1) ≤ w.length) :
    ∃ ρ v out, HaltsWithin P x ρ W t v out f ∧
      (A.host.runWith w (A.host.initCfg x)).state = none ∧
      (A.host.runWith w (A.host.initCfg x)).output = (if fn then out else [v]) ∧
      A.host.spaceUsedWith w (A.host.initCfg x) ≤
        sw + A.boundCost * (f * (W + 1) + W + Complexity.logSpace x.length + 1) := by
  let χ := fun i => w.getD i false
  let D : RunDriver W := RunDriver.ofSchedule χ
  have hD : D.Respects (fun _ _ => True) :=
    (RunDriver.respects_iff D _).mpr (fun _ _ => True.intro)
  have hsource : ∀ coins, RunCoinsSatisfy (fun _ _ => True) coins →
      ∃ ρ, RunCoinsAgree coins ρ ∧ ∃ v out, HaltsWithin P x ρ W t v out f ∧ True := by
    intro coins _
    obtain ⟨v, out, h⟩ := hhalt coins
    exact ⟨coins, runCoinsAgree_refl coins, v, out, h, True.intro⟩
  obtain ⟨u, e, ρ, v, out, hρ, _, hr, hd, ho, ht, hs, hf⟩ :=
    A.input_run x tw sw t f hW hS D (fun _ _ => True) hD (fun _ _ _ => True) hsource
  have hlen : u.length ≤ w.length := ht.trans hw
  have hprefix : u = w.take u.length :=
    (hf χ (RunDriver.ofSchedule_follows χ)).trans (runChoices_take w u.length hlen)
  have hsplit : w = u ++ w.drop u.length :=
    (List.take_append_drop u.length w).symm.trans
      (congrArg (fun z => z ++ w.drop u.length) hprefix.symm)
  have hfinal : A.host.runWith w (A.host.initCfg x) = e := by
    rw [hsplit, NDTM.runWith_append, hr, NDTM.runWith_of_halt e hd]
  refine ⟨ρ, v, out, hρ, by rw [hfinal]; exact hd, by rw [hfinal]; exact ho, ?_⟩
  have hspace : A.host.spaceUsedWith w (A.host.initCfg x) =
      A.host.spaceUsedWith u (A.host.initCfg x) := by
    rw [hsplit]
    exact NDTM.spaceUsedWith_append_of_halt A.host (by rw [hr]; exact hd) _
  exact hspace.le.trans hs

end WordRAM.Sim.RunSetup
