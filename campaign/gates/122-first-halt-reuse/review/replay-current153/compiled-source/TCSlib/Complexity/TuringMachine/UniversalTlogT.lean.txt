/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.TwoTapes
import TCSlib.Complexity.TuringMachine.UniversalK

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficient universal machine

[AB09, Theorem 1.9]: one machine `U` simulates every machine `M`, given a code `α` of `M`, with
overhead `C · T log T` for a run of `T` steps, where `C` depends on `M` but not on the input.

## Deviations from [AB09]

* The code quantifier is relaxed as in `Turing.universal_quadratic`: every machine has some code
  `α` with which `U` simulates it. [AB09] states the simulation for every code of every machine;
  here the code is one of the two-work-tape normal form's, through the two-tape reduction.
* The statement is per run and includes the converse: every completed output of `U` on
  `⟨α, x⟩` is an output of `M` on `x`.
* The overhead is `C · (t + 1)(log₂(t + 1) + 1)`, padded so that it covers `t = 0`.

## Main definitions

No new definitions: the universal machine is an existential contract.

## Main results

* `Turing.universal_TlogT` — [AB09, Theorem 1.9].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 1.9 and its proof, §1.7.)
-/

namespace Turing

/-- **The efficient universal machine** [AB09, Theorem 1.9]: there is one binary machine `U`
such that every binary machine `M` has a code `α` and a constant `C` with which `U` reproduces
each halting run of `M` of `t` steps on input `x`, on the paired input `⟨α, x⟩`, within
`C · (t + 1)(log₂(t + 1) + 1)` steps; and every completed output of `U` on `⟨α, x⟩` is an
output of `M` on `x`.

**Proof sketch.** Take `U` to be the code-first evaluator `Turing.universalK` at two work tapes,
over the two-tape scheme `c`. Given `M`, reduce it to two work tapes
(`Turing.FinTM.two_work_tapes_run`, overhead `c₁ · (t + 1)(log₂(t + 1) + 1)`) and code the result
(`Turing.exists_code2TM`); `α` is that code. `U` simulates the coded machine within linear
overhead `C (t' + 1)`, so a run of `M` of `t` steps costs at most
`C (c₁ (t + 1)(log₂(t + 1) + 1) + 1) ≤ C (c₁ + 1)(t + 1)(log₂(t + 1) + 1)` steps of `U`. The
converse composes the converses of the two steps. -/
theorem universal_TlogT (c : EffectiveMachineCode2) :
    ∃ U : FinTM Bool, ∀ M : FinTM Bool, ∃ (α : List Bool) (C : ℕ),
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨U, hU⟩ := universalK 2 c.toK
  refine ⟨U, fun M => ?_⟩
  obtain ⟨M', c₁, hk, hfwd, hback⟩ := FinTM.two_work_tapes_run M
  obtain ⟨N, hN⟩ := exists_code2TM M' hk
  have hdec : c.toK.toFinTM (c.encode N) = N.toFinTM := by
    rw [EffectiveMachineCode2.toK_toFinTM, c.toMachineCode2.decode_encode N]
  obtain ⟨C, hC⟩ := hU (c.encode N)
  refine ⟨c.encode N, C * (c₁ + 1), fun x output t h => ?_, fun x output h => ?_⟩
  · have h₁ := (hN x output _).2 (hfwd x output t h)
    rw [← hdec] at h₁
    apply ((hC x).1 output _ h₁).mono
    have hpos : 1 ≤ (t + 1) * (Nat.log 2 (t + 1) + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc C * (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)) + 1)
        ≤ C * ((c₁ + 1) * ((t + 1) * (Nat.log 2 (t + 1) + 1))) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = C * (c₁ + 1) * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := by ring
  · obtain ⟨t, ht⟩ := (hC x).2 output h
    rw [hdec] at ht
    exact hback x output ⟨t, (hN x output t).1 ht⟩

end Turing
