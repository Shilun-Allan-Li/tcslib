/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The planted reduction probability is bounded by machine inversion

## Main definitions

None.

## Main results

* `fairBit_redProbability_le_invProbAt`: a realization of successful typed reductions by a
  machine transfers the typed fair-bit success probability to the family's inversion game.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2. This is generic probability and machine transport glue.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity TCSlib.Cryptography.Games

/-- Suppose a machine's coins are a fair planting bit, a complete key table and forger coins,
and every successful typed planted run yields the machine's correctly encoded preimage.
Then the typed reduction's success averaged over the fair bit is at most the machine's
inversion probability against the function family. The preimage width is the family's
actual input width, so no dependent width casts are needed.
[PS10, proof of Theorem 137.2].

**Proof sketch.** Read the machine inversion probability as the uniform probability that its
output encodes a preimage. Product sampling separates the challenge preimage and machine
coins. Reindex the latter by the given coin equivalence, and split the resulting product
sample into its bit, table and forger coins using the published product-sampling law.
Commute the independent bit and challenge samples on the typed side. All remaining samples
have the same order, and the realization hypothesis implies the pointwise event inclusion.
No query-cost assumption is needed for this transport: it is already encapsulated in the
realization hypothesis. -/
theorem fairBit_redProbability_le_invProbAt (F : FunFamily) (n : ℕ) (A B : NUPPT)
    (i : Fin (F.inLen.eval n))
    (adv : ((Fin (F.inLen.eval n) × Bool) → Fin (F.outLen.eval n) → Bool) →
      A.Coins n → OracleComp
        (bitSpec (fun _ : Fin 1 => F.inLen.eval n)
          (fun _ => F.inLen.eval n * F.inLen.eval n))
        (Fin (F.inLen.eval n + F.inLen.eval n * F.inLen.eval n) → Bool))
    (e : ((Bool × Table (F.inLen.eval n)) × A.Coins n) ≃ B.Coins n)
    (hreal : ∀ (y : Fin (F.outLen.eval n) → Bool) (T : Table (F.inLen.eval n))
        (c : Bool) (r : A.Coins n),
      RedSuccess (F.f n) adv y T r (i, c) →
        ∃ x' : Fin (F.inLen.eval n) → Bool,
          B.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ F.f n x' = y) :
    ProbComp.expect (ProbComp.sample Bool)
        (fun c => redProbability (F.f n) adv (i, c)) ≤ F.invProbAt B n := by
  classical
  rw [FunFamily.invProbAt_eq_uprob, ← Bridge.prob_sample_eq_uprob,
    ProbComp.prob_eq_expect, ← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  rw [← ProbComp.expect_sample_equiv e]
  simp only [redProbability_eq]
  rw [ProbComp.expect_sample_comm]
  simp only [← Bridge.expect_sample_pair, ProbComp.expect_bind, ProbComp.expect_pure]
  apply ProbComp.expect_mono
  intro x
  apply ProbComp.expect_mono
  intro c
  apply ProbComp.expect_mono
  intro T
  apply ProbComp.expect_mono
  intro r
  by_cases hs : RedSuccess (F.f n) adv (F.f n x) T r (i, c)
  · have hwin := hreal (F.f n x) T c r hs
    rw [if_pos hs, if_pos hwin] <;> exact le_rfl
  · rw [if_neg hs]
    split_ifs <;> positivity

end TCSlib.Cryptography.Authentication.LamportFill
