/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Collision-game acceptance as a uniform average

The collision game's two samples can be read as the existing uniform expectation
over generator coins and uniform probability over finder coins. This provides the
probability interface used by the discrete-logarithm reduction.

## Main definitions

There are no new definitions.

## Main results

* `expect_sample_eq_uexp` identifies finite uniform sampling with `uexp`.
* `collision_accept_eq` reads collision-game acceptance as a nested uniform average.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Definition 140.1 and proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The expectation of `f` after sampling a nonempty finite type is the uniform
average `uexp f`. Both expressions are the sum of `f` divided by the type's size. -/
theorem expect_sample_eq_uexp {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ProbComp.expect (ProbComp.sample α) f = uexp f := by
  rw [ProbComp.expect_sample, uexp_def, inv_mul_eq_div]

/-- Collision-game acceptance is the average over generator coins of the probability,
over finder coins, that the two padded output halves are distinct domain elements
with equal hashes [PS10, Definition 140.1].

**Proof sketch.** Read the collision game and apply total probability to its two
samples. A pure Boolean verdict accepts exactly when its collision predicate holds;
the finite sampling expectations are the existing uniform average and probability. -/
theorem collision_accept_eq (C : CRH) (A : NUPPT) (n : ℕ) :
    accept (C.collisionGame A n) =
      uexp (fun rg : C.gen.Coins n =>
        uprob (fun r : A.Coins n =>
          let i := C.gen.runAt n [] rg
          let xx := splitBits
            (padFin (C.domLen.eval n + C.domLen.eval n) (A.runAt n i r))
          C.inDom n i xx.1 = true ∧ C.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
            C.hash n i xx.1 = C.hash n i xx.2)) := by
  classical
  rw [accept_eq, CRH.collisionGame_eq, ProbComp.prob_bind, expect_sample_eq_uexp]
  congr 1
  funext rg
  rw [ProbComp.prob_bind, expect_sample_eq_uexp, uprob_eq_uexp]
  congr 1
  funext r
  simp only [ProbComp.prob_pure, decide_eq_true_eq]

end TCSlib.Cryptography.Authentication.FromDiscreteLog
