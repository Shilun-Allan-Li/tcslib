/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite coordinate restriction under uniform sampling

## Main definitions

This module introduces no definitions.

## Main results

* `FiniteRandomness.expect_sample_embedding_independent`: a selected family of distinct
  coordinates of a uniform finite function is fresh jointly with every residual test
  that ignores those coordinates. The complementary coordinates remain sampled.

## References

* TCSlib contributors, *TCSlib*, `Cryptography/Games/Probability.lean`, the uniform
  equivalence and single-coordinate sampling laws, and `Games/Bridges/Experiments.lean`,
  the product sampling law.
* The Mathlib community, *Mathlib*, `Logic/Equiv/Prod.lean` and
  `Logic/Equiv/Fintype.lean`, finite-function image/complement and range equivalences.

The theorem is technical finite-probability glue for the existing sampling interface.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FiniteRandomness

open TCSlib.Cryptography.Games

/-- Restricting a uniform finite function to an embedded coordinate family gives fresh
uniform values jointly with every residual test that ignores those coordinates. The full
original function remains drawn on the right; no unused coordinate is deleted. Framework
glue, generalizing the existing single-coordinate `ProbComp.expect_sample_coord` API.

**Proof sketch.** Use the standard image/complement function splitting equivalence and
reindex the image by the given embedding. Apply the published uniform equivalence and
product laws. The residual-test hypothesis permits replacing the image component while
retaining the complementary coordinates. No counting argument or sampler is constructed. -/
theorem expect_sample_embedding_independent
    {I J C : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype C] [Nonempty C] (e : I ↪ J)
    (F : (I → C) → (J → C) → ℝ)
    (hF : ∀ (r : I → C) (T T' : J → C),
      (∀ j, (∀ i, e i ≠ j) → T j = T' j) → F r T = F r T') :
    ProbComp.expect (ProbComp.sample (J → C)) (fun T => F (fun i => T (e i)) T) =
      ProbComp.expect (ProbComp.sample (I → C))
        (fun r => ProbComp.expect (ProbComp.sample (J → C)) (F r)) := by
  let inside : J → Prop := fun j => ∃ i : I, e i = j
  letI : DecidablePred inside := fun _ => Classical.propDecidable _
  let Outside : Type := {j : J // ¬inside j}
  let indexEquiv : I ≃ {j : J // inside j} := e.toEquivRange
  let split : (J → C) ≃ ((I → C) × (Outside → C)) :=
    (Equiv.piEquivPiSubtypeProd inside (fun _ => C)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr indexEquiv.symm (Equiv.refl C)) (Equiv.refl (Outside → C)))
  have hFst (T : J → C) : (split T).1 = fun i => T (e i) := rfl
  -- The residual observer sees only the unchanged complement of the selected image.
  have hIgnore (r r' : I → C) (u : Outside → C) :
      F r (split.symm (r, u)) = F r (split.symm (r', u)) := ?_
  swap
  · apply hF
    intro j hj
    have hOut : ¬inside j := fun ⟨i, hi⟩ => hj i hi
    refine (show
      (if h : inside j then r (indexEquiv.symm ⟨j, h⟩) else u ⟨j, h⟩) =
        (if h : inside j then r' (indexEquiv.symm ⟨j, h⟩) else u ⟨j, h⟩) from ?_)
    simp only [dif_neg hOut]
  -- Split the original uniform function into its selected image and full complement.
  have hLeft := ProbComp.expect_sample_equiv split
    (fun p : (I → C) × (Outside → C) => F p.1 (split.symm p))
  simp only [hFst, split.symm_apply_apply] at hLeft
  rw [hLeft, ← Bridge.expect_sample_pair (α := I → C) (β := Outside → C)
    (fun p => F p.1 (split.symm p))]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  apply congrArg (ProbComp.expect (ProbComp.sample (I → C)))
  funext r
  -- Reindex the untouched full function on the right by the same existing equivalence.
  have hRight := ProbComp.expect_sample_equiv split
    (fun p : (I → C) × (Outside → C) => F r (split.symm p))
  simp only [split.symm_apply_apply] at hRight
  rw [hRight, ← Bridge.expect_sample_pair (α := I → C) (β := Outside → C)
    (fun p => F r (split.symm p))]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  simp only [← hIgnore r, ProbComp.expect_const]

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FiniteRandomness
