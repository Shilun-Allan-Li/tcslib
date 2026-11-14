/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.DiscreteLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Switching the sampled exponent to a uniform residue

The bounded rejection sampler is statistically close to a uniform number below
the group order. Identifying these numbers with the residues in `ZMod` gives the
distribution switch used by the discrete-logarithm reduction, including arbitrary
independent auxiliary coins.

## Main definitions

* `residueFinEquiv` identifies residues with bounded naturals at an equal modulus.

## Main results

* `sampleBelowL_uprob_le` bounds a sampled test by its ideal uniform-residue test
  plus `(1/2)^n`.

## Promotion requests

`residueFinEquiv` and its readers are general finite-residue encoding helpers.
`sampleBelowL_uprob_le` is a general reader of the candidate layer's sampler law.
They can be promoted to the shared encoding and candidate layers respectively.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, proof of Theorem 142.3; the bounded sampler convention is that of
  the exponentiation collection in §2.8.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open TCSlib.Cryptography TCSlib.Cryptography.Candidates

/-- Residues modulo a nonzero `m` are equivalent to `Fin k` when `m = k`, using
Mathlib's finite-residue ring equivalence and transport of the finite bound. -/
def residueFinEquiv {m k : ℕ} [NeZero m] (h : m = k) : ZMod m ≃ Fin k :=
  (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h)

/-- The residue-to-finite equivalence is Mathlib's inverse `finEquiv`, followed by
transport along the equality of the moduli. -/
theorem residueFinEquiv_eq {m k : ℕ} [NeZero m] (h : m = k) :
    residueFinEquiv h = (ZMod.finEquiv m).symm.toEquiv.trans (finCongr h) := rfl

/-- The residue-to-finite equivalence preserves the natural representative:
`(residueFinEquiv h z).val = z.val`. -/
theorem residueFinEquiv_val {m k : ℕ} [NeZero m] (h : m = k) (z : ZMod m) :
    (residueFinEquiv h z).val = z.val := by
  subst k
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

/-- For a valid group index of order below `2^n`, any test of the rejection-sampled
exponent and independent finite auxiliary coins has probability at most its
probability for a uniform exponent in `ZMod (expOrd i)` plus `(1/2)^n`
[PS10, proof of Theorem 142.3, using the candidate-layer sampler convention].

**Proof sketch.** Apply the published statistical-closeness theorem for bounded
rejection sampling. Relabel its ideal finite seed by the value-preserving residue
equivalence, then apply the statistical-switch bound with auxiliary coins and take
the upper side of its absolute-value bound. -/
theorem sampleBelowL_uprob_le {i : List Bool} (hi : ExpValid i) {n : ℕ}
    (hmn : dlM i < 2 ^ n) {ρ : Type*} [Fintype ρ] (P : ℕ → ρ → Prop) :
    uprob (fun z : (Fin (n * n) → Bool) × ρ =>
      P ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn z.1)).getD 0) z.2) ≤
      uprob (fun z : ZMod (expOrd i) × ρ => P z.1.val z.2) + (1 / 2 : ℝ) ^ n := by
  have hm : 0 < dlM i := ((expValid_iff i).1 hi).2.1
  have hs := ((statClose_sampleBelowL hm hmn).comp_equiv_right
    (residueFinEquiv (expOrd_of_valid hi))).abs_uprob_sub_le_prod P
  simp only [residueFinEquiv_val] at hs
  linarith [(abs_le.1 hs).2]

end TCSlib.Cryptography.Authentication.FromDiscreteLog
