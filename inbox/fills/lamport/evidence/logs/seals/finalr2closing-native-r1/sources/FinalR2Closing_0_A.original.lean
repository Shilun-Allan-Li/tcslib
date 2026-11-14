/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closing Lamport's linear-loss reduction

## Main definitions

None.

## Main results

* `negligible_of_linear_bound`: a nonnegative function bounded by `2n` times a negligible
  nonnegative function for `n ≥ 1` is negligible.
* `oneTimeSecure_of_inversion_bound`: the same bound for each forger proves one-time security.

The zero parameter is excluded only from the eventual comparison supplied to
`Negligible.mono`; no value at zero is changed or assumed.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open Complexity TCSlib.Cryptography.Games

/-- If `e` and `p` are nonnegative, `p` is negligible, and `e(n) ≤ 2n·p(n)` for `n ≥ 1`,
then `e` is negligible. [PS10, final step of the proof of Theorem 137.2].

**Proof sketch.** Multiplication by `n` and then by two preserves negligibility. The eventual
comparison starts at one, so the zero parameter is a finite exception. -/
theorem negligible_of_linear_bound {e p : ℕ → ℝ} (hp : Negligible p)
    (hp0 : ∀ n, 0 ≤ p n) (he0 : ∀ n, 0 ≤ e n)
    (hbound : ∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * p n) : Negligible e := by
  have hmajorant : Negligible (fun n => (2 : ℝ) * ((n : ℝ) ^ 1 * p n)) :=
    (hp.mul_pow 1).const_mul 2
  apply hmajorant.mono
  refine ⟨1, fun n hn => ?_⟩
  have hnonneg : 0 ≤ (2 : ℝ) * ((n : ℝ) ^ 1 * p n) :=
    mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 1) (hp0 n))
  rw [abs_of_nonneg (he0 n), abs_of_nonneg hnonneg]
  simpa only [pow_one, mul_assoc] using hbound n hn

/-- A nonnegative advantage bounded by `2n` times the inversion probability of a fixed
machine against a strong one-way family is negligible for all parameters, with no condition
needed at zero. [PS10, final step of the proof of Theorem 137.2]. -/
theorem negligible_of_inversion_bound (F : FunFamily) (hf : F.StrongOneWay) (B : NUPPT)
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
    (hbound : ∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * F.invProbAt B n) : Negligible e :=
  negligible_of_linear_bound (hf.hard B) (F.invProbAt_nonneg B) he0 hbound

/-- A signature scheme is one-time secure if each forger yields a fixed machine whose
inversion probability against a strong one-way family bounds its forgery probability with
loss `2n` for `n ≥ 1`. [PS10, reduction conclusion in Theorem 137.2].

**Proof sketch.** Use each forger's own acceptance probability as its security majorant.
Polynomial-factor closure proves that majorant negligible; its pointwise bound is equality. -/
theorem oneTimeSecure_of_inversion_bound (S : SignatureScheme) (F : FunFamily)
    (hf : F.StrongOneWay)
    (hred : ∀ A : NUPPT, ∃ B : NUPPT, ∀ n ≥ 1,
      accept (S.forgeGame A 1 n) ≤ 2 * (n : ℝ) * F.invProbAt B n) : S.OneTimeSecure := by
  apply (S.oneTimeSecure_iff).2
  intro A
  obtain ⟨B, hB⟩ := hred A
  refine ⟨fun n => accept (S.forgeGame A 1 n), ?_, fun _ => le_rfl⟩
  exact negligible_of_inversion_bound F hf B _ (fun n => accept_nonneg _) hB

/-- The probability-form reduction `ε(n)/(2n) ≤ inv_B(n)` also implies one-time security.
[PS10, averaging bound and conclusion in Theorem 137.2]. -/
theorem oneTimeSecure_of_inversion_lower (S : SignatureScheme) (F : FunFamily)
    (hf : F.StrongOneWay)
    (hred : ∀ A : NUPPT, ∃ B : NUPPT, ∀ n ≥ 1,
      accept (S.forgeGame A 1 n) / (2 * (n : ℝ)) ≤ F.invProbAt B n) : S.OneTimeSecure := by
  apply oneTimeSecure_of_inversion_bound S F hf
  intro A
  obtain ⟨B, hB⟩ := hred A
  refine ⟨B, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
  have hden : 0 < (2 : ℝ) * (n : ℝ) := mul_pos (by norm_num) hn0
  have h := (div_le_iff₀ hden).1 (hB n hn)
  simpa only [mul_comm (F.invProbAt B n) (2 * (n : ℝ))] using h

end TCSlib.Cryptography.Authentication.LamportReduction
