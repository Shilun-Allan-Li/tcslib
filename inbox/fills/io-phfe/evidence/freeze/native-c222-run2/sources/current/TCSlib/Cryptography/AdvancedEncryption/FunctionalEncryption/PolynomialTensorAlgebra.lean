/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padded monomial representations

This module isolates the finite algebra behind the padded coefficient tensors used
for [GJLS21, Section 9, printed pp.57–58]. It depends only on Mathlib and does not
introduce an encoding, a sampler or a computational representation of polynomials.

## Main definitions

The results use finite tuples and their weighted products directly.

## Main results

* `PolynomialTensorAlgebra.exists_padded_tuple`: a bounded monomial is a product
  of exactly the supplied number of variable or constant labels.

* `PolynomialTensorAlgebra.exists_quadratic_expansion`: finite coefficient collection
  into padded public tuples and private pairs.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, ePrint 2020/764, Section 9, printed pp.57–58.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PolynomialTensorAlgebra

open scoped BigOperators

/-- Every finite monomial of total degree at most d is represented by a length-d
word of variable labels and a final constant label. The word is fixed before the
variable values. This is technical padding glue for [GJLS21, Section 9, pp.57–58].

**Proof sketch.** Repeat each variable label according to its exponent, concatenate
those finite lists, and append constant labels up to the supplied degree. The
published list/tuple product and replicate identities identify its weighted product
with the original power product; the degree bound certifies the padded length. -/
theorem exists_padded_tuple {R : Type*} [CommMonoid R] (m d : ℕ) (e : Fin m → ℕ)
    (he : ∑ i : Fin m, e i ≤ d) :
    ∃ tau : Fin d → Fin (m + 1), ∀ x : Fin m → R,
      (∏ j : Fin d, Fin.snoc (α := fun _ => R) x 1 (tau j)) =
        ∏ i : Fin m, x i ^ e i := by
  let labels : List (Fin (m + 1)) :=
    (List.ofFn (fun i : Fin m => List.replicate (e i) i.castSucc)).flatten
  have hlength : labels.length = ∑ i : Fin m, e i := by
    simp only [labels, List.length_flatten, ← List.ofFn_comp',
      List.length_replicate, List.sum_ofFn]
  let padded := labels ++ List.replicate (d - labels.length) (Fin.last m)
  have hpadded : padded.length = d := by
    simp only [padded, List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le (hlength.le.trans he)
  rw [← hpadded]
  refine ⟨padded.get, fun x => ?_⟩
  rw [← Fin.prod_ofFn, List.ofFn_comp', List.ofFn_get]
  change ((labels ++ List.replicate (d - labels.length) (Fin.last m)).map
    (Fin.snoc (α := fun _ => R) x 1)).prod = _
  rw [List.map_append, List.prod_append, List.map_replicate, Fin.snoc_last,
    List.prod_replicate, one_pow, mul_one]
  simp only [labels, List.map_flatten, List.prod_flatten,
    ← List.ofFn_comp', List.map_replicate, Fin.snoc_castSucc,
    List.prod_replicate, List.prod_ofFn]

/-- A polynomial with public degree at most d and private degree at most two has
coefficients on padded public tuples and ordered padded private pairs. The same
coefficients work for all variable values. This is the algebraic representation
underlying [GJLS21, Section 9, printed p.58].

**Proof sketch.** Apply the padded-monomial representation separately to the public
and private exponents of each supported monomial. Choose one public tuple and one
private ordered pair for each support element. Collect coefficients by those finite
fibres. Expand evaluation with the published monomial-sum formula, interchange the
finite sums, and select the unique assigned tuple and pair in each monomial term. -/
theorem exists_quadratic_expansion {R : Type*} [CommSemiring R] (l n d : ℕ)
    (P : MvPolynomial (Fin l ⊕ Fin n) R)
    (hdeg : ∀ s : (Fin l ⊕ Fin n) →₀ ℕ, MvPolynomial.coeff s P ≠ 0 →
      (∑ i : Fin l, s (Sum.inl i)) ≤ d ∧ (∑ j : Fin n, s (Sum.inr j)) ≤ 2) :
    ∃ C : (Fin (n + 1) × Fin (n + 1)) → (Fin d → Fin (l + 1)) → R,
      ∀ (x : Fin l → R) (y : Fin n → R),
        MvPolynomial.eval (Sum.elim x y) P =
          ∑ ij : Fin (n + 1) × Fin (n + 1), ∑ tau : Fin d → Fin (l + 1),
            C ij tau * (∏ i : Fin d, Fin.snoc (α := fun _ => R) x 1 (tau i)) *
              Fin.snoc (α := fun _ => R) y 1 ij.1 * Fin.snoc (α := fun _ => R) y 1 ij.2 :=
  by
    classical
    choose publicTuple hpub using fun s : P.support =>
      exists_padded_tuple (R := R) l d (fun i => s.val (Sum.inl i))
        (hdeg s.val (MvPolynomial.mem_support_iff.mp s.property)).1
    choose privateTuple hpriv using fun s : P.support =>
      exists_padded_tuple (R := R) n 2 (fun i => s.val (Sum.inr i))
        (hdeg s.val (MvPolynomial.mem_support_iff.mp s.property)).2
    let privatePair (s : P.support) : Fin (n + 1) × Fin (n + 1) :=
      (privateTuple s 0, privateTuple s 1)
    let C : (Fin (n + 1) × Fin (n + 1)) → (Fin d → Fin (l + 1)) → R :=
      fun ij tau => ∑ s : P.support,
        if privatePair s = ij ∧ publicTuple s = tau then P.coeff s.val else 0
    refine ⟨C, fun x y => ?_⟩
    have hEval : MvPolynomial.eval (Sum.elim x y) P =
        ∑ s : P.support, P.coeff s.val *
          (∏ i : Fin d, Fin.snoc (α := fun _ => R) x 1 (publicTuple s i)) *
          Fin.snoc (α := fun _ => R) y 1 (privatePair s).1 *
          Fin.snoc (α := fun _ => R) y 1 (privatePair s).2 := ?_
    swap
    · rw [MvPolynomial.eval_eq', ← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← hpub s x, ← hpriv s y, Fin.prod_univ_two]
      simp only [privatePair, mul_assoc]
    rw [hEval]
    symm
    simp only [C, Finset.sum_mul]
    simp_rw [Finset.sum_comm
      (s := (Finset.univ : Finset (Fin d → Fin (l + 1))))
      (t := (Finset.univ : Finset P.support))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq]

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PolynomialTensorAlgebra
