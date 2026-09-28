import TCSlib.BooleanAnalysis.LMN.DecisionTreeFourier
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier analysis of multilinear polynomials

A multilinear polynomial is stored by its Walsh-basis coefficients, so its evaluation has exactly
these coefficients as Fourier coefficients. This file records the resulting Parseval and
correlation identities, which are used repeatedly in the Chapter 5 proofs about polynomial
threshold functions.

## Main definitions

No new definitions are exported.

## Main results

* `MultilinearPolynomial.fourierCoeff_eval`: the Fourier coefficients of `p.eval` are the
  coefficients of `p`.
* `MultilinearPolynomial.innerProduct_eval_self` and `MultilinearPolynomial.innerProduct_eval`:
  Parseval and Plancherel for polynomials.
* `MultilinearPolynomial.abs_coeff_le_expect_abs`: each coefficient is bounded by the `L¹` norm.
* `MultilinearPolynomial.expect_abs_eval_eq_innerProduct`: a threshold representation correlates
  with the represented function exactly in its `L¹` norm.
* `MultilinearPolynomial.eval_of_degree_le_one`: the explicit form of a degree-one polynomial.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §1.4 and Chapter 5.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions
namespace MultilinearPolynomial

variable {n : ℕ} (p : MultilinearPolynomial n)

/-- The Fourier coefficients of the evaluation of a multilinear polynomial are its coefficients
(uniqueness of the Fourier expansion). [OD14, §1.4] -/
@[simp]
lemma fourierCoeff_eval (S : Finset (Fin n)) : fourierCoeff p.eval S = p S :=
  DecisionTree.fourierCoeff_sum_chiS p S

/-- Parseval's identity for a multilinear polynomial: its squared `L²` norm is the sum of its
squared coefficients. [OD14, §1.4] -/
lemma innerProduct_eval_self : innerProduct p.eval p.eval = ∑ S : Finset (Fin n), p S ^ 2 := by
  simp [parseval]

/-- Parseval's identity for a multilinear polynomial, as a mean square. [OD14, §1.4] -/
lemma expect_eval_sq : expect (fun x ↦ p.eval x ^ 2) = ∑ S : Finset (Fin n), p S ^ 2 := by
  simpa [innerProduct, sq] using p.innerProduct_eval_self

/-- Plancherel's identity for a multilinear polynomial: its correlation with `u` is the
coefficient-weighted sum of the Fourier coefficients of `u`. [OD14, §1.4] -/
lemma innerProduct_eval (u : BooleanFunc n) :
    innerProduct p.eval u = ∑ S : Finset (Fin n), p S * fourierCoeff u S := by
  simp [plancherel]

/-- Every coefficient of a multilinear polynomial is bounded in absolute value by the `L¹` norm
of the polynomial, since Walsh characters have absolute value one. [OD14, §5.1, Thm. 5.10] -/
lemma abs_coeff_le_expect_abs (S : Finset (Fin n)) :
    |p S| ≤ expect (fun x ↦ |p.eval x|) := by
  rw [← p.fourierCoeff_eval S, fourierCoeff, innerProduct, expect_eq_fintypeExpect,
    expect_eq_fintypeExpect]
  refine (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun x _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    ((sq_le_one_iff_abs_le_one _).mp (chiS_sq_eq_one S x).le)

/-- A nonzero multilinear polynomial has positive sum of squared coefficients. -/
lemma sum_sq_pos {p : MultilinearPolynomial n} (hp : p ≠ 0) :
    0 < ∑ S : Finset (Fin n), p S ^ 2 := by
  obtain ⟨S, hS⟩ := Function.ne_iff.mp hp
  exact Finset.sum_pos' (fun S _ ↦ sq_nonneg (p S)) ⟨S, Finset.mem_univ S,
    (sq_nonneg _).lt_of_ne (pow_ne_zero 2 hS).symm⟩

/-- If `p` is a threshold representation of `f`, then the correlation of `p` with `f` equals the
`L¹` norm of `p`. [OD14, §5.1, proof of Thm. 5.2] -/
lemma expect_abs_eval_eq_innerProduct {f : BooleanFunc n}
    (hrep : IsPolynomialThresholdRepresentation f p) :
    expect (fun x ↦ |p.eval x|) = innerProduct p.eval f := by
  rw [← hrep]
  simp only [innerProduct, threshold, mul_thresholdSign_self]

/-- A multilinear polynomial of degree at most one is an affine form in the `±1` variables. -/
lemma eval_of_degree_le_one {p : MultilinearPolynomial n} (hp : p.HasDegreeAtMost 1)
    (x : BoolCube n) :
    p.eval x = p ∅ + ∑ i : Fin n, p {i} * boolToSign (x i) := by
  classical
  set T : Finset (Finset (Fin n)) :=
    insert ∅ (Finset.univ.image (fun i : Fin n ↦ ({i} : Finset (Fin n)))) with hT
  have hzero : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))), S ∉ T → p S * chiS S x = 0 := by
    intro S _ hS
    suffices hcard : 1 < S.card by rw [hp S hcard, zero_mul]
    by_contra hcard
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (not_lt.mp hcard) with h0 | h1
    · exact hS (by simp [hT, Finset.card_eq_zero.mp h0])
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      exact hS (by simp [hT])
  have hnot : (∅ : Finset (Fin n)) ∉
      Finset.univ.image (fun i : Fin n ↦ ({i} : Finset (Fin n))) := by
    simp [eq_comm]
  rw [MultilinearPolynomial.eval, ← Finset.sum_subset (Finset.subset_univ T) hzero, hT,
    Finset.sum_insert hnot,
    Finset.sum_image (fun i _ j _ h ↦ Finset.singleton_injective h)]
  simp

end MultilinearPolynomial
end ThresholdFunctions
end BooleanAnalysis
