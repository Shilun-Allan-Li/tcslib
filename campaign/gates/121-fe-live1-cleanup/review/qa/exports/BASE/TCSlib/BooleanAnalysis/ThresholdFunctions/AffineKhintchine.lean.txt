import TCSlib.BooleanAnalysis.ThresholdFunctions.BitFlipSets
import TCSlib.BooleanAnalysis.ThresholdFunctions.Polynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp affine Khintchine inequality on the Boolean cube

A degree-one Walsh polynomial has squared Fourier norm at most twice the square of its expected
absolute value. This sharp affine form is used to prove the degree-one Fourier weight bound for
linear threshold functions.

## Main definitions

No new definitions are exported.

## Main results

* `affine_khintchine_sq`: the sharp degree-one `L¹`–`L²` inequality.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Exercises 2.55 and 5.5.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

open MultilinearPolynomial

variable {n : ℕ}

/-- Taking absolute values cannot increase the quadratic influence of one coordinate. -/
private lemma influence_abs_le (h : BooleanFunc n) (i : Fin n) :
    influence i (fun x ↦ |h x|) ≤ influence i h := by
  refine expect_mono fun x ↦ ?_
  gcongr ?_ / 4
  exact sq_le_sq.mpr (by simpa using abs_abs_sub_abs_le_abs_sub (h x) (h (flipBit x i)))

/-- The nonconstant Fourier weight is controlled by total influence, allowing degree one an
additional unit of weight. This is a degree-sensitive Poincaré inequality. -/
private lemma spectral_inequality (g : BooleanFunc n) :
    2 * (innerProduct g g - (expect g) ^ 2) ≤ totalInfluence g + weightLevel 1 g := by
  classical
  rw [parseval, totalInfluence_eq_sum_sq_deg, ← fourierCoeff_empty, weightLevel,
    show fourierCoeff g ∅ ^ 2 =
      ∑ S : Finset (Fin n), if S = ∅ then fourierCoeff g S ^ 2 else 0 by simp,
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ ↦ ?_
  rcases Nat.lt_or_ge S.card 2 with hS | hS
  · interval_cases h : S.card
    · simp [Finset.card_eq_zero.mp h]
    · simp [Finset.card_ne_zero.mp (by omega : S.card ≠ 0) |>.ne_empty]
      nlinarith [sq_nonneg (fourierCoeff g S)]
  · have hS0 : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega))
    have hcard : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    simp only [hS0, if_false, sub_zero, show S.card ≠ 1 by omega, add_zero]
    nlinarith [sq_nonneg (fourierCoeff g S)]

/-- The degree-one Fourier weight is bounded by the squared size of the odd part under the
antipodal map. The odd part has the same singleton Fourier coefficients as the original function.

**Proof sketch.** Let `u(x) = (g(x) - g(-x))/2` be the odd part of `g`. Negating all inputs
multiplies each Fourier coefficient of degree one by `-1`, so `u` and `g` have the same singleton
coefficients. By Parseval the degree-one weight of `g` is at most `E[u²] ≤ a²`. -/
private lemma weightLevel1_antipode_le (g : BooleanFunc n) (a : ℝ)
    (hbound : ∀ x : BoolCube n, |g x - g (fun i ↦ !x i)| ≤ 2 * |a|) :
    weightLevel 1 g ≤ a ^ 2 := by
  let u : BooleanFunc n := fun x ↦ (g x - g (fun i ↦ !x i)) / 2
  -- The odd part `u` has the same degree-one coefficients as `g`.
  have hcoeff (S : Finset (Fin n)) (hS : S.card = 1) : fourierCoeff u S = fourierCoeff g S := by
    have hflip := fourierCoeff_comp_flipSet g Finset.univ S
    simp only [flipSet_univ, Finset.inter_univ, hS, pow_one] at hflip
    have hu : (fun x ↦ u x * chiS S x) =
        fun x ↦ 2⁻¹ * (g x * chiS S x) + (-2⁻¹) * (g (fun i ↦ !x i) * chiS S x) := by
      funext x; ring
    simp only [fourierCoeff, innerProduct] at hflip ⊢
    rw [hu, expect_add, expect_const_mul, expect_const_mul, hflip]
    ring
  calc weightLevel 1 g ≤ innerProduct u u := by
        rw [parseval, weightLevel]
        refine Finset.sum_le_sum fun S _ ↦ ?_
        split_ifs with h1
        · rw [hcoeff S h1]
        · exact sq_nonneg _
    _ ≤ expect (fun _ ↦ a ^ 2) := expect_mono fun x ↦ by
        rw [← sq, sq_le_sq, abs_div, abs_two]
        linarith [hbound x]
    _ = a ^ 2 := expect_const _

/-- The values of a degree-one polynomial at opposite cube points sum to twice its
constant coefficient. -/
private lemma affine_sum_antipode (p : MultilinearPolynomial n) (hdeg : p.HasDegreeAtMost 1)
    (x : BoolCube n) :
    p.eval x + p.eval (fun i ↦ !x i) = 2 * p ∅ := by
  simp only [eval_of_degree_le_one hdeg, boolToSign_not, mul_neg, Finset.sum_neg_distrib]
  ring

/-- For a degree-one polynomial, its total influence is its nonconstant squared Fourier
norm. -/
private lemma affine_influence (p : MultilinearPolynomial n) (hdeg : p.HasDegreeAtMost 1) :
    totalInfluence p.eval + p ∅ ^ 2 = ∑ S : Finset (Fin n), p S ^ 2 := by
  rw [totalInfluence_eq_sum_sq_deg,
    show p ∅ ^ 2 = ∑ S : Finset (Fin n), if S = ∅ then p S ^ 2 else 0 by simp,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rcases Nat.lt_or_ge S.card 2 with hS | hS
  · interval_cases h : S.card
    · simp [Finset.card_eq_zero.mp h]
    · simp [Finset.card_ne_zero.mp (by omega : S.card ≠ 0) |>.ne_empty]
  · have hS0 : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega))
    simp [hS0, hdeg S (by omega)]

/-- A degree-one Walsh polynomial has expected absolute value at least its `L²` norm
divided by `√2`, stated without square roots. [OD14, Ex. 2.55 and Ex. 5.5]

**Proof sketch.** For the absolute value `g = |p|`, the degree-sensitive Poincaré inequality
bounds twice its variance by its total influence plus its degree-one Fourier weight. Taking
absolute values is 1-Lipschitz, so the influence of `g` is at most the nonconstant squared norm
of `p`. The odd part of `g` under antipodal input has magnitude at most the constant coefficient
of `p`, because the values of `p` at opposite points sum to twice that coefficient. Its
degree-one Fourier weight is therefore at most the square of the constant coefficient by Parseval.
Together these two terms sum to `‖p‖₂²`, yielding the sharp factor two. -/
theorem affine_khintchine_sq {n : ℕ} (p : MultilinearPolynomial n)
    (hdeg : p.HasDegreeAtMost 1) :
    (∑ S : Finset (Fin n), p S ^ 2) ≤
      2 * (expect (fun x ↦ |p.eval x|)) ^ 2 := by
  let g : BooleanFunc n := fun x ↦ |p.eval x|
  have hg2 : innerProduct g g = ∑ S : Finset (Fin n), p S ^ 2 := by
    rw [← p.innerProduct_eval_self]
    simp only [innerProduct, g, abs_mul_abs_self]
  -- Taking absolute values does not increase influences.
  have hIabs : totalInfluence g ≤ totalInfluence p.eval :=
    Finset.sum_le_sum fun i _ ↦ influence_abs_le p.eval i
  -- The odd part of `g` is bounded by the constant coefficient of `p`.
  have hW1 : weightLevel 1 g ≤ p ∅ ^ 2 := by
    refine weightLevel1_antipode_le g (p ∅) fun x ↦ ?_
    have h := abs_abs_sub_abs_le_abs_sub (p.eval x) (-p.eval (fun i ↦ !x i))
    rw [abs_neg, sub_neg_eq_add, affine_sum_antipode p hdeg x] at h
    simpa [g, abs_mul] using h
  have hspec := spectral_inequality g
  have hI := affine_influence p hdeg
  change (∑ S : Finset (Fin n), p S ^ 2) ≤ 2 * (expect g) ^ 2
  nlinarith

end ThresholdFunctions
end BooleanAnalysis
