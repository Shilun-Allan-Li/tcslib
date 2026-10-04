import Mathlib.Algebra.Order.Floor.Ring
import TCSlib.BooleanAnalysis.KKL
import TCSlib.BooleanAnalysis.ThresholdFunctions.AffineKhintchine
import TCSlib.BooleanAnalysis.ThresholdFunctions.LowDegreeNorm
import TCSlib.BooleanAnalysis.ThresholdFunctions.SparseSampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier theory of threshold functions

This file states the Chapter 5 results relating polynomial threshold representations to low-degree
Fourier coefficients, Fourier weight, and polynomial sparsity.

## Main definitions

The representation and Fourier-weight definitions are imported from `ThresholdFunctions.Basic`.

## Main results

* `chow_theorem`: an LTF is determined by its degree-zero and degree-one coefficients.
* `ptf_chow_theorem`: a degree-`k` PTF is determined by coefficients through degree `k`.
* `ptf_low_degree_weight`: a degree-`k` PTF has low-degree weight at least `exp (-2k)`.
* `ptf_support_fourier_mass`: a PTF support carries Fourier one-mass at least one.
* `sparse_polynomial_approximation`: small spectral one-norm gives a sparse approximation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapter 5.
* [Cho61] C.-K. Chow, On the characterization of threshold functions, 1961.
* [Bru90] J. Bruck, Harmonic analysis of polynomial threshold functions, 1990.
* [GL94] C. Gotsman and N. Linial, Spectral properties of threshold functions, 1994.
* [BS92] J. Bruck and R. Smolensky, Polynomial threshold functions and sparse polynomials, 1992.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

open MultilinearPolynomial

variable {n k : ℕ}

/-! ## Chow-type uniqueness theorems -/

/-- A degree-`k` polynomial threshold function is uniquely determined among all `±1`-valued
functions by its Fourier coefficients through degree `k`. [OD14, Thm. 5.8; Bru90]
The hypothesis `hfb` is automatic for threshold functions; it is kept to match the source.

**Proof sketch.** The difference of the two correlations with a representing polynomial is
nonnegative pointwise. Expanding in Walsh characters shows its expectation is zero, so the
functions agree wherever the polynomial is nonzero. At its zeros the threshold function is one,
so it dominates the other function everywhere. Equality of the constant coefficients, hence of
the means, forces pointwise equality also at these zeros. -/
theorem ptf_chow_theorem {f g : BooleanFunc n} (hf : IsPolynomialThreshold f k)
    (hfb : isPmOne f) (hgb : isPmOne g)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ k → fourierCoeff g S = fourierCoeff f S) :
    g = f := by
  obtain ⟨p, hdeg, hrep⟩ := hf
  have hsign (x : BoolCube n) : f x = thresholdSign (p.eval x) := congrFun hrep.symm x
  -- Both functions have the same correlation with the representing polynomial.
  have hinner : innerProduct p.eval f = innerProduct p.eval g := by
    rw [p.innerProduct_eval, p.innerProduct_eval]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    by_cases hS : S.card ≤ k
    · rw [hcoeff S hS]
    · rw [hdeg S (Nat.lt_of_not_ge hS), zero_mul, zero_mul]
  -- The nonnegative correlation difference therefore vanishes at every point.
  have hnonneg (x : BoolCube n) : 0 ≤ (f x - g x) * p.eval x := by
    rw [hsign]
    unfold thresholdSign
    rcases hgb x with hg | hg <;> rw [hg] <;> split_ifs <;> nlinarith
  have hzero := eq_zero_of_expect_eq_zero hnonneg (by
    simp only [sub_mul, expect_sub]
    simpa [innerProduct, mul_comm] using sub_eq_zero.mpr hinner)
  -- Hence `g ≤ f`: they agree off the zero set of `p`, where `f = 1`.
  have hle (x : BoolCube n) : g x ≤ f x := by
    rcases mul_eq_zero.mp (congrFun hzero x) with heq | hp
    · exact (sub_eq_zero.mp heq).ge
    · rw [hsign, hp, thresholdSign_of_nonneg le_rfl]
      rcases hgb x with hg | hg <;> simp [hg]
  -- Equality of the means removes any remaining disagreement.
  have hmean : expect g = expect f := by
    simpa only [fourierCoeff_empty] using hcoeff ∅ (by simp)
  have hdiff := eq_zero_of_expect_eq_zero (fun x ↦ sub_nonneg.mpr (hle x))
    (by rw [expect_sub, hmean, sub_self])
  funext x
  exact (sub_eq_zero.mp (congrFun hdiff x)).symm

/-- A linear threshold function is uniquely determined among all `±1`-valued functions by its
Fourier coefficients in degrees zero and one. [OD14, Thm. 5.1]

**Proof sketch.** Apply polynomial-threshold uniqueness with degree bound one. -/
theorem chow_theorem {f g : BooleanFunc n} (hf : IsLinearThreshold f) (hfb : isPmOne f)
    (hgb : isPmOne g)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ 1 → fourierCoeff g S = fourierCoeff f S) :
    g = f :=
  ptf_chow_theorem hf hfb hgb hcoeff

/-! ## Low-degree approximation and weight -/

/-- A Bernoulli-type estimate: if `0 < δ ≤ 1/2` and `δ m > 1`, then `(1 - 2δ)^m ≤ 1/3`.

**Proof sketch.** Bernoulli's inequality gives `1 + 2δm ≤ (1 + 2δ)^m`, so
`(1 - 2δ)^m (1 + 2δm) ≤ (1 - 4δ²)^m ≤ 1`, and `1 + 2δm > 3`. -/
private lemma one_sub_two_mul_pow_le_third {δ : ℝ} (hδ' : δ ≤ 1 / 2) {m : ℕ}
    (hdm : 1 < δ * m) : (1 - 2 * δ) ^ m ≤ 1 / 3 := by
  have hρ : 0 ≤ 1 - 2 * δ := by linarith
  have hδ : 0 < δ := by
    by_contra h
    nlinarith [m.cast_nonneg (α := ℝ)]
  have hbern := one_add_mul_le_pow (show -2 ≤ 2 * δ by linarith) m
  have hprod : (1 - 2 * δ) ^ m * (1 + 2 * δ) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg hρ (by linarith)) (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left hbern (pow_nonneg hρ m), pow_nonneg hρ m]

/-- Every Boolean function is close to a PTF whose degree is the reciprocal noise scale.
[OD14, Prop. 5.6]

**Proof sketch.** Truncate the Fourier expansion above degree `⌊1/δ⌋`. The Fourier tail is bounded
by three times the noise sensitivity, and taking the sign of the truncation can only decrease the
pointwise disagreement with the original Boolean function. -/
theorem close_to_low_degree_ptf (f : BooleanFunc n) (hf : isPmOne f) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ g : BooleanFunc n,
      IsPolynomialThreshold g (Nat.floor δ⁻¹) ∧
        IsClose f g (3 * noiseSensitivity δ f) := by
  classical
  let d := Nat.floor δ⁻¹
  let p : MultilinearPolynomial n := fun S ↦ if S.card ≤ d then fourierCoeff f S else 0
  have heval : p.eval = KKL.lowDegreePart f d := by
    funext x
    simp [MultilinearPolynomial.eval, KKL.lowDegreePart, p, ite_mul]
  refine ⟨p.threshold, ⟨p, ?_, rfl⟩, ?_⟩
  · intro S hS
    exact if_neg (Nat.not_le.mpr hS)
  have hρ : 0 ≤ 1 - 2 * δ := by linarith
  have hρ' : 1 - 2 * δ ≤ 1 := by linarith
  -- Bernoulli's inequality bounds the noise multiplier on the discarded levels.
  have hdecay (m : ℕ) (hm : d < m) : (1 - 2 * δ) ^ m ≤ (1 : ℝ) / 3 :=
    one_sub_two_mul_pow_le_third hδ' (by
      calc 1 = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
        _ < δ * m := mul_lt_mul_of_pos_left (Nat.lt_of_floor_lt hm) hδ)
  have htail : KKL.l2DistSq f (KKL.lowDegreePart f d) ≤
      3 * noiseSensitivity δ f := by
    rw [KKL.lowDegree_l2_error]
    calc
      (∑ S : Finset (Fin n), if d < S.card then fourierCoeff f S ^ 2 else 0) ≤
          ∑ S : Finset (Fin n),
            (3 / 2 : ℝ) * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) := by
        refine Finset.sum_le_sum fun S _ ↦ ?_
        split_ifs with hS
        · have h := mul_le_mul_of_nonneg_right (hdecay S.card hS)
            (sq_nonneg (fourierCoeff f S))
          nlinarith
        · exact mul_nonneg (by norm_num)
            (mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hρ hρ')) (sq_nonneg _))
      _ = 3 * noiseSensitivity δ f := by
        rw [← Finset.mul_sum]
        simp_rw [sub_mul, one_mul]
        rw [Finset.sum_sub_distrib, parseval_pm_one f hf]
        simp only [noiseSensitivity, noiseStability, stability_formula]
        ring
  -- Taking the sign costs at most the squared approximation error at each point.
  unfold IsClose disagreementProbability
  calc
    expect (fun x ↦ if f x = p.threshold x then 0 else 1) ≤
        KKL.l2DistSq f p.eval := by
      refine expect_mono fun x ↦ ?_
      by_cases hx : f x = p.threshold x
      · simp [hx, sq_nonneg]
      · simp only [if_neg hx]
        change f x ≠ thresholdSign (p.eval x) at hx
        unfold thresholdSign at hx
        rcases hf x with hf | hf <;> rw [hf] at hx ⊢ <;>
          split_ifs at hx <;> norm_num at hx <;> nlinarith [sq_nonneg (p.eval x)]
    _ ≤ 3 * noiseSensitivity δ f := heval ▸ htail

/-- The correlation step of the low-degree weight bounds: if `p` has degree at most `k` and
represents `f`, then `‖p‖₁² ≤ ‖p‖₂² · W^{≤k}[f]`. [OD14, proofs of Thm. 5.2 and Thm. 5.9]

**Proof sketch.** The `L¹` norm of `p` is its correlation with `f`. By Plancherel and the degree
bound this is `∑_S p(S) f̂^{≤k}(S)`; apply Cauchy-Schwarz. -/
private lemma sq_expect_abs_le_mul_fourierWeightUpTo {f : BooleanFunc n}
    {p : MultilinearPolynomial n} (hdeg : p.HasDegreeAtMost k)
    (hrep : IsPolynomialThresholdRepresentation f p) :
    expect (fun x ↦ |p.eval x|) ^ 2 ≤ (∑ S : Finset (Fin n), p S ^ 2) * fourierWeightUpTo k f := by
  let q : Finset (Fin n) → ℝ := fun S ↦ if S.card ≤ k then fourierCoeff f S else 0
  have hcorr : expect (fun x ↦ |p.eval x|) = ∑ S : Finset (Fin n), p S * q S := by
    rw [p.expect_abs_eval_eq_innerProduct hrep, p.innerProduct_eval]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    by_cases hS : S.card ≤ k
    · simp [q, hS]
    · simp [q, hS, hdeg S (Nat.lt_of_not_ge hS)]
  rw [hcorr]
  convert Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p q using 2
  simp [q, fourierWeightUpTo]

/-- The threshold of the zero polynomial is the constant function `1`, whose Fourier weight
lies entirely on the empty set. -/
private lemma fourierWeightUpTo_of_rep_zero {f : BooleanFunc n}
    (hrep : IsPolynomialThresholdRepresentation f 0) : fourierWeightUpTo k f = 1 := by
  have hfchi : f = chiS (∅ : Finset (Fin n)) := by
    rw [← hrep]
    funext x
    simp [MultilinearPolynomial.threshold, MultilinearPolynomial.eval, chiS]
  have hcoeff (S : Finset (Fin n)) : fourierCoeff f S = if S = ∅ then 1 else 0 := by
    rw [hfchi]
    simpa only [fourierCoeff, eq_comm] using fourier_coeff_chi ∅ S
  simp only [fourierWeightUpTo, hcoeff]
  rw [Finset.sum_eq_single ∅ (fun S _ hS ↦ by simp [hS]) (by simp)]
  simp

/-- If every polynomial of degree at most `k` satisfies `c ‖p‖₂² ≤ ‖p‖₁²` for a constant
`c ≤ 1`, then every degree-`k` PTF has Fourier weight at least `c` through degree `k`.
[OD14, proofs of Thm. 5.2 and Thm. 5.9] -/
private lemma le_fourierWeightUpTo_of_l1_l2 {f : BooleanFunc n} {c : ℝ} (hc : c ≤ 1)
    (hf : IsPolynomialThreshold f k)
    (hnorm : ∀ p : MultilinearPolynomial n, p.HasDegreeAtMost k →
      c * ∑ S : Finset (Fin n), p S ^ 2 ≤ expect (fun x ↦ |p.eval x|) ^ 2) :
    c ≤ fourierWeightUpTo k f := by
  obtain ⟨p, hdeg, hrep⟩ := hf
  by_cases hp0 : p = 0
  · subst hp0
    rw [fourierWeightUpTo_of_rep_zero hrep]
    exact hc
  · have h := (hnorm p hdeg).trans (sq_expect_abs_le_mul_fourierWeightUpTo hdeg hrep)
    rw [mul_comm] at h
    exact le_of_mul_le_mul_left h (sum_sq_pos hp0)

/-- Every linear threshold function has at least one half of its Fourier weight in degrees zero and
one. [OD14, Thm. 5.2; GL94]
The hypothesis `hfb` is automatic for threshold functions; it is kept to match the source.

**Proof sketch.** Correlate the function with a normalized affine separator, project the correlation
onto degrees zero and one, and apply Cauchy-Schwarz. For the absolute value of the affine
separator, compare its variance to its total influence and degree-one weight. The absolute value
map does not increase influence; its degree-one weight is bounded by the squared constant
coefficient via the antipodal odd part. This sharp Khintchine bound gives the factor `1/2`. -/
theorem ltf_low_degree_weight {f : BooleanFunc n} (hf : IsLinearThreshold f)
    (hfb : isPmOne f) :
    1 / 2 ≤ fourierWeightUpTo 1 f :=
  le_fourierWeightUpTo_of_l1_l2 (by norm_num) hf fun p hp ↦ by
    linarith [affine_khintchine_sq p hp]

/-- A degree-`k` polynomial threshold function has Fourier weight at least `exp (-2k)` through
degree `k`. [OD14, Thm. 5.9; GL94]
The hypothesis `hfb` is automatic for threshold functions; it is kept to match the source.

**Proof sketch.** Correlate `f` with a degree-`k` representing polynomial and use Cauchy-Schwarz on
the low-degree projection. The hypercontractive estimate `‖p‖₂ ≤ exp(k) ‖p‖₁` supplies the stated
exponential lower bound. -/
theorem ptf_low_degree_weight {f : BooleanFunc n} (hf : IsPolynomialThreshold f k)
    (hfb : isPmOne f) :
    Real.exp (-2 * (k : ℝ)) ≤ fourierWeightUpTo k f :=
  le_fourierWeightUpTo_of_l1_l2 (Real.exp_le_one_iff.mpr (by linarith [k.cast_nonneg (α := ℝ)])) hf
    fun p hp ↦ low_degree_l1_l2_sq p hp

/-! ## Sparse threshold representations -/

/-- The support of a nonzero representing polynomial carries Fourier one-mass at least one.
[OD14, Thm. 5.10; Bru90] The nonzero hypothesis excludes the zero polynomial, whose threshold
is the constant one function under our sign convention.

**Proof sketch.** Let `A` be the expected absolute value of the polynomial. Each coefficient
has absolute value at most `A`, since Walsh characters have absolute value one. Nonzeroness
therefore gives `A > 0`. Correlation with the represented function equals `A`; Plancherel and
the coefficient bound make it at most `A` times the Fourier one-mass on the support. Cancel `A`. -/
theorem ptf_support_fourier_mass_of_ne_zero {f : BooleanFunc n}
    (p : MultilinearPolynomial n) (F : Finset (Finset (Fin n))) (hp : p ≠ 0)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hsupport : ∀ S : Finset (Fin n), p S ≠ 0 → S ∈ F) :
    1 ≤ ∑ S ∈ F, |fourierCoeff f S| := by
  set A := expect (fun x ↦ |p.eval x|) with hAdef
  have hA : 0 < A := by
    obtain ⟨S, hS⟩ := Function.ne_iff.mp hp
    exact (abs_pos.mpr hS).trans_le (p.abs_coeff_le_expect_abs S)
  -- The correlation of `p` with `f` is `A`, and only monomials in `F` contribute.
  have hcorr : A = ∑ S ∈ F, p S * fourierCoeff f S := by
    rw [hAdef, p.expect_abs_eval_eq_innerProduct hrep, p.innerProduct_eval]
    refine (Finset.sum_subset (Finset.subset_univ F) fun S _ hS ↦ ?_).symm
    rw [not_ne_iff.mp (mt (hsupport S) hS), zero_mul]
  refine le_of_mul_le_mul_left ?_ hA
  calc A * 1 = ∑ S ∈ F, p S * fourierCoeff f S := by rw [mul_one, hcorr]
    _ ≤ ∑ S ∈ F, |p S| * |fourierCoeff f S| :=
      Finset.sum_le_sum fun S _ ↦ (le_abs_self _).trans_eq (abs_mul _ _)
    _ ≤ ∑ S ∈ F, A * |fourierCoeff f S| :=
      Finset.sum_le_sum fun S _ ↦
        mul_le_mul_of_nonneg_right (p.abs_coeff_le_expect_abs S) (abs_nonneg _)
    _ = A * ∑ S ∈ F, |fourierCoeff f S| := by rw [← Finset.mul_sum]

/-- If a PTF is represented using only monomials from `F`, the absolute Fourier mass of `f` on `F`
is at least one. [OD14, Thm. 5.10; Bru90]
The hypothesis `hfb` is automatic for threshold functions; it is kept to match the source.

**Proof sketch.** Form the polynomial whose coefficients on `F` are the corresponding Fourier
coefficients of `f`. Plancherel identifies its correlation with the representing polynomial.
Hölder's inequality and `‖p̂‖∞ ≤ ‖p‖₁` then force Fourier one-mass at least one. -/
theorem ptf_support_fourier_mass {f : BooleanFunc n} (hfb : isPmOne f)
    (p : MultilinearPolynomial n) (hp : p ≠ 0) (F : Finset (Finset (Fin n)))
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hsupport : ∀ S : Finset (Fin n), p S ≠ 0 → S ∈ F) :
    1 ≤ ∑ S ∈ F, |fourierCoeff f S| :=
  ptf_support_fourier_mass_of_ne_zero p F hp hrep hsupport

/-- Inner product mod two is a bent function: every Fourier coefficient of `IP₂ₙ` has absolute
value `2⁻ⁿ`. [OD14, §5.1, proof of Cor. 5.11]

**Proof sketch.** Both `IP₂ₙ` and a Walsh character factor over the `n` coordinate pairs
`(xᵢ, xₙ₊ᵢ)`, so the correlation sum is a product of `n` sums over `Bool × Bool`. Each of these
four-term sums has absolute value `2`, and the normalization contributes `2⁻²ⁿ`. -/
lemma abs_fourierCoeff_innerProductModTwo (S : Finset (Fin (n + n))) :
    |fourierCoeff (innerProductModTwo n) S| = (2 : ℝ)⁻¹ ^ n := by
  classical
  let g : Fin n → Bool × Bool → ℝ := fun i ab ↦
    (if ab.1 && ab.2 then -1 else 1) *
    (if Fin.castAdd n i ∈ S then boolToSign ab.1 else 1) *
    (if Fin.natAdd n i ∈ S then boolToSign ab.2 else 1)
  let e : (Fin n → Bool × Bool) ≃ BoolCube (n + n) :=
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ Bool) (fun _ ↦ Bool)).trans
      (Fin.appendEquiv n n)
  have hchar (x : BoolCube (n + n)) : chiS S x =
      (∏ i : Fin n, if Fin.castAdd n i ∈ S then boolToSign (x (Fin.castAdd n i)) else 1) *
      (∏ i : Fin n, if Fin.natAdd n i ∈ S then boolToSign (x (Fin.natAdd n i)) else 1) := by
    calc
      chiS S x = ∏ i : Fin (n + n), if i ∈ S then boolToSign (x i) else 1 := by
        rw [← Finset.prod_filter]
        simp [chiS]
      _ = _ := Fin.prod_univ_add _
  have hterm (x : BoolCube (n + n)) :
      innerProductModTwo n x * chiS S x =
        ∏ i : Fin n, g i (x (Fin.castAdd n i), x (Fin.natAdd n i)) := by
    rw [hchar]
    dsimp [innerProductModTwo, g]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp only [mul_assoc]
  have hsum :
      (∑ x : BoolCube (n + n), innerProductModTwo n x * chiS S x) =
        ∏ i : Fin n, ∑ ab : Bool × Bool, g i ab := by
    calc
      _ = ∑ u : Fin n → Bool × Bool, ∏ i : Fin n, g i (u i) := by
        symm
        apply Fintype.sum_equiv e
        intro u
        rw [hterm]
        apply Finset.prod_congr rfl
        intro i hi
        change g i (u i) = g i
          (Fin.append (fun j ↦ (u j).1) (fun j ↦ (u j).2) (Fin.castAdd n i),
           Fin.append (fun j ↦ (u j).1) (fun j ↦ (u j).2) (Fin.natAdd n i))
        have hr : Fin.append (fun j ↦ (u j).1) (fun j ↦ (u j).2)
            (Fin.natAdd n i) = (u i).2 := by
          simpa using Fin.append_right (fun j ↦ (u j).1) (fun j ↦ (u j).2) i
        rw [Fin.append_left, hr]
      _ = _ := by rw [Fintype.prod_sum]
  have hlocal (i : Fin n) : |∑ ab : Bool × Bool, g i ab| = 2 := by
    dsimp only [g]
    by_cases hL : Fin.castAdd n i ∈ S <;>
      by_cases hR : Fin.natAdd n i ∈ S <;>
      simp only [hL, hR, ite_true, ite_false] <;>
      norm_num [Fintype.sum_prod_type, boolToSign]
  calc
    |fourierCoeff (innerProductModTwo n) S| = ((2 : ℝ)⁻¹) ^ (n + n) * 2 ^ n := by
      rw [fourierCoeff, innerProduct, expect, hsum, abs_mul]
      simp [uniformWeight, Finset.abs_prod, hlocal]
    _ = ((2 : ℝ)⁻¹) ^ n := by
      rw [pow_add, mul_assoc, ← mul_pow]
      norm_num

/-- Every polynomial threshold representation of the inner-product-mod-two function on `2n` bits
has sparsity at least `2ⁿ`. [OD14, Cor. 5.11]

**Proof sketch.** Every Fourier coefficient of inner product mod two has magnitude `2⁻ⁿ`. Apply
`ptf_support_fourier_mass` to the support of the representing polynomial and rearrange. -/
theorem innerProductModTwo_ptf_sparsity (p : MultilinearPolynomial (n + n))
    (hrep : IsPolynomialThresholdRepresentation (innerProductModTwo n) p) (hp : p ≠ 0) :
    2 ^ n ≤ p.sparsity := by
  have hmass := ptf_support_fourier_mass_of_ne_zero p p.support hp hrep
    fun S hS ↦ by simp [MultilinearPolynomial.support, hS]
  simp only [abs_fourierCoeff_innerProductModTwo, Finset.sum_const, nsmul_eq_mul, inv_pow,
    ← div_eq_mul_inv] at hmass
  rw [le_div_iff₀ (by positivity), one_mul] at hmass
  exact_mod_cast hmass

/-- A nonzero function of positive arity with small spectral one-norm has a uniformly close sparse
multilinear polynomial approximation. The positive-arity hypothesis makes explicit the source's
standing convention that Boolean functions have at least one input. [OD14, Thm. 5.12; BS92]

**Proof sketch.** Independently sample `s` Fourier characters with probabilities proportional to
the magnitudes of their coefficients and average their signed characters. A Chernoff bound controls
the error at each cube point; a union bound over the `2ⁿ` points yields one simultaneous choice.
Collect repeated sampled characters into polynomial coefficients. Its support lies in the sampled
set, and finiteness of the cube turns pointwise strict error into a strict supremum bound. -/
theorem sparse_polynomial_approximation (f : BooleanFunc n) (hn : 0 < n) (hf : f ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (s : ℕ) (hs : 4 * n * spectralOneNorm f ^ 2 / δ ^ 2 ≤ s) :
    ∃ q : MultilinearPolynomial n,
      q.sparsity ≤ s ∧ supNorm (fun x ↦ f x - q.eval x) < δ := by
  classical
  -- Concentration and a union bound supply one sample that works on the whole cube.
  obtain ⟨T, hT⟩ := sparse_signed_sample f hn hf hδ s hs
  let a : Fin s → ℝ := fun j ↦
    spectralOneNorm f / (s : ℝ) * thresholdSign (fourierCoeff f (T j))
  let q : MultilinearPolynomial n :=
    fun S ↦ ∑ j : Fin s, if T j = S then a j else 0
  -- Only sampled characters can occur in the polynomial's support.
  have hsub : q.support ⊆ Finset.univ.image T := by
    intro S hS
    by_contra hnot
    refine (Finset.mem_filter.mp hS).2 (Finset.sum_eq_zero fun j _ ↦ if_neg fun h ↦ hnot ?_)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩
  have hsparse : q.sparsity ≤ s :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  -- Exchanging the two finite sums identifies evaluation with the sampled average.
  have heval (x : BoolCube n) : q.eval x = ∑ j : Fin s, a j * chiS (T j) x := by
    simp only [MultilinearPolynomial.eval, q, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp
  refine ⟨q, hsparse, ?_⟩
  unfold supNorm
  rw [Set.Finite.csSup_lt_iff (Set.finite_range _) (Set.range_nonempty _)]
  rintro y ⟨x, rfl⟩
  simpa only [heval, a] using hT x

/-- Every positive-arity `±1`-valued Boolean function has a PTF representation of sparsity at most
`⌈4n ‖f̂‖₁²⌉` and is a majority of that many parities or negated parities. The positive-arity
hypothesis makes explicit the source's standing convention. [OD14, Cor. 5.13; BS92]

**Proof sketch.** Apply `sparse_polynomial_approximation` with error one. Strict approximation to a
`±1`-valued function preserves its sign, yielding a sparse PTF representation. The signed sample
from `sparse_signed_sample` has exactly `s` terms; its positive scaling factor does not affect its
sign, so the unscaled sum is a majority of signed parities. -/
theorem exists_sparse_ptf_representation (f : BooleanFunc n) (hn : 0 < n) (hf : isPmOne f) :
    let s := Nat.ceil (4 * n * spectralOneNorm f ^ 2)
    (∃ p : MultilinearPolynomial n,
      IsPolynomialThresholdRepresentation f p ∧ p.sparsity ≤ s) ∧
      IsMajorityOfSignedParities f s := by
  intro s
  have hfne : f ≠ 0 := fun h0 ↦ by
    rcases hf (fun _ ↦ false) with h | h <;> simp [h0] at h
  have hL : 0 < spectralOneNorm f := spectralOneNorm_pos hfne
  have hspos : 0 < s := Nat.ceil_pos.mpr (by positivity)
  have hsbound : 4 * n * spectralOneNorm f ^ 2 / (1 : ℝ) ^ 2 ≤ (s : ℝ) := by
    simpa using Nat.le_ceil (4 * (n : ℝ) * spectralOneNorm f ^ 2)
  -- A sparse polynomial within uniform distance one of `f` represents it.
  obtain ⟨q, hsp, hqnorm⟩ := sparse_polynomial_approximation f hn hfne one_pos s hsbound
  have hrep : IsPolynomialThresholdRepresentation f q := by
    unfold supNorm at hqnorm
    rw [Set.Finite.csSup_lt_iff (Set.finite_range _) (Set.range_nonempty _)] at hqnorm
    funext x
    exact thresholdSign_eq_of_abs_sub_lt_one (hf x) (hqnorm _ ⟨x, rfl⟩)
  -- The signed sample itself, with its positive scaling removed, is a majority of parities.
  obtain ⟨T, hT⟩ := sparse_signed_sample f hn hfne one_pos s hsbound
  have hc : 0 < spectralOneNorm f / (s : ℝ) := div_pos hL (by exact_mod_cast hspos)
  refine ⟨⟨q, hrep, hsp⟩, T, fun j ↦ thresholdSign (fourierCoeff f (T j)),
    fun j ↦ thresholdSign_pm_one _, funext fun x ↦ ?_⟩
  have hsum : (∑ j : Fin s,
      (spectralOneNorm f / (s : ℝ) * thresholdSign (fourierCoeff f (T j))) * chiS (T j) x) =
      spectralOneNorm f / (s : ℝ) *
        ∑ j : Fin s, thresholdSign (fourierCoeff f (T j)) * chiS (T j) x := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [← thresholdSign_mul_of_pos hc, ← hsum]
  exact (thresholdSign_eq_of_abs_sub_lt_one (hf x) (hT x)).symm

end ThresholdFunctions
end BooleanAnalysis
