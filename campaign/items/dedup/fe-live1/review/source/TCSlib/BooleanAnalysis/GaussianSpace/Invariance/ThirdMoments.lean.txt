/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Replacement
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Moments
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Third moments of hypercontractive multilinear polynomials

## Main definitions

The polynomial representation and hypercontractive input predicate are reused.

## Main results

* Third-order moment bounds for the coordinate replacement argument.
* `hypercontractive_radius_sq_le` and `hypercontractive_radius_le_five_sixths`:
  a standardized nonconstant input has a hypercontractive radius bounded away from one.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §9.2 and §11.6, Remark 11.66.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- Squared third norms of affine sections satisfy a product-law Minkowski bound.
This is the tensorization step in [OD14, Remark 11.66 (proof)].

**Proof sketch.** Integrate the scalar contraction in the first law. The triangle
inequality at exponent three halves separates the two squared background terms. -/
theorem affine_product_three_norm_sq
    (τ : Measure (ℝ × ℝ)) (ν : Measure ℝ) [SFinite ν] {ρ : ℝ}
    (hν : ∀ a b : ℝ,
      eLpNorm (fun x => a + b * x) 3 ν ^ (2 : ℝ) ≤
        ENNReal.ofReal (a ^ 2 + (b / ρ) ^ 2)) :
    eLpNorm (fun z : (ℝ × ℝ) × ℝ => z.1.1 + z.1.2 * z.2) 3 (τ.prod ν) ^ (2 : ℝ) ≤
      eLpNorm (fun z : ℝ × ℝ => z.1) 3 τ ^ (2 : ℝ) +
        eLpNorm (fun z : ℝ × ℝ => z.2 / ρ) 3 τ ^ (2 : ℝ) := by
  let A : ℝ × ℝ → ℝ≥0∞ := fun z => ‖z.1‖ₑ ^ (2 : ℝ)
  let B : ℝ × ℝ → ℝ≥0∞ := fun z => ‖z.2 / ρ‖ₑ ^ (2 : ℝ)
  have hsum (z : ℝ × ℝ) : ENNReal.ofReal (z.1 ^ 2 + (z.2 / ρ) ^ 2) = A z + B z := by
    rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    simp only [A, B, ENNReal.rpow_two, ← enorm_pow,
      Real.enorm_eq_ofReal (sq_nonneg _)]
  have hsection (z : ℝ × ℝ) :
      (∫⁻ x, ‖z.1 + z.2 * x‖ₑ ^ (3 : ℝ) ∂ν) ≤ (A z + B z) ^ (3 / 2 : ℝ) := by
    have h := ENNReal.rpow_le_rpow (hν z.1 z.2) (by norm_num : 0 ≤ (3 / 2 : ℝ))
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at h
    simp only [ENNReal.toReal_ofNat, ← ENNReal.rpow_mul] at h
    norm_num at h
    simpa only [hsum, ENNReal.rpow_ofNat] using h
  have hM := ENNReal.lintegral_Lp_add_le
    (μ := τ) (p := (3 / 2 : ℝ))
    (show AEMeasurable A τ by dsimp [A]; fun_prop)
    (show AEMeasurable B τ by dsimp [B]; fun_prop)
    (by norm_num)
  have hleft :
      eLpNorm (fun z : (ℝ × ℝ) × ℝ => z.1.1 + z.1.2 * z.2) 3 (τ.prod ν) ^ (2 : ℝ) ≤
        (∫⁻ z : ℝ × ℝ, (A z + B z) ^ (3 / 2 : ℝ) ∂τ) ^ (2 / 3 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
    rw [show (1 / (3 : ℝ)) * 2 = 2 / 3 by norm_num]
    rw [lintegral_prod _ (by fun_prop)]
    exact ENNReal.rpow_le_rpow (lintegral_mono hsection) (by norm_num)
  apply hleft.trans
  convert hM using 1 <;>
    simp only [A, B, Pi.add_apply, ← ENNReal.rpow_mul,
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (3 : ℝ≥0∞) ≠ 0)
        (by norm_num : (3 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat] <;>
    norm_num

/-- An input independent of a random affine background satisfies the squared
third-norm recurrence. [OD14, §9.2, tensorization; Remark 11.66]

**Proof sketch.** Independence factors the joint law. Apply the product-law
norm inequality and transfer all norms back to the original probability space. -/
theorem independent_affine_three_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A D X : Ω → ℝ} {ρ : ℝ}
    (hA : MemLp A 3 μ) (hD : MemLp D 3 μ)
    (hX : IsHypercontractive X μ 2 3 ρ) (hρ : 0 < ρ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hsecond : (∫ ω, X ω ^ 2 ∂μ) = 1)
    (hind : IndepFun X (fun ω => (A ω, D ω)) μ) :
    rvLpNorm (fun ω => A ω + D ω * X ω) μ 3 ^ 2 ≤
      rvLpNorm A μ 3 ^ 2 + rvLpNorm (fun ω => D ω / ρ) μ 3 ^ 2 := by
  have hXmem : MemLp X 3 μ := hX.2.2.2.2.1
  have hAD := hA.aemeasurable.prodMk hD.aemeasurable
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hXmem.aemeasurable
  have hscalar (a b : ℝ) :
      eLpNorm (fun x => a + b * x) 3 (μ.map X) ^ (2 : ℝ) ≤
        ENNReal.ofReal (a ^ 2 + (b / ρ) ^ 2) := by
    rw [eLpNorm_map_measure (by fun_prop) hXmem.aemeasurable]
    have hm : MemLp (fun ω => a + b * X ω) 3 μ :=
      (memLp_const a).add (hXmem.const_mul b)
    have h := ENNReal.ofReal_le_ofReal (hX.affine_three_norm_sq hρ hmean hsecond a b)
    have he : ENNReal.ofReal (rvLpNorm (fun ω => a + b * X ω) μ 3) =
        eLpNorm (fun ω => a + b * X ω) 3 μ := by
      simpa [rvLpNorm] using ENNReal.ofReal_toReal hm.2.ne
    rw [ENNReal.ofReal_pow
      (show 0 ≤ rvLpNorm (fun ω => a + b * X ω) μ 3 from ENNReal.toReal_nonneg), he] at h
    simpa only [ENNReal.rpow_two] using h
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hAD hXmem.aemeasurable).mp hind.symm
  have h := affine_product_three_norm_sq (μ.map (fun ω => (A ω, D ω))) (μ.map X) hscalar
  rw [← hlaw] at h
  rw [eLpNorm_map_measure (by fun_prop) (hAD.prodMk hXmem.aemeasurable),
    eLpNorm_map_measure (by fun_prop) hAD,
    eLpNorm_map_measure (by fun_prop) hAD] at h
  have hDs : MemLp (fun ω => D ω / ρ) 3 μ := by
    simpa only [div_eq_mul_inv, mul_comm] using hD.const_mul ρ⁻¹
  have hnA := hA.2.ne
  have hnD := hDs.2.ne
  simp only [ENNReal.rpow_two] at h
  have hR : eLpNorm A 3 μ ^ 2 + eLpNorm (fun ω => D ω / ρ) 3 μ ^ 2 ≠ ⊤ := by
    finiteness
  have hr := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simpa [rvLpNorm] using hr

/-- A bound on the squared third norm bounds the third absolute moment by its
three-halves power. This is technical real-norm conversion glue. -/
theorem third_moment_le_of_three_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℝ} (hZ : MemLp Z 3 μ) {B : ℝ} (_hB : 0 ≤ B)
    (h : rvLpNorm Z μ 3 ^ 2 ≤ B) :
    (∫ ω, |Z ω| ^ 3 ∂μ) ≤ B ^ (3 / 2 : ℝ) := by
  have hnorm : 0 ≤ rvLpNorm Z μ 3 := ENNReal.toReal_nonneg
  have hm := rvLpNorm_rpow Z μ 3 (by norm_num) (by simpa using hZ)
  simp only [Real.rpow_ofNat] at hm
  rw [← hm]
  calc
    _ = (rvLpNorm Z μ 3 ^ 2) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast_mul hnorm]
      norm_num
    _ ≤ B ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (sq_nonneg _) h (by norm_num)

/-- A degree-`k` polynomial in standardized hypercontractive inputs has squared
third norm at most `ρ^(-2k)` times its coefficient second moment.
[OD14, Remark 11.66, using the tensorization argument of §9.2]

**Proof sketch.** Induct over the active coordinates. Split off one input and
apply the affine norm recurrence. Its derivative has one lower degree, which
absorbs the extra inverse square of the hypercontractive radius. -/
theorem polynomial_three_norm_sq
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hX : ∀ i, IsHypercontractive (X i) μ 2 3 ρ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) :
    rvLpNorm (evalMultilinearRV F X) μ 3 ^ 2 ≤
      (1 / ρ) ^ (2 * k) * (∑ S : Finset (Fin n), F S ^ 2) := by
  classical
  let r : ℝ := 1 / ρ
  let Y (s : Finset (Fin n)) (H : MultilinearPolynomial n) : Ω → ℝ :=
    fun ω => ∑ T ∈ s.powerset, H T * ∏ j ∈ T, X j ω
  have hr : 1 ≤ r := (one_le_div hρ.1).mpr hρ.2.le
  have hmem (i : Fin n) : MemLp (X i) 3 μ := (hX i).2.2.2.2.1
  have hYmem (s : Finset (Fin n)) (H : MultilinearPolynomial n) :
      MemLp (Y s H) 3 μ := by
    exact memLp_finset_sum s.powerset fun T _ =>
      (MultilinearMoments.monomial_memLp_nat (by norm_num : 0 < 3) X hI hmem T).const_mul (H T)
  have hconstant (c : ℝ) (m : ℕ) :
      rvLpNorm (fun _ : Ω => c) μ 3 ^ 2 ≤ r ^ (2 * m) * c ^ 2 := by
    rw [rvLpNorm_const μ c 3 (by norm_num), sq_abs]
    exact le_mul_of_one_le_left (sq_nonneg c) (one_le_pow₀ hr)
  have hscale (D : Ω → ℝ) :
      rvLpNorm (fun ω => D ω / ρ) μ 3 ^ 2 = r ^ 2 * rvLpNorm D μ 3 ^ 2 := by
    have he : (fun ω => D ω / ρ) = fun ω => r * D ω := by
      funext ω
      simp [r, div_eq_mul_inv, mul_comm]
    rw [he, rvLpNorm_const_mul, mul_pow, sq_abs]
  have hYzero (s : Finset (Fin n)) (H : MultilinearPolynomial n)
      (hH : H.HasDegreeAtMost 0) : Y s H = fun _ => H ∅ := by
    funext ω
    dsimp only [Y]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T hT hTne
      rw [hH T (by simpa only [Finset.card_pos] using Finset.nonempty_iff_ne_empty.mpr hTne),
        zero_mul]
    · simp
  have hbound : ∀ (s : Finset (Fin n)) (m : ℕ) (H : MultilinearPolynomial n),
      H.HasDegreeAtMost m →
      rvLpNorm (Y s H) μ 3 ^ 2 ≤ r ^ (2 * m) * (∑ T ∈ s.powerset, H T ^ 2) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro m H hH
        simpa only [Y, Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty, mul_one] using
          hconstant (H ∅) m
    | @insert i s hi ih =>
        intro m H hH
        cases m with
        | zero =>
            rw [hYzero (insert i s) H hH]
            have hsum : H ∅ ^ 2 ≤ ∑ T ∈ (insert i s).powerset, H T ^ 2 :=
              Finset.single_le_sum (fun T _ => sq_nonneg (H T)) (by simp)
            calc
              _ ≤ H ∅ ^ 2 := by simpa using hconstant (H ∅) 0
              _ ≤ _ := by simpa using hsum
        | succ m =>
            let G := coordinateDerivative H i
            have hGcoeff (T : Finset (Fin n)) (hT : T ∈ s.powerset) : G T = H (insert i T) := by
              change coordinateDerivative H i T = H (insert i T)
              rw [coordinateDerivative_coeff, if_neg]
              exact fun hiT => hi ((Finset.mem_powerset.mp hT) hiT)
            have hsplit : Y (insert i s) H = fun ω => Y s H ω + Y s G ω * X i ω := by
              funext ω
              dsimp only [Y]
              rw [multilinear_sum_insert hi H X ω]
              have he : (∑ T ∈ s.powerset, G T * ∏ j ∈ T, X j ω) =
                  ∑ T ∈ s.powerset, H (insert i T) * ∏ j ∈ T, X j ω :=
                Finset.sum_congr rfl fun T hT => by rw [hGcoeff T hT]
              rw [he, mul_comm]
            have hcoeff : (∑ T ∈ (insert i s).powerset, H T ^ 2) =
                (∑ T ∈ s.powerset, H T ^ 2) + (∑ T ∈ s.powerset, G T ^ 2) := by
              rw [Finset.sum_powerset_insert hi]
              congr 1
              apply Finset.sum_congr rfl
              intro T hT
              rw [hGcoeff T hT]
            have hind : IndepFun (X i) (fun ω => (Y s H ω, Y s G ω)) μ :=
              MultilinearMoments.indep_sum_of_notMem hI (fun j => (hmem j).aemeasurable) H G s i hi
            have hrecur := independent_affine_three_norm_sq (hYmem s H) (hYmem s G)
              (hX i) hρ.1 (hmean i) (hsecond i) hind
            rw [hscale] at hrecur
            rw [hsplit, hcoeff]
            calc
              _ ≤ rvLpNorm (Y s H) μ 3 ^ 2 + r ^ 2 * rvLpNorm (Y s G) μ 3 ^ 2 := hrecur
              _ ≤ r ^ (2 * (m + 1)) * (∑ T ∈ s.powerset, H T ^ 2) +
                  r ^ 2 * (r ^ (2 * m) * (∑ T ∈ s.powerset, G T ^ 2)) :=
                add_le_add (ih (m + 1) H hH)
                  (mul_le_mul_of_nonneg_left (ih m G (coordinateDerivative_degree H i hH)) (sq_nonneg r))
              _ = _ := by
                rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
                ring
  simpa only [Y, Finset.powerset_univ, r, evalMultilinearRV] using
    hbound Finset.univ k F hdegree

/-- A degree-`k` polynomial in standardized hypercontractive inputs has third
absolute moment at most `ρ^(-3k)` times its coefficient energy to the three-halves
power. [OD14, Remark 11.66 (proof)]

**Proof sketch.** Raise the squared third-norm bound to the three-halves power.
The norm-moment identity and the power laws give the stated radius exponent. -/
theorem polynomial_abs_third_moment
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hX : ∀ i, IsHypercontractive (X i) μ 2 3 ρ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) :
    (∫ ω, |evalMultilinearRV F X ω| ^ 3 ∂μ) ≤
      (1 / ρ) ^ (3 * k) * (∑ S : Finset (Fin n), F S ^ 2) ^ (3 / 2 : ℝ) := by
  have hρ0 : 0 < ρ := hρ.1
  have hQ : 0 ≤ ∑ S : Finset (Fin n), F S ^ 2 :=
    Finset.sum_nonneg fun S _ => sq_nonneg _
  have hmem := evalMultilinearRV_memLp_nat (by decide : 0 < 3) F X μ hI
    (fun i => (hX i).2.2.2.2.1)
  calc
    _ ≤ ((1 / ρ) ^ (2 * k) * (∑ S : Finset (Fin n), F S ^ 2)) ^ (3 / 2 : ℝ) :=
      third_moment_le_of_three_norm_sq hmem (by positivity)
        (polynomial_three_norm_sq F hdegree X hI ρ hρ hX hmean hsecond)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hQ,
        ← Real.rpow_natCast_mul (by positivity : 0 ≤ 1 / ρ)]
      congr 1
      rw [← Real.rpow_natCast (1 / ρ) (3 * k)]
      congr 1
      push_cast
      ring

/-- The part of a polynomial containing coordinate `i` has third absolute moment
bounded by `ρ^(-3k)` times the influence to the three-halves power.
[OD14, Remark 11.66 (proof)]

**Proof sketch.** Remove the coordinate-free coefficients. The remaining
polynomial has the same degree bound and coefficient energy equal to the influence. -/
theorem coordinate_abs_third_moment
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (i : Fin n) (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hX : ∀ j, IsHypercontractive (X j) μ 2 3 ρ)
    (hmean : ∀ j, (∫ ω, X j ω ∂μ) = 0)
    (hsecond : ∀ j, (∫ ω, X j ω ^ 2 ∂μ) = 1) :
    (∫ ω, |X i ω * evalMultilinearRV (coordinateDerivative F i) X ω| ^ 3 ∂μ) ≤
      (1 / ρ) ^ (3 * k) * (influence i F.eval) ^ (3 / 2 : ℝ) := by
  classical
  let G : MultilinearPolynomial n := fun S => F S - coordinateFree F i S
  have hG : G.HasDegreeAtMost k := by
    intro S hS
    simp [G, coordinateFree, hdegree S hS]
  have hGeval : evalMultilinearRV G X =
      fun ω => X i ω * evalMultilinearRV (coordinateDerivative F i) X ω := by
    funext ω
    have he : evalMultilinearRV G X ω =
        evalMultilinearRV F X ω - evalMultilinearRV (coordinateFree F i) X ω := by
      simp only [evalMultilinearRV, G, sub_mul, Finset.sum_sub_distrib]
    rw [he, eval_coordinate_split]
    ring
  have hGsq : (∑ S : Finset (Fin n), G S ^ 2) = influence i F.eval := by
    rw [influence_eq_sum_fourier]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hiS : i ∈ S <;> simp [G, coordinateFree, hiS]
  simpa only [hGeval, hGsq] using
    polynomial_abs_third_moment G hG X hI ρ hρ hX hmean hsecond

/-- The sum of the two absolute cubic affine tests dominates their quadratic
Taylor sum. This is scalar algebra for the hypercontractive radius bound. -/
private lemma two_add_six_sq_le_abs_cubes (t : ℝ) :
    2 + 6 * t ^ 2 ≤ |1 + t| ^ 3 + |1 - t| ^ 3 := by
  by_cases hneg : t < -1
  · rw [abs_of_nonpos (by linarith : 1 + t ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
    nlinarith [pow_nonneg (by linarith : 0 ≤ -t - 1) 3]
  · by_cases hpos : 1 < t
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 + t),
        abs_of_nonpos (by linarith : 1 - t ≤ 0)]
      nlinarith [pow_nonneg (by linarith : 0 ≤ t - 1) 3]
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 + t),
        abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
      ring_nf
      exact le_rfl

/-- Affine third moments of a standardized hypercontractive input are bounded by
the three-halves power of the rescaled second moment. [OD14, Remark 11.66 (proof)] -/
theorem affine_abs_third_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {ρ : ℝ}
    (hX : IsHypercontractive X μ 2 3 ρ) (hρ : 0 < ρ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hsecond : (∫ ω, X ω ^ 2 ∂μ) = 1)
    (a b : ℝ) :
    (∫ ω, |a + b * X ω| ^ 3 ∂μ) ≤
      (a ^ 2 + (b / ρ) ^ 2) ^ (3 / 2 : ℝ) :=
  third_moment_le_of_three_norm_sq
    ((memLp_const a).add (hX.2.2.2.2.1.const_mul b)) (by positivity)
    (hX.affine_three_norm_sq hρ hmean hsecond a b)

/-- A coarse rational bound for the affine third-moment estimate. -/
private lemma two_rpow_three_halves_le_three : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
  have hs : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 / 2 : ℝ)]

/-- A centered unit-second-moment input hypercontractive from two to three has
squared radius at most `2/3`. [OD14, Def. 9.13; Cor. 11.70 (proof)]
This coarse bound suffices to absorb the polynomial degree into the radius power.

**Proof sketch.** Test both affine functions `1 ± ρX`. Each third absolute moment
is at most `2^(3/2) ≤ 3`. Their pointwise sum dominates `2 + 6ρ²X²`.
Integrating and using unit second moment gives `2 + 6ρ² ≤ 6`. -/
theorem hypercontractive_radius_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {ρ : ℝ}
    (hX : IsHypercontractive X μ 2 3 ρ) (hρ : 0 < ρ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hsecond : (∫ ω, X ω ^ 2 ∂μ) = 1) :
    ρ ^ 2 ≤ 2 / 3 := by
  have hmoment (b : ℝ) (hb : b ^ 2 = ρ ^ 2) :
      (∫ ω, |1 + b * X ω| ^ 3 ∂μ) ≤ 3 := by
    have h := affine_abs_third_moment_le hX hρ hmean hsecond 1 b
    have heq : (1 : ℝ) ^ 2 + (b / ρ) ^ 2 = 2 := by
      rw [div_pow, hb, div_self (pow_ne_zero 2 hρ.ne')]
      norm_num
    rw [heq] at h
    exact h.trans two_rpow_three_halves_le_three
  have hplus := hmoment ρ rfl
  have hminus := hmoment (-ρ) (by ring)
  simp only [neg_mul, ← sub_eq_add_neg] at hminus
  have hplusM : MemLp (fun ω => 1 + ρ * X ω) 3 μ :=
    (memLp_const (μ := μ) (p := (3 : ℝ≥0∞)) (1 : ℝ)).add
      (hX.2.2.2.2.1.const_mul ρ)
  have hminusM : MemLp (fun ω => 1 - ρ * X ω) 3 μ :=
    (memLp_const (μ := μ) (p := (3 : ℝ≥0∞)) (1 : ℝ)).sub
      (hX.2.2.2.2.1.const_mul ρ)
  have hplusI : Integrable (fun ω => |1 + ρ * X ω| ^ 3) μ := by
    simpa only [Real.norm_eq_abs] using hplusM.integrable_norm_pow' (p := 3)
  have hminusI : Integrable (fun ω => |1 - ρ * X ω| ^ 3) μ := by
    simpa only [Real.norm_eq_abs] using hminusM.integrable_norm_pow' (p := 3)
  have hscaled : MemLp (fun ω => ρ * X ω) 2 μ :=
    (hX.2.2.2.2.1.const_mul ρ).mono_exponent (by norm_num)
  have hcompare := integral_mono
    ((integrable_const (2 : ℝ)).add (hscaled.integrable_sq.const_mul 6))
    (hplusI.add hminusI) (fun ω => two_add_six_sq_le_abs_cubes (ρ * X ω))
  change (∫ ω, 2 + 6 * (ρ * X ω) ^ 2 ∂μ) ≤
    ∫ ω, |1 + ρ * X ω| ^ 3 + |1 - ρ * X ω| ^ 3 ∂μ at hcompare
  rw [integral_add (integrable_const 2) (hscaled.integrable_sq.const_mul 6),
    integral_add hplusI hminusI] at hcompare
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
    integral_const_mul] at hcompare
  simp_rw [mul_pow, integral_const_mul] at hcompare
  rw [hsecond] at hcompare
  nlinarith only [hcompare, hplus, hminus]

/-- A standardized two-to-three hypercontractive input has radius at most `5/6`.
[OD14, Def. 9.13; Cor. 11.70 (proof), coarse radius bound] -/
theorem hypercontractive_radius_le_five_sixths
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {ρ : ℝ}
    (hX : IsHypercontractive X μ 2 3 ρ) (hρ : 0 < ρ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hsecond : (∫ ω, X ω ^ 2 ∂μ) = 1) :
    ρ ≤ 5 / 6 := by
  nlinarith [hypercontractive_radius_sq_le hX hρ hmean hsecond]

end BooleanAnalysis.GaussianSpace.Invariance
