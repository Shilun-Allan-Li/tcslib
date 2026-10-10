/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Definitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Contraction
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Centered
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.ProjectionBounds
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.LowDegree
import TCSlib.BooleanAnalysis.KKL
import TCSlib.BooleanAnalysis.LMN.DecisionTreeFourier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomization and low-degree projections

## Main definitions

The constructions live in `Randomization.Definitions` and `RandomVariables.Basic`.

## Main results

* `randomization_norm_two`: Proposition 10.34.
* Theorem 10.35 is subsumed by the later contraction statements; see the derivation note
  below `randomized_noise_contraction`.
* `cube_lowDegree_projection`, `cube_lowDegree_projection_noise`: 10.37–10.38.
* `product_lowDegree_projection`: Theorem 10.39, independent of atom probabilities.
* `half_noise_norm_le_randomization`, `centered_negative_contraction`,
  `randomized_noise_contraction`: 10.42–10.44.

The constants precede all product spaces and dimensions. Heterogeneous products extend
the source's homogeneous presentation by the same coordinatewise argument.
The cube projection, randomization, and product low-degree projection estimates are proved.
Supporting spectral and norm lemmas live in `Randomization.ProjectionBounds`; conditional
expectation and contraction lemmas live in `Randomization.Basic` and
`Randomization.Contraction`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.4, Remark 10.33 through Theorem 10.44.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

open RandomizationAux RandomizationProjectionAux

variable {n : ℕ}

universe u

/-- At each product input, the randomized second moment equals the sum of squared
orthogonal components. [OD14, Rem. 10.33]

**Proof sketch.** Apply cube Parseval with the component-as-coefficient identity. -/
theorem randomization_pointwise_parseval {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) :
    expect (fun r => randomization P f r x ^ 2) =
      ∑ S : Finset (Fin n), P.component S f x ^ 2 := by
  simpa only [innerProduct, ← pow_two, randomization_fourier_coefficient] using
    (parseval (fun r => randomization P f r x))

/-- Randomization preserves the second norm. [OD14, Prop. 10.34]

**Proof sketch.** Apply Parseval in the signs at each input, average over inputs, and
apply orthogonality of the product decomposition. -/
theorem randomization_norm_two {n : ℕ} (P : FiniteProduct.{u} n) (f : P.Point → ℝ) :
    randomizationNorm P 2 f = P.norm 2 f := (by
  unfold randomizationNorm FiniteProduct.norm
  simp only [Real.rpow_two, sq_abs, randomization_pointwise_parseval]
  rw [P.expect_sum, ← P.parseval]
)


/-- Cube projection to degree `k` costs at most `(√(q-1))^k` for `q≥2`, and its reciprocal
to the same power for `1<q≤2`. [OD14, Prop. 10.37]

**Proof sketch.** For `q≥2` use hypercontractivity, second-norm contractivity of projection,
and norm monotonicity. Apply self-adjointness and duality for exponents below two. -/
theorem cube_lowDegree_projection {n : ℕ} (g : BooleanFunc n) (k : ℕ)
    (q : ℝ) (hq : 1 < q) :
    (2 ≤ q → cubeLpNorm q (KKL.lowDegreePart g k) ≤
      Real.sqrt (q - 1) ^ k * cubeLpNorm q g) ∧
    (q ≤ 2 → cubeLpNorm q (KKL.lowDegreePart g k) ≤
      (1 / Real.sqrt (q - 1)) ^ k * cubeLpNorm q g) := (by
  classical
  -- Above two, combine the low-degree bound, projection contractivity, and norm monotonicity.
  have high (p : ℝ) (hp : 2 ≤ p) (f : BooleanFunc n) :
      cubeLpNorm p (KKL.lowDegreePart f k) ≤
        Real.sqrt (p - 1) ^ k * cubeLpNorm p f := by
    calc
      cubeLpNorm p (KKL.lowDegreePart f k) ≤
          Real.sqrt (p - 1) ^ k * l2Norm (KKL.lowDegreePart f k) :=
        lowDegree_norm_ge_two _ (cube_lowDegree_has_degree f k) p hp
      _ ≤ Real.sqrt (p - 1) ^ k * l2Norm f :=
        mul_le_mul_of_nonneg_left (cube_lowDegree_l2_le f k) (by positivity)
      _ ≤ Real.sqrt (p - 1) ^ k * cubeLpNorm p f := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← cubeLpNorm_two]
        exact lp_norm_mono 2 p (by norm_num) hp f
  refine ⟨fun hq2 => high q hq2 g, ?_⟩
  intro hq2
  -- Below two, transfer the conjugate-exponent bound through self-adjointness.
  let p : ℝ := q / (q - 1)
  have hconj : Real.HolderConjugate q p :=
    (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  have hp2 : 2 ≤ p := by
    dsimp only [p]
    apply (le_div_iff₀ (sub_pos.mpr hq)).2
    linarith
  have hself (f h : BooleanFunc n) :
      innerProduct f (KKL.lowDegreePart h k) =
        innerProduct (KKL.lowDegreePart f k) h := by
    rw [plancherel, plancherel]
    apply Finset.sum_congr rfl
    intro S _
    rw [KKL.fourierCoeff_lowDegreePart, KKL.fourierCoeff_lowDegreePart]
    split_ifs <;> simp
  have hroot : (p - 1) / p = 1 / q := by
    field_simp [hconj.symm.ne_zero, hconj.ne_zero]
    nlinarith [hconj.symm.sub_one_mul_conj]
  have hsqrt : Real.sqrt (p - 1) = 1 / Real.sqrt (q - 1) := by
    rw [show p - 1 = (q - 1)⁻¹ by
      dsimp only [p]
      field_simp [ne_of_gt (sub_pos.mpr hq)]
      ring, Real.sqrt_inv, one_div]
  obtain ⟨f, hf, hnorm⟩ := holder_sharpness hconj.symm (KKL.lowDegreePart g k)
  have hholder :
      innerProduct (KKL.lowDegreePart f k) g ≤
        cubeLpNorm p (KKL.lowDegreePart f k) * cubeLpNorm q g := by
    simpa only [← hconj.symm.conjugate_eq, hroot, cubeLpNorm] using
      (holder_ineq_bool p hconj.symm.lt (KKL.lowDegreePart f k) g)
  calc
    cubeLpNorm q (KKL.lowDegreePart g k) ≤ innerProduct f (KKL.lowDegreePart g k) :=
      hnorm
    _ = innerProduct (KKL.lowDegreePart f k) g := hself f g
    _ ≤ cubeLpNorm p (KKL.lowDegreePart f k) * cubeLpNorm q g := hholder
    _ ≤ (Real.sqrt (p - 1) ^ k * cubeLpNorm p f) * cubeLpNorm q g :=
      mul_le_mul_of_nonneg_right (high p hp2 f)
        (Real.rpow_nonneg (expect_rpow_abs_nonneg q g) _)
    _ ≤ Real.sqrt (p - 1) ^ k * cubeLpNorm q g := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (expect_rpow_abs_nonneg q g) _)
      exact mul_le_of_le_one_right (pow_nonneg (Real.sqrt_nonneg _) _) hf
    _ = (1 / Real.sqrt (q - 1)) ^ k * cubeLpNorm q g := by rw [hsqrt]
)


/-- Cube projection to degree `k` has fourth norm at most `(√3/ρ)^k` times the fourth
norm of the `ρ`-noised function. [OD14, Lem. 10.38]

**Proof sketch.** Apply Bonami to the projection, compare its second-norm Fourier weights
with those of the noisy function, and increase the norm exponent from two to four. -/
theorem cube_lowDegree_projection_noise {n : ℕ} (g : BooleanFunc n) (k : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cubeLpNorm 4 (KKL.lowDegreePart g k) ≤
      (Real.sqrt 3 / ρ) ^ k * cubeLpNorm 4 (noiseOp ρ g) := (by
  classical
  let r : ℝ := Real.sqrt 3 / ρ
  let f : BooleanFunc n := KKL.lowDegreePart (noiseOp ρ g) k
  have hsqrt : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have hr : 1 ≤ r := (le_div_iff₀ hρ).2 (by simpa using hρ1.trans hsqrt)
  have hcancel :
      noiseOp (1 / Real.sqrt 3) (noiseOp r f) = KKL.lowDegreePart g k := by
    rw [noiseOp_compose]
    funext x
    change
      (∑ S : Finset (Fin n),
        (1 / Real.sqrt 3 * r) ^ S.card *
          fourierCoeff (KKL.lowDegreePart (noiseOp ρ g) k) S * chiS S x) =
      ∑ S : Finset (Fin n),
        if S.card ≤ k then fourierCoeff g S * chiS S x else 0
    apply Finset.sum_congr rfl
    intro S _
    rw [KKL.fourierCoeff_lowDegreePart, noiseOp_fourier]
    by_cases hS : S.card ≤ k
    · simp only [if_pos hS]
      rw [← mul_assoc, ← mul_pow,
        show (1 / Real.sqrt 3 * r) * ρ = 1 by
          dsimp [r]
          field_simp [hρ.ne', ne_of_gt (lt_of_lt_of_le zero_lt_one hsqrt)]]
      simp
    · simp [hS]
  have hc := general_one_function_hypercontractivity
    2 4 (by norm_num) (by norm_num) (by norm_num)
    (1 / Real.sqrt 3) (by positivity)
    (div_le_one_of_le₀ hsqrt (by positivity))
    (by norm_num [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num)])
    (noiseOp r f)
  calc
    cubeLpNorm 4 (KKL.lowDegreePart g k) ≤ l2Norm (noiseOp r f) := by
      rw [← cubeLpNorm_two]
      simpa only [hcancel] using hc
    _ ≤ r ^ k * l2Norm f :=
      l2Norm_noiseOp_le f (cube_lowDegree_has_degree (noiseOp ρ g) k) r hr
    _ ≤ r ^ k * l2Norm (noiseOp ρ g) :=
      mul_le_mul_of_nonneg_left (cube_lowDegree_l2_le (noiseOp ρ g) k)
        (pow_nonneg (zero_le_one.trans hr) _)
    _ ≤ r ^ k * cubeLpNorm 4 (noiseOp ρ g) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hr) _)
      rw [← cubeLpNorm_two]
      exact lp_norm_mono 2 4 (by norm_num) (by norm_num) (noiseOp ρ g)
)


/-- Randomization equals anisotropic noise at the independently chosen sign rates.
[OD14, Fact 10.41]

**Proof sketch.** Compare their orthogonal-component expansions term by term. -/
theorem randomization_eq_anisotropicNoise {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (r : BoolCube n) (x : P.Point) :
    randomization P f r x = anisotropicNoise P (fun i => boolToSign (r i)) f x := by
  rfl

/-- The positive-sign mask contains the coordinates whose Walsh signs equal one. -/
private def positiveMask {n : ℕ} (r : BoolCube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => r i = false)

/-- A component retained by the positive-sign mask has expected signed multiplier
`(1/2)^|S|`. [OD14, Def. 10.32]
This finite identity expresses the independence of the coordinate signs.

**Proof sketch.** The retained multiplier is the product of the factors
`(1 + rᵢ)/2` over `S`. Expand this product into Walsh characters. Every nonempty
character has expectation zero, leaving only the empty character. -/
private theorem positiveMask_coefficient_expect {n : ℕ} (S : Finset (Fin n)) :
    expect (fun r : BoolCube n =>
      if S ⊆ positiveMask r then chiS S r else 0) = (1 / 2 : ℝ) ^ S.card :=
  (by
  classical
  have hmask (r : BoolCube n) :
      (if S ⊆ positiveMask r then chiS S r else 0) =
        (1 / 2 : ℝ) ^ S.card * ∑ T ∈ S.powerset, chiS T r := by
    calc
      (if S ⊆ positiveMask r then chiS S r else 0) =
          ∏ i ∈ S, if r i = false then boolToSign (r i) else 0 := by
        rw [Finset.prod_ite_zero]
        simp only [positiveMask, Finset.subset_iff, Finset.mem_filter,
          Finset.mem_univ, true_and, chiS]
        congr 1
      _ = ∏ i ∈ S, (1 / 2 : ℝ) * (1 + boolToSign (r i)) := by
        apply Finset.prod_congr rfl
        intro i _
        cases r i <;> norm_num [boolToSign]
      _ = (1 / 2 : ℝ) ^ S.card * ∑ T ∈ S.powerset, chiS T r := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_one_add]
        rfl
  have hmean (T : Finset (Fin n)) :
      expect (chiS T) = if T = ∅ then 1 else 0 := by
    simpa only [innerProduct, chiS_empty, mul_one] using
      (fourier_coeff_chi T ∅)
  simp_rw [hmask]
  rw [ThresholdFunctions.expect_const_mul, expect_eq_fintypeExpect,
    Finset.expect_sum_comm]
  simp [← expect_eq_fintypeExpect, hmean]
)

/-- Averaging randomization after retaining only its positive-sign coordinates recovers
half-noising. [OD14, Thm. 10.42]
This is a finite averaging reformulation used for the norm comparison.

**Proof sketch.** Conditional expectation discards components outside the retained
coordinate set. Average the remaining signed multipliers: a component indexed by `S`
receives coefficient `(1/2)^|S|`, exactly its half-noise multiplier. -/
private theorem randomization_condExp_average {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) :
    expect (fun r : BoolCube n =>
      P.condExp (positiveMask r) (randomization P f r) x) =
        P.noise (1 / 2) f x :=
  (by
  classical
  have hcond (r : BoolCube n) :
      P.condExp (positiveMask r) (randomization P f r) x =
        ∑ S : Finset (Fin n),
          (if S ⊆ positiveMask r then chiS S r else 0) * P.component S f x := by
    change P.expect (fun y => ∑ S : Finset (Fin n),
      chiS S r * P.component S f
        (fun i => if i ∈ positiveMask r then x i else y i)) = _
    rw [P.expect_sum_mul]
    change (∑ S : Finset (Fin n),
      chiS S r * P.condExp (positiveMask r) (P.component S f) x) = _
    simp only [condExp_component]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  simp_rw [hcond]
  rw [expect_eq_fintypeExpect, Finset.expect_sum_comm]
  simp only [FiniteProduct.noise, ← Finset.expect_mul,
    ← expect_eq_fintypeExpect, positiveMask_coefficient_expect]
)

/-- Half-noising has no larger norm than randomizing at every exponent `q≥1`.
[OD14, Thm. 10.42]

**Proof sketch.** For each choice of signs, retain its positive-sign coordinates by
conditional expectation. Averaging these functions gives half-noising. Jensen bounds
the absolute power of this sign average, and conditional expectation does not increase
the corresponding moment. Interchange the finite expectations and take the monotone
`q`th root. -/
theorem half_noise_norm_le_randomization {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (q : ℝ) (hq : 1 ≤ q) :
    P.norm q (P.noise (1 / 2) f) ≤ randomizationNorm P q f := (by
  classical
  have hmass (x : P.Point) : 0 ≤ P.mass x :=
    Finset.prod_nonneg (fun i _ => (P.weight_pos i (x i)).le)
  have hsign : (∑ _r : BoolCube n, uniformWeight n) = 1 := by
    simpa only [expect, Finset.mul_sum, mul_one] using
      (ThresholdFunctions.expect_const (n := n) (1 : ℝ))
  unfold FiniteProduct.norm randomizationNorm
  apply Real.rpow_le_rpow
    (Finset.sum_nonneg (fun x _ =>
      mul_nonneg (hmass x) (Real.rpow_nonneg (abs_nonneg _) _)))
    ?_ (one_div_nonneg.mpr (zero_le_one.trans hq))
  calc
    P.expect (fun x => |P.noise (1 / 2) f x| ^ q) ≤
        P.expect (fun x => expect (fun r =>
          |P.condExp (positiveMask r) (randomization P f r) x| ^ q)) := by
      unfold FiniteProduct.expect
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hmass x)
      dsimp only
      rw [← randomization_condExp_average P f x]
      simp only [expect, Finset.mul_sum]
      exact weighted_abs_rpow_sum_le Finset.univ
        (fun _ : BoolCube n => uniformWeight n)
        (fun r => P.condExp (positiveMask r) (randomization P f r) x) q
        (fun _ _ => by unfold uniformWeight; positivity) hsign hq
    _ = expect (fun r => P.expect (fun x =>
        |P.condExp (positiveMask r) (randomization P f r) x| ^ q)) := by
      simp only [FiniteProduct.expect, expect_eq_fintypeExpect,
        Finset.expect_sum_comm, ← Finset.mul_expect]
    _ ≤ expect (fun r => P.expect (fun x => |randomization P f r x| ^ q)) :=
      ThresholdFunctions.expect_mono (fun r =>
        condExp_moment_le P (positiveMask r) (randomization P f r) q hq)
    _ = P.expect (fun x => expect (fun r => |randomization P f r x| ^ q)) := by
      simp only [FiniteProduct.expect, expect_eq_fintypeExpect,
        Finset.expect_sum_comm, ← Finset.mul_expect]
)

/-- A sufficiently small negative multiple of any centered variable costs no more in
`Lᵠ` than the original positive multiple, uniformly in the translate; `q=4` permits `c=2/5`.
[OD14, Lem. 10.43]

**Proof sketch.** Bound the scalar remainder after removing the affine part, then integrate
using centering. For exponent four, expand and use a nonnegative quadratic estimate. -/
theorem centered_negative_contraction (q : ℝ) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ (q = 4 → c = 2 / 5) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (a : ℝ), MemLp X (ENNReal.ofReal q) μ →
        (∫ ω, X ω ∂μ) = 0 →
        rvLpNorm (fun ω => a - c * X ω) μ q ≤ rvLpNorm (fun ω => a + X ω) μ q := (by
  obtain ⟨c, hc0, hc1, hc4, hscalar⟩ := CenteredContraction.scalar_contraction q hq
  refine ⟨c, hc0, hc1, hc4, ?_⟩
  intro Ω _ μ _ X a hX hmean
  exact CenteredContraction.norm_le_of_scalar μ q hq c hc0.le hc1 hscalar X hX hmean a
)


/-- Randomizing a noised finite-product function equals anisotropic noise
whose coordinate rates are the ordinary rate times the chosen Walsh signs.
[OD14, Defs. 10.32 and 10.40; Thm. 10.44 (proof)]
The identity holds at every real rate.

**Proof sketch.** Ordinary noise multiplies the component indexed by `S`
by the rate to the power `|S|`. Its Walsh sign is the product of the
coordinate signs over `S`. Combining these two products gives exactly
the anisotropic multiplier, so the finite component expansions agree. -/
private theorem randomization_noise_eq_anisotropicNoise {n : ℕ}
    (P : FiniteProduct.{u} n) (c : ℝ) (f : P.Point → ℝ)
    (r : BoolCube n) :
    randomization P (P.noise c f) r =
      anisotropicNoise P (fun i => c * boolToSign (r i)) f :=
  (by
  classical
  funext x
  simp only [randomization, anisotropicNoise, component_noise, chiS,
    Finset.prod_mul_distrib, Finset.prod_const]
  apply Finset.sum_congr rfl
  intro S _
  ring
)
/-- If every fixed-sign randomization of a finite-product function has
`Lᵠ` norm at most that of a comparison function, its norm averaged over
the signs satisfies the same bound, for every `q > 0`.
[OD14, Thm. 10.44 (proof)]
This isolates the final finite averaging step of the source argument.

**Proof sketch.** Raise each fixed-sign norm inequality to the positive
`q`th power to compare absolute moments. Average these bounds over the
signs and interchange the two finite expectations. The comparison moment
is independent of the signs, so averaging leaves it unchanged. Take the
increasing positive `q`th root. -/
private theorem randomizationNorm_le_of_norm_le {n : ℕ}
    (P : FiniteProduct.{u} n) (f g : P.Point → ℝ)
    (q : ℝ) (hq : 0 < q)
    (hbound : ∀ r : BoolCube n,
      P.norm q (randomization P f r) ≤ P.norm q g) :
    randomizationNorm P q f ≤ P.norm q g :=
  (by
  classical
  have hnonneg (h : P.Point → ℝ) :
      0 ≤ P.expect (fun x => |h x| ^ q) :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
        (Real.rpow_nonneg (abs_nonneg _) _)
  have hmoment (r : BoolCube n) :
      P.expect (fun x => |randomization P f r x| ^ q) ≤
        P.expect (fun x => |g x| ^ q) :=
    (Real.rpow_le_rpow_iff (hnonneg (randomization P f r)) (hnonneg g)
      (one_div_pos.mpr hq)).mp (hbound r)
  unfold randomizationNorm FiniteProduct.norm
  refine Real.rpow_le_rpow ?_ ?_ (one_div_nonneg.mpr hq.le)
  · unfold FiniteProduct.expect
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
        (expect_rpow_abs_nonneg q (fun r => randomization P f r x))
  · calc
      P.expect (fun x => expect (fun r => |randomization P f r x| ^ q)) =
          expect (fun r => P.expect (fun x => |randomization P f r x| ^ q)) := by
        simp only [FiniteProduct.expect, expect_eq_fintypeExpect,
          Finset.expect_sum_comm, ← Finset.mul_expect]
      _ ≤ expect (fun _ : BoolCube n => P.expect (fun x => |g x| ^ q)) :=
        ThresholdFunctions.expect_mono hmoment
      _ = P.expect (fun x => |g x| ^ q) :=
        ThresholdFunctions.expect_const _
)

/-- A fixed amount of noise makes randomization contractive for every `q>1`; `q=4,4/3`
permit `c=2/5`. [OD14, Thm. 10.44]

**Proof sketch.** Lemma 10.43 makes negative coordinate noise contractive for `q≥2`.
Self-adjoint duality transfers this bound to conjugate exponents below two, while
positive coordinate noise is contractive throughout. Compose the signed coordinate
operators, then average their moment bounds over the random signs. -/
theorem randomized_noise_contraction (q : ℝ) (hq : 1 < q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ((q = 4 ∨ q = 4 / 3) → c = 2 / 5) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ),
        randomizationNorm P q (P.noise c f) ≤ P.norm q f := (by
  obtain ⟨c, hc0, hc1, hcspecial, hbound⟩ :=
    signed_anisotropicNoise_contraction q hq
  refine ⟨c, hc0, hc1, hcspecial, ?_⟩
  intro n P f
  refine randomizationNorm_le_of_norm_le P (P.noise c f) f q
    (lt_trans zero_lt_one hq) ?_
  intro r
  rw [randomization_noise_eq_anisotropicNoise P c f r]
  exact hbound n P r f
)


/-- Noise at a nonzero real rate cancels noise at its reciprocal.
[OD14, Thm. 8.35; Def. 10.40]
This finite-product consequence of the spectral formula also holds for heterogeneous
coordinate laws and rates outside `[0, 1]`.

**Proof sketch.** Each component of the reciprocal-noised function has its reciprocal
multiplier. The outer noise multiplies it back, so every component has coefficient
one. Inclusion-exclusion reconstruction then recovers the original function. -/
theorem product_noise_inverse {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (hρ : ρ ≠ 0) (f : P.Point → ℝ) :
    P.noise ρ (P.noise ρ⁻¹ f) = f := (by
  classical
  funext x
  change (∑ S : Finset (Fin n),
    ρ ^ S.card * P.component S (P.noise ρ⁻¹ f) x) = f x
  simp_rw [component_noise, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hρ, one_pow, one_mul]
  calc
    (∑ S : Finset (Fin n), P.component S f x) =
        P.condExp Finset.univ f x := by
      simpa only [FiniteProduct.component, Finset.powerset_univ] using
        (sum_powerset_signed_sum (Finset.univ : Finset (Fin n))
          (fun T => P.condExp T f x))
    _ = f x := by
      simp only [FiniteProduct.condExp, Finset.mem_univ, ite_true, P.expect_const]
)

/-! The comparison in [OD14, Thm. 10.35] has no separate statement skeleton here.
Its lower bound follows from `half_noise_norm_le_randomization`. For the upper bound,
apply `randomized_noise_contraction` to the inverse-noised function `P.noise c⁻¹ f`
and use `product_noise_inverse` to cancel the consecutive noise operators. -/



/-- Equal anisotropic noise rates recover the ordinary product noise operator.
[OD14, Def. 10.40]

**Proof sketch.** The product of a constant rate over a set is its cardinality power. -/
theorem anisotropicNoise_constant {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) :
    anisotropicNoise P (fun _ => ρ) f x = P.noise ρ f x := by
  simp only [anisotropicNoise, FiniteProduct.noise, Finset.prod_const]

/-- For every `q ≥ 2`, finite-product low-degree projection has norm at most
`C ^ k` times the original norm, with `C ≥ 1` depending only on `q`; exponent
four permits `C = 5 * √3`. [OD14, Thm. 10.39, proof]

**Proof sketch.** Undo half-noising and bound the resulting norm by randomization.
Randomization turns product projection into cube projection. Apply the noisy cube
projection estimate at rate `c/2`, average over product inputs, and use randomized
noise contraction at rate `c`. Its fourth-exponent choice `c = 2/5` gives the constant. -/
private theorem product_lowDegree_projection_ge_two (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 1 ≤ C ∧ (q = 4 → C = 5 * Real.sqrt 3) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (k : ℕ),
        P.norm q (P.lowDegree k f) ≤ C ^ k * P.norm q f := by
  obtain ⟨c, hc0, hc1, hc4, hcontract⟩ :=
    randomized_noise_contraction q (by linarith)
  let C : ℝ := Real.sqrt (q - 1) / (c / 2)
  have hρ : 0 < c / 2 := by positivity
  have hC : 1 ≤ C := by
    dsimp only [C]
    apply (le_div_iff₀ hρ).2
    simp only [one_mul]
    calc
      c / 2 ≤ 1 := by linarith
      _ ≤ Real.sqrt (q - 1) := Real.one_le_sqrt.mpr (by linarith)
  refine ⟨C, hC, ?_, ?_⟩
  · intro hq4
    dsimp only [C]
    rw [hq4, hc4 (Or.inl hq4)]
    norm_num [div_eq_mul_inv]
    ring
  · intro n P f k
    calc
      P.norm q (P.lowDegree k f) =
          P.norm q (P.noise (1 / 2) (P.noise 2 (P.lowDegree k f))) := by
        congr 1
        simpa only [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] using
          (product_noise_inverse P (1 / 2) (by norm_num) (P.lowDegree k f)).symm
      _ ≤ randomizationNorm P q (P.noise 2 (P.lowDegree k f)) :=
        half_noise_norm_le_randomization P (P.noise 2 (P.lowDegree k f)) q
          (by linarith)
      _ ≤ C ^ k * randomizationNorm P q (P.noise c f) := by
        apply randomizationNorm_le_of_pointwise_cube_bound P
          (P.noise 2 (P.lowDegree k f)) (P.noise c f) q (C ^ k)
          (by linarith) (pow_nonneg (zero_le_one.trans hC) k)
        intro x
        rw [product_noise_lowDegree_commute, randomization_cube_lowDegree]
        simpa only [C, randomization_cube_noise, noiseOp_compose,
          show c / 2 * 2 = c by ring] using
          (cube_lowDegree_projection_noise_ge_two
            (fun r => randomization P (P.noise 2 f) r x) k q hq
            (c / 2) hρ (by linarith))
      _ ≤ C ^ k * P.norm q f :=
        mul_le_mul_of_nonneg_left (hcontract n P f)
          (pow_nonneg (zero_le_one.trans hC) k)

/-- Low-degree projection on any finite product costs at most `C(q)^k` in `Lᵠ`,
independently of its smallest atom; `q=4,4/3` permit `C=5√3`.
[OD14, Thm. 10.39]

**Proof sketch.** For exponents at least two, combine half-noise comparison,
pointwise cube projection, and randomized noise contraction. For smaller exponents,
transfer the bound from the conjugate exponent through self-adjointness. The
conjugate pair `4, 4/3` shares the constant `5√3`. -/
theorem product_lowDegree_projection (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 1 ≤ C ∧ ((q = 4 ∨ q = 4 / 3) → C = 5 * Real.sqrt 3) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (k : ℕ),
        P.norm q (P.lowDegree k f) ≤ C ^ k * P.norm q f := (by
  by_cases hq2 : 2 ≤ q
  · obtain ⟨C, hC, hC4, hbound⟩ := product_lowDegree_projection_ge_two q hq2
    refine ⟨C, hC, ?_, hbound⟩
    rintro (h4 | h43)
    · exact hC4 h4
    · rw [h43] at hq2
      norm_num at hq2
  · let p : ℝ := q / (q - 1)
    have hp2 : 2 ≤ p := by
      dsimp only [p]
      apply (le_div_iff₀ (sub_pos.mpr hq)).2
      linarith [lt_of_not_ge hq2]
    obtain ⟨C, hC, hC4, hbound⟩ := product_lowDegree_projection_ge_two p hp2
    refine ⟨C, hC, ?_, ?_⟩
    · rintro (h4 | h43)
      · rw [h4] at hq2
        norm_num at hq2
      · apply hC4
        dsimp only [p]
        rw [h43]
        norm_num
    · intro n P f k
      exact product_selfAdjoint_bound P (P.lowDegree k)
        (product_lowDegree_selfAdjoint P k) q hq (C ^ k)
        (pow_pos (lt_of_lt_of_le zero_lt_one hC) k)
        (fun g => hbound n P g k) f
)

end BooleanAnalysis.Hypercontractivity
