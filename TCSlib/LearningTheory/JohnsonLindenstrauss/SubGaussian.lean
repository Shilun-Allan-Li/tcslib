/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import TCSlib.LearningTheory.JohnsonLindenstrauss.ConcentrationBound
import TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sub-Gaussian Abstraction Layer for the Johnson–Lindenstrauss Lemma

## Main definitions

- (none; this file contains only theorems)

## Main results

- `subgaussian_centered_sq_bernstein` ([Ver18, Lemma 2.7.6], fully proved): a strictly
  sub-Gaussian `Z` with variance `σ²` has `Z² − σ²` with Bernstein MGF `(2σ⁴, 1/(4σ²))`.
  Helpers: `exp_mul_sq_eq_integral_gaussian` (Gaussian decoupling),
  `exp_neg_le_one_sub_add_sq_div_two`, `integral_exp_mul_sq_le_of_subgaussian` (Tonelli +
  Gaussian quadratic integral), `integral_pow_four_le_of_subgaussian` (`E Z⁴ ≤ 4σ⁴`),
  `mgf_centered_sq_le_of_nonpos`, `mgf_centered_sq_le_of_nonneg`.
- `jl_concentration_single_subgaussian`: distribution-agnostic JL single-vector
  concentration bound for sub-Gaussian row projections (no project-local axioms).

## References

* [Ver18] R. Vershynin, *High-Dimensional Probability: An Introduction with Applications in
  Data Science*, Cambridge University Press, 2018.
* [Ach03] D. Achlioptas, "Database-friendly random projections: Johnson–Lindenstrauss with
  binary coins", *J. Comput. Syst. Sci.* 66(4):671–687, 2003.
* [DG03] S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and
  Lindenstrauss", *Random Structures & Algorithms* 22(1):60–65, 2003.

Original formalization by Ganesh Sankar.
-/

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section JLSubGaussian

variable {d k : ℕ}

/-! ## Part I — Sub-Gaussian abstraction layer

The sub-Gaussian path proves **one** classical fact (the scalar Hanson–Wright bound,
[Ver18, Lemma 2.7.6], as `subgaussian_centered_sq_bernstein`) and uses it to prove a
distribution-agnostic JL concentration theorem. This is the architectural lever that lets the
Rademacher specialization in `TCSlib.LearningTheory.JohnsonLindenstrauss.Rademacher`
plug into the JL machinery for free. -/

/-! ## §1. Sub-Gaussian → sub-exponential-squared

The classical inequality: if `Z` is sub-Gaussian with parameter `σ²`
(meaning `mgf Z μ t ≤ exp(σ² · t² / 2)` for all `t`) and `E[Z²] = σ²`, then
`Z² − σ²` is sub-exponential, with centered MGF bounded by `exp(2 σ⁴ t²)`
on `|t| ≤ 1/(4 σ²)`.

This recovers the Gaussian centered-chi-squared bound in the special case
where `Z ~ N(0, σ²)`. For Rademacher rows `Z = Σⱼ εⱼ xⱼ / √k` (`εⱼ ∈ {±1}`
iid), Hoeffding's lemma gives `Z` sub-Gaussian with parameter `‖x‖²/k`,
so the same bound applies.

The proof (helpers below, assembled in `subgaussian_centered_sq_bernstein`) uses only
the strictly-sub-Gaussian MGF envelope and the exact second moment: Gaussian decoupling
plus Tonelli for `t ≥ 0`, and the elementary bound `exp(−x) ≤ 1 − x + x²/2` together with
a fourth-moment estimate for `t ≤ 0`. No Orlicz-norm machinery is needed. -/

/-- **Gaussian decoupling identity.** For `t ≥ 0` and every real `z`,
`exp(t z²) = ∫ exp(√(2t) · z · g) dN(0,1)(g)`: the Gaussian MGF `E exp(s W) = exp(s²/2)` at
`s = √(2t) z` (Mathlib's `mgf_fun_id_gaussianReal`) with `s²/2 = t z²`. This is the
decoupling trick in [Ver18, proof of Lemma 6.2.2] (conditioning on a Gaussian and applying
the normal MGF (2.12)). -/
lemma exp_mul_sq_eq_integral_gaussian (t : ℝ) (ht : 0 ≤ t) (z : ℝ) :
    Real.exp (t * z ^ 2) =
      ∫ g, Real.exp (Real.sqrt (2 * t) * z * g) ∂(gaussianReal 0 1) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (Real.sqrt (2 * t) * z)
  simp only [mgf, NNReal.coe_one, zero_mul, zero_add, one_mul] at h
  rw [h, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * t)]
  congr 1
  ring

/-- **Quadratic upper bound on `exp(−x)`.** For `x ≥ 0`, `exp(−x) ≤ 1 − x + x²/2`.

**Proof sketch.** `exp(−x) = 1/exp(x) ≤ 1/(1 + x + x²/2)` by Mathlib's
`Real.quadratic_le_exp_of_nonneg`, and `(1 + x + x²/2)(1 − x + x²/2) = 1 + x⁴/4 ≥ 1`. -/
lemma exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have h1 : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have h2 : (1 + x + x ^ 2 / 2) * (1 - x + x ^ 2 / 2) ≤ Real.exp x * (1 - x + x ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hq h1
  have h3 : (1 + x + x ^ 2 / 2) * (1 - x + x ^ 2 / 2) = 1 + x ^ 4 / 4 := by ring
  rw [h3] at h2
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀' (Real.exp_pos x)]
  nlinarith [pow_nonneg hx 4]

/-- **Exponential moment of `Z²` for a strictly sub-Gaussian `Z`** (positive side).
If `Z` is strictly sub-Gaussian with variance proxy `σ²` (MGF at most `exp(σ²s²/2)` for all
`s`), then for `0 ≤ t` with `2σ²t < 1`, `exp(t Z²)` is integrable and
`E exp(t Z²) ≤ 1/√(1 − 2σ²t)` — the same bound as for `Z ~ N(0, σ²)`
([Ver18, proof of Lemma 6.2.2], Gaussian decoupling: condition on a Gaussian and apply
the normal MGF (2.12)).

**Proof sketch.** Step 1: decouple pointwise, `exp(t Z²) = ∫ exp(√(2t) Z g) dN(0,1)(g)`
(`exp_mul_sq_eq_integral_gaussian`). Step 2: pass to `lintegral`s of the nonnegative kernel
and swap the two integrals by Tonelli (`lintegral_lintegral_swap`). Step 3: for fixed `g`
the inner integral is `mgf Z μ (√(2t) g) ≤ exp(σ² t g²)`. Step 4: the outer Gaussian
integral `∫ exp(σ²t g²) dN(0,1)` equals `1/√(1 − 2σ²t)`
(`integral_exp_mul_sq_gaussianReal_zero`). Step 5: finiteness of the `lintegral` gives
integrability, and `toReal` of the bound gives the integral estimate. -/
lemma integral_exp_mul_sq_le_of_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (σ_sq : ℝ)
    (hZ_subG : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        mgf Z μ t ≤ Real.exp (σ_sq * t ^ 2 / 2))
    (t : ℝ) (ht : 0 ≤ t) (ht_lt : 2 * σ_sq * t < 1) :
    Integrable (fun ω => Real.exp (t * Z ω ^ 2)) μ ∧
      ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ ≤ 1 / Real.sqrt (1 - 2 * σ_sq * t) := by
  -- Step 1: pointwise Gaussian decoupling of the integrand.
  have h_decouple : ∀ ω, Real.exp (t * Z ω ^ 2) =
      ∫ g, Real.exp (Real.sqrt (2 * t) * Z ω * g) ∂(gaussianReal 0 1) := fun ω =>
    exp_mul_sq_eq_integral_gaussian t ht (Z ω)
  have hF_meas : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (Real.sqrt (2 * t) * Z p.1 * p.2))) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_const.mul (hZ_meas.comp measurable_fst)).mul measurable_snd).exp)
  -- Step 2: the `lintegral` of the integrand as an iterated `lintegral`, integrals swapped.
  have h_lint_eq : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Z ω ^ 2)) ∂μ =
      ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.sqrt (2 * t) * Z ω * g)) ∂μ
        ∂(gaussianReal 0 1) := by
    have h1 : ∀ ω, ENNReal.ofReal (Real.exp (t * Z ω ^ 2)) =
        ∫⁻ g, ENNReal.ofReal (Real.exp (Real.sqrt (2 * t) * Z ω * g))
          ∂(gaussianReal 0 1) := by
      intro ω
      rw [h_decouple ω]
      exact ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _)
        (ae_of_all _ fun g => (Real.exp_pos _).le)
    simp_rw [h1]
    exact lintegral_lintegral_swap hF_meas.aemeasurable
  -- Step 3: for fixed `g`, the inner integral is `mgf Z μ (√(2t) g) ≤ exp(σ² t g²)`.
  have h_inner : ∀ g : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.sqrt (2 * t) * Z ω * g)) ∂μ ≤
        ENNReal.ofReal (Real.exp (σ_sq * t * g ^ 2)) := by
    intro g
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Real.sqrt (2 * t) * Z ω * g)) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (Real.exp ((Real.sqrt (2 * t) * g) * Z ω)) ∂μ := by
          congr 1
          funext ω
          congr 2
          ring
      _ = ENNReal.ofReal (mgf Z μ (Real.sqrt (2 * t) * g)) := by
          rw [mgf, ofReal_integral_eq_lintegral_ofReal (hZ_subG _).1
            (ae_of_all _ fun ω => (Real.exp_pos _).le)]
      _ ≤ ENNReal.ofReal (Real.exp (σ_sq * (Real.sqrt (2 * t) * g) ^ 2 / 2)) :=
          ENNReal.ofReal_le_ofReal (hZ_subG _).2
      _ = ENNReal.ofReal (Real.exp (σ_sq * t * g ^ 2)) := by
          congr 2
          rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * t)]
          ring
  -- Step 4: the outer Gaussian integral in closed form.
  have hσt : 2 * (σ_sq * t) * ((1 : ℝ≥0) : ℝ) < 1 := by
    rw [NNReal.coe_one, mul_one, ← mul_assoc]
    exact ht_lt
  have h_outer : ∫⁻ g, ENNReal.ofReal (Real.exp (σ_sq * t * g ^ 2)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * σ_sq * t)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_sq_gaussianReal_zero 1 one_ne_zero (σ_sq * t) hσt)
      (ae_of_all _ fun g => (Real.exp_pos _).le)]
    rw [integral_exp_mul_sq_gaussianReal_zero 1 one_ne_zero (σ_sq * t) hσt]
    congr 1
    rw [NNReal.coe_one, mul_one, mul_assoc]
  have h_bound : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Z ω ^ 2)) ∂μ ≤
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * σ_sq * t)) := by
    rw [h_lint_eq, ← h_outer]
    exact lintegral_mono fun g => h_inner g
  -- Step 5: finiteness gives integrability; `toReal` of the bound gives the estimate.
  have h_nonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (t * Z ω ^ 2) :=
    ae_of_all _ fun ω => (Real.exp_pos _).le
  have h_meas : AEStronglyMeasurable (fun ω => Real.exp (t * Z ω ^ 2)) μ :=
    ((measurable_const.mul (hZ_meas.pow_const 2)).exp).aestronglyMeasurable
  have h_int : Integrable (fun ω => Real.exp (t * Z ω ^ 2)) μ := by
    refine ⟨h_meas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal h_nonneg]
    exact lt_of_le_of_lt h_bound ENNReal.ofReal_lt_top
  refine ⟨h_int, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h_nonneg h_meas]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h_bound

/-- **Fourth-moment bound for a strictly sub-Gaussian `Z`.** If `Z` is strictly
sub-Gaussian with variance proxy `σ²` and `E Z² = σ²`, then `Z⁴` is integrable and
`E Z⁴ ≤ 4σ⁴` (the Gaussian value is `3σ⁴`; cf. [Ver18, Prop 2.5.2]).

**Proof sketch.** Step 1: apply `integral_exp_mul_sq_le_of_subgaussian` at
`t₀ = 1/(8σ²)`, so `2σ²t₀ = 1/4` and `E exp(t₀ Z²) ≤ 1/√(3/4) ≤ 1.155`. Step 2: the
pointwise bound `1 + x + x²/2 ≤ exp(x)` at `x = t₀ Z²` gives
`Z⁴ ≤ (2/t₀²) exp(t₀ Z²)`, hence integrability. Step 3: integrate the pointwise bound:
`1 + t₀σ² + t₀² E Z⁴/2 ≤ 1.155`, i.e. `E Z⁴ ≤ 128 · 0.03 · σ⁴ = 3.84σ⁴ ≤ 4σ⁴`.
-/
lemma integral_pow_four_le_of_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (σ_sq : ℝ) (hσ_pos : 0 < σ_sq)
    (hZ_subG : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        mgf Z μ t ≤ Real.exp (σ_sq * t ^ 2 / 2))
    (hZ_var : ∫ ω, (Z ω) ^ 2 ∂μ = σ_sq) :
    Integrable (fun ω => Z ω ^ 4) μ ∧ ∫ ω, Z ω ^ 4 ∂μ ≤ 4 * σ_sq ^ 2 := by
  -- Step 1: exponential-moment bound at `t₀ = 1/(8σ²)`, where `2σ²t₀ = 1/4`.
  have ht₀_pos : 0 < 1 / (8 * σ_sq) := by positivity
  have hσt₀ : σ_sq * (1 / (8 * σ_sq)) = 1 / 8 := by
    field_simp
  have ht₀_lt : 2 * σ_sq * (1 / (8 * σ_sq)) < 1 := by
    rw [mul_assoc, hσt₀]
    norm_num
  obtain ⟨h_int_exp, h_exp_le⟩ :=
    integral_exp_mul_sq_le_of_subgaussian μ Z hZ_meas σ_sq hZ_subG (1 / (8 * σ_sq))
      ht₀_pos.le ht₀_lt
  have h_exp_le' : ∫ ω, Real.exp (1 / (8 * σ_sq) * Z ω ^ 2) ∂μ ≤ 231 / 200 := by
    refine h_exp_le.trans ?_
    rw [mul_assoc, hσt₀, show (1 : ℝ) - 2 * (1 / 8) = 3 / 4 by norm_num]
    have h34 : (200 / 231 : ℝ) ≤ Real.sqrt (3 / 4) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    calc (1 : ℝ) = 231 / 200 * (200 / 231) := by norm_num
      _ ≤ 231 / 200 * Real.sqrt (3 / 4) := by gcongr
  -- Step 2: pointwise `1 + t₀ Z² + t₀² Z⁴/2 ≤ exp(t₀ Z²)`, hence `Z⁴` is integrable.
  have h_pt : ∀ ω, 1 + 1 / (8 * σ_sq) * Z ω ^ 2 + (1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4 / 2 ≤
      Real.exp (1 / (8 * σ_sq) * Z ω ^ 2) := by
    intro ω
    have h := Real.quadratic_le_exp_of_nonneg
      (show 0 ≤ 1 / (8 * σ_sq) * Z ω ^ 2 by positivity)
    calc 1 + 1 / (8 * σ_sq) * Z ω ^ 2 + (1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4 / 2
        = 1 + 1 / (8 * σ_sq) * Z ω ^ 2 + (1 / (8 * σ_sq) * Z ω ^ 2) ^ 2 / 2 := by ring
      _ ≤ Real.exp (1 / (8 * σ_sq) * Z ω ^ 2) := h
  have h_int_sq : Integrable (fun ω => Z ω ^ 2) μ := by
    by_contra h
    rw [integral_undef h] at hZ_var
    linarith
  have h_int_four : Integrable (fun ω => Z ω ^ 4) μ := by
    refine Integrable.mono' (h_int_exp.const_mul (2 / (1 / (8 * σ_sq)) ^ 2))
      (hZ_meas.pow_const 4).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hq : (1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4 ≤ 2 * Real.exp (1 / (8 * σ_sq) * Z ω ^ 2) := by
      linarith [h_pt ω, mul_nonneg ht₀_pos.le (sq_nonneg (Z ω))]
    have ht₀sq : 0 < (1 / (8 * σ_sq)) ^ 2 := by positivity
    calc Z ω ^ 4 = ((1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4) / (1 / (8 * σ_sq)) ^ 2 := by
          rw [eq_div_iff ht₀sq.ne']
          ring
      _ ≤ (2 * Real.exp (1 / (8 * σ_sq) * Z ω ^ 2)) / (1 / (8 * σ_sq)) ^ 2 := by gcongr
      _ = 2 / (1 / (8 * σ_sq)) ^ 2 * Real.exp (1 / (8 * σ_sq) * Z ω ^ 2) := by ring
  -- Step 3: integrate the pointwise bound and solve for `E Z⁴`.
  have h_int_lin : Integrable (fun ω => 1 + 1 / (8 * σ_sq) * Z ω ^ 2) μ :=
    (integrable_const 1).add (h_int_sq.const_mul _)
  have h_int_quart : Integrable (fun ω => (1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4 / 2) μ :=
    (h_int_four.const_mul _).div_const 2
  have h_int_ineq :
      ∫ ω, (1 + 1 / (8 * σ_sq) * Z ω ^ 2 + (1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4 / 2) ∂μ ≤
        ∫ ω, Real.exp (1 / (8 * σ_sq) * Z ω ^ 2) ∂μ :=
    integral_mono (h_int_lin.add h_int_quart) h_int_exp h_pt
  have h_lhs_eq :
      ∫ ω, (1 + 1 / (8 * σ_sq) * Z ω ^ 2 + (1 / (8 * σ_sq)) ^ 2 * Z ω ^ 4 / 2) ∂μ =
        1 + 1 / (8 * σ_sq) * σ_sq + (1 / (8 * σ_sq)) ^ 2 * (∫ ω, Z ω ^ 4 ∂μ) / 2 := by
    rw [integral_add h_int_lin h_int_quart, integral_add (integrable_const 1)
      (h_int_sq.const_mul _), integral_const, integral_const_mul, integral_div,
      integral_const_mul, hZ_var]
    simp
  have h_key : (1 / (8 * σ_sq)) ^ 2 * (∫ ω, Z ω ^ 4 ∂μ) ≤ 3 / 50 := by
    have h := h_lhs_eq ▸ h_int_ineq.trans h_exp_le'
    rw [mul_comm (1 / (8 * σ_sq)) σ_sq, hσt₀] at h
    linarith
  have h64 : (1 / (8 * σ_sq)) ^ 2 * (64 * σ_sq ^ 2) = 1 := by
    field_simp
    norm_num
  refine ⟨h_int_four, ?_⟩
  calc ∫ ω, Z ω ^ 4 ∂μ
      = ((1 / (8 * σ_sq)) ^ 2 * (64 * σ_sq ^ 2)) * ∫ ω, Z ω ^ 4 ∂μ := by
        rw [h64, one_mul]
    _ = (64 * σ_sq ^ 2) * ((1 / (8 * σ_sq)) ^ 2 * ∫ ω, Z ω ^ 4 ∂μ) := by ring
    _ ≤ (64 * σ_sq ^ 2) * (3 / 50) := by gcongr
    _ ≤ 4 * σ_sq ^ 2 := by nlinarith [sq_nonneg σ_sq]

/-- **Centered-square MGF bound, nonpositive `t`.** For `−1/(4σ²) ≤ t ≤ 0`,
`exp(t(Z² − σ²))` is integrable and `mgf (Z² − σ²) μ t ≤ exp(2σ⁴t²)`.

**Proof sketch.** Write `a = −tσ² ∈ [0, 1/4]`. Step 1: pointwise
`exp(t Z²) ≤ 1 + t Z² + t² Z⁴/2` (`exp_neg_le_one_sub_add_sq_div_two` at `x = −t Z²`).
Step 2: `exp(t Z²) ≤ 1` and `exp(t(Z² − σ²)) ≤ exp(a)` are bounded measurable, hence
integrable. Step 3: integrate Step 1 using `E Z² = σ²` and the fourth-moment bound
`E Z⁴ ≤ 4σ⁴` (`integral_pow_four_le_of_subgaussian`): `E exp(t Z²) ≤ 1 − a + 2a²`.
Step 4: `mgf (Z² − σ²) μ t = exp(a) · E exp(t Z²) ≤ exp(a)(1 − a + 2a²)
≤ exp(a) exp(−a + 2a²) = exp(2a²) = exp(2σ⁴t²)` by `Real.add_one_le_exp`. -/
lemma mgf_centered_sq_le_of_nonpos
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (σ_sq : ℝ) (hσ_pos : 0 < σ_sq)
    (hZ_subG : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        mgf Z μ t ≤ Real.exp (σ_sq * t ^ 2 / 2))
    (hZ_var : ∫ ω, (Z ω) ^ 2 ∂μ = σ_sq)
    (t : ℝ) (ht_nonpos : t ≤ 0) (ht_ge : -(1 / (4 * σ_sq)) ≤ t) :
    Integrable (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) μ ∧
      mgf (fun ω => Z ω ^ 2 - σ_sq) μ t ≤ Real.exp (2 * σ_sq ^ 2 * t ^ 2) := by
  obtain ⟨h_int_four, h_four_le⟩ :=
    integral_pow_four_le_of_subgaussian μ Z hZ_meas σ_sq hσ_pos hZ_subG hZ_var
  have h_int_sq : Integrable (fun ω => Z ω ^ 2) μ := by
    by_contra h
    rw [integral_undef h] at hZ_var
    linarith
  -- The range `a = −tσ² ∈ [0, 1/4]`.
  have ha_nonneg : 0 ≤ -t * σ_sq := by nlinarith
  have ha_le : -t * σ_sq ≤ 1 / 4 := by
    have h : -t ≤ 1 / (4 * σ_sq) := by linarith
    calc -t * σ_sq ≤ 1 / (4 * σ_sq) * σ_sq := by gcongr
      _ = 1 / 4 := by field_simp
  -- Step 1: pointwise `exp(t Z²) ≤ 1 + t Z² + t² Z⁴/2`.
  have h_pt : ∀ ω, Real.exp (t * Z ω ^ 2) ≤ 1 + t * Z ω ^ 2 + t ^ 2 * Z ω ^ 4 / 2 := by
    intro ω
    have hx : 0 ≤ -(t * Z ω ^ 2) := by nlinarith [sq_nonneg (Z ω)]
    have h := exp_neg_le_one_sub_add_sq_div_two hx
    rw [neg_neg] at h
    calc Real.exp (t * Z ω ^ 2) ≤ 1 - -(t * Z ω ^ 2) + (-(t * Z ω ^ 2)) ^ 2 / 2 := h
      _ = 1 + t * Z ω ^ 2 + t ^ 2 * Z ω ^ 4 / 2 := by ring
  -- Step 2: integrability of `exp(t Z²)` (bounded by `1`) and of `exp(t(Z² − σ²))`.
  have h_meas_exp : Measurable (fun ω => Real.exp (t * Z ω ^ 2)) :=
    (measurable_const.mul (hZ_meas.pow_const 2)).exp
  have h_int_exp : Integrable (fun ω => Real.exp (t * Z ω ^ 2)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) h_meas_exp.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Z ω)])
  have h_factor : ∀ ω, Real.exp (t * (Z ω ^ 2 - σ_sq)) =
      Real.exp (-t * σ_sq) * Real.exp (t * Z ω ^ 2) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    ring
  have h_int_centered : Integrable (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) μ := by
    refine (h_int_exp.const_mul (Real.exp (-t * σ_sq))).congr (ae_of_all _ fun ω => ?_)
    exact (h_factor ω).symm
  -- Step 3: integrate the pointwise bound, using `E Z² = σ²` and `E Z⁴ ≤ 4σ⁴`.
  have h_int_lin : Integrable (fun ω => 1 + t * Z ω ^ 2) μ :=
    (integrable_const 1).add (h_int_sq.const_mul t)
  have h_int_quart : Integrable (fun ω => t ^ 2 * Z ω ^ 4 / 2) μ :=
    (h_int_four.const_mul (t ^ 2)).div_const 2
  have h_exp_le : ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ ≤
      1 + t * σ_sq + t ^ 2 * (4 * σ_sq ^ 2) / 2 := by
    calc ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ
        ≤ ∫ ω, (1 + t * Z ω ^ 2 + t ^ 2 * Z ω ^ 4 / 2) ∂μ :=
          integral_mono h_int_exp (h_int_lin.add h_int_quart) h_pt
      _ = 1 + t * σ_sq + t ^ 2 * (∫ ω, Z ω ^ 4 ∂μ) / 2 := by
          rw [integral_add h_int_lin h_int_quart, integral_add (integrable_const 1)
            (h_int_sq.const_mul t), integral_const, integral_const_mul, integral_div,
            integral_const_mul, hZ_var]
          simp
      _ ≤ 1 + t * σ_sq + t ^ 2 * (4 * σ_sq ^ 2) / 2 := by gcongr
  -- Step 4: assemble `mgf = exp(a) · E exp(t Z²) ≤ exp(a)(1 − a + 2a²) ≤ exp(2a²)`.
  refine ⟨h_int_centered, ?_⟩
  have h_mgf_eq : mgf (fun ω => Z ω ^ 2 - σ_sq) μ t =
      Real.exp (-t * σ_sq) * ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ := by
    rw [mgf]
    have h_pull : (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) =
        fun ω => Real.exp (-t * σ_sq) * Real.exp (t * Z ω ^ 2) := funext h_factor
    rw [h_pull, integral_const_mul]
  rw [h_mgf_eq]
  have h_scalar : 1 + t * σ_sq + t ^ 2 * (4 * σ_sq ^ 2) / 2 =
      1 - -t * σ_sq + 2 * (-t * σ_sq) ^ 2 := by ring
  calc Real.exp (-t * σ_sq) * ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ
      ≤ Real.exp (-t * σ_sq) * (1 - -t * σ_sq + 2 * (-t * σ_sq) ^ 2) := by
        rw [← h_scalar]
        exact mul_le_mul_of_nonneg_left h_exp_le (Real.exp_pos _).le
    _ ≤ Real.exp (-t * σ_sq) * Real.exp (-(-t * σ_sq) + 2 * (-t * σ_sq) ^ 2) := by
        gcongr
        linarith [Real.add_one_le_exp (-(-t * σ_sq) + 2 * (-t * σ_sq) ^ 2)]
    _ = Real.exp (2 * σ_sq ^ 2 * t ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Centered-square MGF bound, nonnegative `t`.** For `0 ≤ t ≤ 1/(4σ²)`,
`exp(t(Z² − σ²))` is integrable and `mgf (Z² − σ²) μ t ≤ exp(2σ⁴t²)`.

**Proof sketch.** Write `a = σ²t ∈ [0, 1/4]`. Step 1: `integral_exp_mul_sq_le_of_subgaussian`
gives integrability of `exp(t Z²)` and `E exp(t Z²) ≤ 1/√(1 − 2a)`. Step 2: pull out the
constant, `mgf (Z² − σ²) μ t = exp(−a) · E exp(t Z²)`. Step 3: write
`1/√(1 − 2a) = exp(−½ log(1 − 2a))` and apply the Taylor bound
`−a − ½ log(1 − 2a) ≤ 2a²` (`neg_log_one_sub_two_mul_le_two_sq`). -/
lemma mgf_centered_sq_le_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (σ_sq : ℝ) (hσ_pos : 0 < σ_sq)
    (hZ_subG : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        mgf Z μ t ≤ Real.exp (σ_sq * t ^ 2 / 2))
    (t : ℝ) (ht : 0 ≤ t) (ht_le : t ≤ 1 / (4 * σ_sq)) :
    Integrable (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) μ ∧
      mgf (fun ω => Z ω ^ 2 - σ_sq) μ t ≤ Real.exp (2 * σ_sq ^ 2 * t ^ 2) := by
  -- Step 1: the range `a = σ²t ∈ [0, 1/4]` and the exponential-moment bound.
  have ha_nonneg : 0 ≤ σ_sq * t := by positivity
  have ha_le : σ_sq * t ≤ 1 / 4 := by
    calc σ_sq * t ≤ σ_sq * (1 / (4 * σ_sq)) := by gcongr
      _ = 1 / 4 := by field_simp
  have ht_lt : 2 * σ_sq * t < 1 := by linarith
  obtain ⟨h_int_exp, h_exp_le⟩ :=
    integral_exp_mul_sq_le_of_subgaussian μ Z hZ_meas σ_sq hZ_subG t ht ht_lt
  -- Step 2: factor the constant `exp(−a)` out of the centered exponential.
  have h_factor : ∀ ω, Real.exp (t * (Z ω ^ 2 - σ_sq)) =
      Real.exp (-(σ_sq * t)) * Real.exp (t * Z ω ^ 2) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    ring
  have h_int_centered : Integrable (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) μ := by
    refine (h_int_exp.const_mul (Real.exp (-(σ_sq * t)))).congr (ae_of_all _ fun ω => ?_)
    exact (h_factor ω).symm
  have h_mgf_eq : mgf (fun ω => Z ω ^ 2 - σ_sq) μ t =
      Real.exp (-(σ_sq * t)) * ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ := by
    rw [mgf]
    have h_pull : (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) =
        fun ω => Real.exp (-(σ_sq * t)) * Real.exp (t * Z ω ^ 2) := funext h_factor
    rw [h_pull, integral_const_mul]
  refine ⟨h_int_centered, ?_⟩
  rw [h_mgf_eq]
  -- Step 3: Taylor bound `−a − ½ log(1 − 2a) ≤ 2a²` and
  -- `1/√(1 − 2a) = exp(−½ log(1 − 2a))`.
  have hs_abs : |σ_sq * t| ≤ 1 / 4 := by
    rw [abs_of_nonneg ha_nonneg]
    exact ha_le
  have h_taylor := neg_log_one_sub_two_mul_le_two_sq (σ_sq * t) hs_abs
  have h_pos : 0 < 1 - 2 * (σ_sq * t) := by linarith
  have h_inv_sqrt_exp : (1 : ℝ) / Real.sqrt (1 - 2 * (σ_sq * t)) =
      Real.exp (-(1 / 2) * Real.log (1 - 2 * (σ_sq * t))) := by
    rw [one_div, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h_pos, ← Real.exp_neg]
    congr 1
    ring
  calc Real.exp (-(σ_sq * t)) * ∫ ω, Real.exp (t * Z ω ^ 2) ∂μ
      ≤ Real.exp (-(σ_sq * t)) * (1 / Real.sqrt (1 - 2 * σ_sq * t)) :=
        mul_le_mul_of_nonneg_left h_exp_le (Real.exp_pos _).le
    _ = Real.exp (-(σ_sq * t)) * Real.exp (-(1 / 2) * Real.log (1 - 2 * (σ_sq * t))) := by
        rw [show (2 : ℝ) * σ_sq * t = 2 * (σ_sq * t) from mul_assoc _ _ _, h_inv_sqrt_exp]
    _ = Real.exp (-(σ_sq * t) + -(1 / 2) * Real.log (1 - 2 * (σ_sq * t))) := by
        rw [Real.exp_add]
    _ ≤ Real.exp (2 * (σ_sq * t) ^ 2) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = Real.exp (2 * σ_sq ^ 2 * t ^ 2) := by
        congr 1
        ring

/-- **Sub-Gaussian → sub-exponential-squared centered MGF bound**, [Ver18, Lemma 2.7.6]
(the scalar case of Hanson–Wright), in the MGF form of [Ver18, Prop 2.7.1(e)].

Let `Z` be a measurable real random variable on a probability space `(Ω, μ)` which is
*strictly sub-Gaussian* with variance proxy `σ² > 0`, i.e. `exp(t·Z)` is integrable and
the moment generating function of `Z` at `t` is at most `exp(σ²t²/2)` for **every** real
`t`, and whose second moment is exactly `σ²`. Then the centered square `Z² − σ²` has a
Bernstein-type MGF with parameters `(2σ⁴, 1/(4σ²))`: `exp(t(Z² − σ²))` is integrable and
its mean is at most `exp(2σ⁴t²)` for `|t| ≤ 1/(4σ²)`.

Deviation from the source: the constants `(2σ⁴, 1/(4σ²))` are the *Gaussian-case*
constants (those of `hasBernsteinMGF_centered_chi_squared` in
`TCSlib.LearningTheory.JohnsonLindenstrauss.ChiSquaredMGF`, generalized from variance
`1/k` to `σ²`); Lemma 2.7.6 only gives constants up to unspecified absolute factors for a
general sub-Gaussian variable. The strictly-sub-Gaussian hypothesis (Gaussian MGF envelope
for **all** `t`, exact second moment) is what makes the sharp constants provable.

**Proof sketch.** Step 1 (`exp_mul_sq_eq_integral_gaussian`, Gaussian decoupling): for
`t ≥ 0`, `exp(t z²) = ∫ exp(√(2t) z g) dN(0,1)(g)`. Step 2
(`integral_exp_mul_sq_le_of_subgaussian`): Tonelli on `μ ⊗ N(0,1)`, the sub-Gaussian
hypothesis at `√(2t) g`, and the Gaussian quadratic integral give
`E exp(t Z²) ≤ 1/√(1 − 2σ²t)` for `0 ≤ t`, `2σ²t < 1`, with integrability. Step 3
(`integral_pow_four_le_of_subgaussian`): Step 2 at `t = 1/(8σ²)` and
`1 + x + x²/2 ≤ exp x` give `E Z⁴ ≤ 4σ⁴`. Step 4 (`mgf_centered_sq_le_of_nonpos`): for
`t ≤ 0`, `exp(−x) ≤ 1 − x + x²/2` and Step 3 give `E exp(t Z²) ≤ 1 − a + 2a²` with
`a = −tσ²`, hence `mgf (Z² − σ²) μ t ≤ exp(a)(1 − a + 2a²) ≤ exp(2a²)`. Step 5
(`mgf_centered_sq_le_of_nonneg`): for `t ≥ 0`, Step 2 and the Taylor bound
`−a − ½ log(1 − 2a) ≤ 2a²` (`neg_log_one_sub_two_mul_le_two_sq`, `a = σ²t ≤ 1/4`) give
`mgf (Z² − σ²) μ t = exp(−a)/√(1 − 2a) ≤ exp(2a²)`. Step 6: assemble the two fields
of `HasBernsteinMGF` by the sign of `t`. -/
theorem subgaussian_centered_sq_bernstein
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (σ_sq : ℝ) (hσ_pos : 0 < σ_sq)
    (hZ_subG : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        mgf Z μ t ≤ Real.exp (σ_sq * t ^ 2 / 2))
    (hZ_var : ∫ ω, (Z ω) ^ 2 ∂μ = σ_sq) :
    HasBernsteinMGF (fun ω => (Z ω) ^ 2 - σ_sq) μ
      (2 * σ_sq ^ 2) (1 / (4 * σ_sq)) := by
  -- Step 6: split on the sign of `t` and combine the two one-sided bounds.
  have h_cases : ∀ t : ℝ, |t| ≤ 1 / (4 * σ_sq) →
      Integrable (fun ω => Real.exp (t * (Z ω ^ 2 - σ_sq))) μ ∧
        mgf (fun ω => Z ω ^ 2 - σ_sq) μ t ≤ Real.exp (2 * σ_sq ^ 2 * t ^ 2) := by
    intro t ht
    obtain ⟨ht_ge, ht_le⟩ := abs_le.mp ht
    rcases le_or_gt 0 t with h | h
    · exact mgf_centered_sq_le_of_nonneg μ Z hZ_meas σ_sq hσ_pos hZ_subG t h ht_le
    · exact mgf_centered_sq_le_of_nonpos μ Z hZ_meas σ_sq hσ_pos hZ_subG hZ_var t h.le ht_ge
  exact ⟨fun t ht => (h_cases t ht).1, fun t ht => (h_cases t ht).2⟩

/-! ## (Note) Gaussian specialization: `(Ax)_i` for Gaussian matrix

For `Y ~ N(0, σ²)` the conclusion of `subgaussian_centered_sq_bernstein` is also
available directly from the closed-form Gaussian computation
(`centered_chi_squared_step` / `hasBernsteinMGF_centered_chi_squared` in
`TCSlib.LearningTheory.JohnsonLindenstrauss.ChiSquaredMGF`, stated there for variance
`1/k`). The general theorem above reproduces exactly those Gaussian-case constants for
every strictly sub-Gaussian `Z`, e.g. Rademacher row projections. -/

/-! ## §2. Distribution-agnostic JL concentration

Given the sub-Gaussian → sub-exponential-squared bound
`subgaussian_centered_sq_bernstein` (or, in the Gaussian case, the chi-squared analogue),
`jl_concentration_single_via_bernstein` in
`TCSlib.LearningTheory.JohnsonLindenstrauss.ConcentrationBound` immediately gives the
JL concentration bound.

For a matrix `A` with sub-Gaussian rows of variance `‖x‖²/k`:

  ℙ[ ε ‖x‖² < |‖A x‖² − ‖x‖²| ] ≤ 2 · exp(−ε² k / 8)

— the standard JL bound, identical for Gaussian and Rademacher inputs.

The theorem statement and proof mirror `jl_concentration_single_via_chi_squared`, with
sub-Gaussian + variance hypotheses replacing the explicit Gaussian-law hypothesis. -/

/-- **Distribution-agnostic JL single-vector concentration.**

Let `A` be a random `k × d` matrix (`k > 0`) and `x ≠ 0` a fixed vector such that the
row-projections `(Ax)_i` are measurable, mutually independent, each strictly
sub-Gaussian with variance proxy `‖x‖²/k` (MGF at most `exp((‖x‖²/k) t²/2)` for all
`t`), and each with second moment exactly `‖x‖²/k`. Then for every `0 < ε < 1`,

  ℙ[ ε ‖x‖² < |‖A x‖² − ‖x‖²| ] ≤ 2 · exp(−ε² k / 8).

This is the sub-Gaussian JL concentration of [Ach03, Thm 1.1], in the form of
[DG03, Lemma 2.2]. Deviation from the sources: the statement is distribution-agnostic
(hypotheses on the row projections only, rather than on `±1` or Gaussian entries), the
exponent is `kε²/8` for both distributions (Achlioptas obtains
`2 exp(−(ε²/2 − ε³/3) k/2)` for the `±1` case). The proof is complete: it relies on the
fully proved `subgaussian_centered_sq_bernstein` and on no project-local axioms. In
particular, applying it to a Rademacher matrix (where `(Ax)_i = (1/√k) Σⱼ εᵢⱼ xⱼ` is
Hoeffding sub-Gaussian with variance `‖x‖²/k`) recovers Achlioptas's `±1`-entries variant
of JL with the same constants as Dasgupta–Gupta.

**Proof sketch.** Step 1: by `subgaussian_centered_sq_bernstein`, each centered
row-square `((Ax)_i)² − ‖x‖²/k` has a Bernstein-type MGF with parameters
`(c, tmax) = (2(‖x‖²/k)², 1/(4‖x‖²/k))`. Step 2: the threshold `s = ε‖x‖²` lies in the
admissible range, since `2k·c·tmax = ‖x‖²` and `ε ≤ 1`. Step 3: apply the abstract bound
`jl_concentration_single_via_bernstein`, giving `2·exp(−s²/(4kc))`. Step 4: the exponent
`−ε²‖x‖⁴/(4k · 2(‖x‖²/k)²)` simplifies to `−kε²/8`. -/
theorem jl_concentration_single_subgaussian (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0)
    (h_proj_meas : ∀ i, Measurable (fun ω => (A ω).toEuclideanLin x i))
    (h_proj_indep : iIndepFun (fun (i : Fin k) ω => (A ω).toEuclideanLin x i) μ)
    (h_proj_subG : ∀ i, ∀ t : ℝ,
        Integrable (fun ω => Real.exp (t * (A ω).toEuclideanLin x i)) μ ∧
        mgf (fun ω => (A ω).toEuclideanLin x i) μ t ≤
          Real.exp ((‖x‖ ^ 2 / k) * t ^ 2 / 2))
    (h_proj_var : ∀ i, ∫ ω, ((A ω).toEuclideanLin x i) ^ 2 ∂μ = ‖x‖ ^ 2 / k)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (μ {ω | ε * ‖x‖ ^ 2 < |‖(A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  classical
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_norm_sq_pos : 0 < ‖x‖ ^ 2 := by positivity
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hσ_pos : 0 < ‖x‖ ^ 2 / k := by positivity
  -- Step 1: derive Bernstein MGF for centered row-square via the sub-Gaussian →
  -- sub-exp-sq bound `subgaussian_centered_sq_bernstein`.
  have h_bern : ∀ i, HasBernsteinMGF
      (fun ω => ((A ω).toEuclideanLin x i) ^ 2 - ‖x‖ ^ 2 / k) μ
      (2 * (‖x‖ ^ 2 / k) ^ 2) (1 / (4 * (‖x‖ ^ 2 / k))) := fun i =>
    subgaussian_centered_sq_bernstein μ
      (fun ω => (A ω).toEuclideanLin x i) (h_proj_meas i)
      (‖x‖ ^ 2 / k) hσ_pos (h_proj_subG i) (h_proj_var i)
  -- Step 2: the threshold `s = ε‖x‖²` lies in the admissible range `s ≤ 2k·c·tmax`.
  set s : ℝ := ε * ‖x‖ ^ 2 with hs_def
  have hs_pos : 0 ≤ s := by positivity
  have h_2c_tmax_eq : 2 * (k : ℝ) * (2 * (‖x‖ ^ 2 / k) ^ 2) * (1 / (4 * (‖x‖ ^ 2 / k))) =
      ‖x‖ ^ 2 := by
    have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
    have hxn_ne : (‖x‖ ^ 2 / k) ≠ 0 := by positivity
    field_simp
    ring
  have hs_le : s ≤ 2 * (k : ℝ) * (2 * (‖x‖ ^ 2 / k) ^ 2) * (1 / (4 * (‖x‖ ^ 2 / k))) := by
    rw [h_2c_tmax_eq, hs_def]
    have : ε * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right hε_lt.le
      positivity
    linarith
  -- Step 3: apply the abstract distribution-agnostic JL concentration.
  have h_concentration := jl_concentration_single_via_bernstein hk_pos μ A x
    h_proj_meas h_proj_indep _ _ (by positivity) h_bern s hs_pos hs_le
  -- Step 4: match the exponent:
  -- -s²/(4 k c) = -ε² ‖x‖⁴ / (4 k · 2 (‖x‖²/k)²) = -ε² k / 8.
  refine le_trans h_concentration ?_
  apply le_of_eq
  congr 2
  have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
  have hxn_pos : 0 < ‖x‖ ^ 2 := hx_norm_sq_pos
  have hxn_ne : (‖x‖ ^ 2 : ℝ) ≠ 0 := hxn_pos.ne'
  rw [hs_def]
  field_simp
  ring

end JLSubGaussian
