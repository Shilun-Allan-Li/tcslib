/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Real
import TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein

/-!
# Chi-Squared MGF Bound for the Johnson–Lindenstrauss Random Projection

## Main definitions

- (none; this file contains only auxiliary lemmas and theorems)

## Main results

- `centered_chi_squared_step`: Gaussian quadratic MGF closed form plus Taylor bound for one
  summand
- `hasBernsteinMGF_centered_chi_squared`: packages the chi-squared MGF bound into the
  Bernstein form
- `chi_squared_tail`: ℙ[|Σ Yᵢ² − 1| > ε] ≤ 2 exp(−k ε² / 8) for Yᵢ ~ N(0, 1/k) i.i.d.

The lemmas `neg_log_one_sub_two_mul_le_two_sq` (Taylor bound on the centered chi-squared
log-MGF), `integral_exp_mul_sq_gaussianReal_zero` and `integrable_exp_mul_sq_gaussianReal_zero`
(Gaussian quadratic MGF closed form and integrability) are the analytic ingredients of
`centered_chi_squared_step`; they are public because `SubGaussian.lean` reuses them to prove
`subgaussian_centered_sq_bernstein`. The remaining `integral_exp_mul_sq_standardGaussian`
helper stays private.

## References

* [DG03] S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and
  Lindenstrauss", *Random Structures & Algorithms* 22(1):60–65, 2003.
* [LM00] B. Laurent, P. Massart, "Adaptive estimation of a quadratic functional by model
  selection", *Ann. Statist.* 28(5):1302–1338, 2000.
* [Ver18] R. Vershynin, *High-Dimensional Probability: An Introduction with Applications in
  Data Science*, Cambridge University Press, 2018.

Original formalization by Ganesh Sankar.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section JLConcentration

variable {d k : ℕ}

/-! ## Step 5: The chi-squared tail bound

The genuinely analytic fact at the heart of the JL argument. We prove the
**centered chi-squared MGF bound** at the level of a single
`Y ~ N(0, 1/k)` random variable, and derive the iid-sum tail bound from
there using Mathlib's standard MGF + Chernoff infrastructure.

**The key step** (`centered_chi_squared_step`).
For `Y ~ N(0, 1/k)`, the MGF of `Y² − 1/k` (the centered scaled chi-square
summand with one degree of freedom) is bounded by `exp(2 t² / k²)` for
`|t| ≤ k/4`:

  𝔼[exp(t(Y² − 1/k))] ≤ exp(2 t² / k²)

with `Integrable` of the integrand on the same range.

**Proof outline.** Compute the Gaussian quadratic MGF in closed form using
`integral_gaussianReal_eq_integral_smul` + `integral_gaussian` (this is
`integral_exp_mul_sq_gaussianReal_zero` below):
  `∫ exp(s y²) ∂(gaussianReal 0 v) = 1/√(1 − 2 s v)` for `2 s v < 1`.
Then `E[exp(t(Y² − 1/k))] = exp(−t/k) · 1/√(1 − 2 t/k)`. Apply the Taylor
inequality `−s − (1/2) log(1 − 2 s) ≤ 2 s²` for `|s| ≤ 1/4` (proved as
`neg_log_one_sub_two_mul_le_two_sq` below) to `s := t/k` to get
`exp(−t/k) · (1 − 2 t/k)^{−1/2} ≤ exp(2 (t/k)²) = exp(2 t² / k²)`. -/

/-! ### Step 5a: Taylor bound on the centered chi-squared log-MGF

The key real-analytic ingredient. Setting `u := 2s`, we prove
`u² + u + log(1 − u) ≥ 0` for `|u| ≤ 1/2`. This is equivalent to
`2 s² + s + (1/2) log(1 − 2 s) ≥ 0` for `|s| ≤ 1/4`, which is the bound
`−s − (1/2)log(1 − 2 s) ≤ 2 s²` underlying the centered chi-squared MGF
bound. The proof is a classical derivative argument:
`h(u) := u² + u + log(1−u)` has `h(0) = 0`, `h'(u) = u(1−2u)/(1−u)` which
is `≥ 0` on `[0, 1/2]` and `≤ 0` on `[−1/2, 0]`. -/

/-- For `u < 1`, the auxiliary function `h(x) = x² + x + log(1 − x)` is differentiable at
`u` with derivative `u(1 − 2u)/(1 − u)`. -/
private lemma taylorAux_hasDerivAt (u : ℝ) (hu : u < 1) :
    HasDerivAt (fun x : ℝ => x ^ 2 + x + Real.log (1 - x))
      (u * (1 - 2 * u) / (1 - u)) u := by
  have hne : (1 - u : ℝ) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u)
  have h2 : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  have h3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u :=
    (hasDerivAt_id u).const_sub 1
  have h4 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - u)) u :=
    h3.log hne
  have h5 := (h1.add h2).add h4
  -- Sum derivative: 2u + 1 + (-1/(1-u))
  -- Goal: 2u + 1 + (-1)/(1-u) = u(1-2u)/(1-u)
  convert h5 using 1
  field_simp
  ring

/-- The auxiliary function `h(x) = x² + x + log(1 − x)` vanishes at `x = 0`. -/
private lemma taylorAux_zero : ((0 : ℝ) ^ 2 + (0 : ℝ) + Real.log (1 - (0 : ℝ))) = 0 := by
  simp

/-- **Taylor bound** for the centered chi-squared log-MGF: for every real `s` with
`|s| ≤ 1/4`, `−s − (1/2) log(1 − 2s) ≤ 2s²`. This is the log-MGF estimate in
[LM00, proof of Lemma 1].

Deviation from the source: Laurent–Massart prove `−s − ½ log(1 − 2s) ≤ s²/(1 − 2s)` for
`0 ≤ s < 1/2`; we restrict to `|s| ≤ 1/4`, where `s²/(1 − 2s) ≤ 2s²`, and also cover
negative `s` (needed for the two-sided Bernstein bound).

**Proof sketch.** Substitute `u = 2s`, so `|u| ≤ 1/2`, and set
`f(u) = u² + u + log(1 − u)`; the claim is `f(u) ≥ 0 = f(0)`. Step 1: `f` is continuous
on `[−1/2, 1/2]` and differentiable on its interior, with derivative `u(1 − 2u)/(1 − u)`
(`taylorAux_hasDerivAt`). Step 2: the derivative is nonnegative on `[0, 1/2]`, so `f` is
monotone there. Step 3: the derivative is nonpositive on `[−1/2, 0]`, so `f` is antitone
there. Step 4: split on the sign of `u`; in either case `f(u) ≥ f(0) = 0`
(`taylorAux_zero`). Step 5: unfold `f(2s) = 4s² + 2s + log(1 − 2s) ≥ 0` and rearrange. -/
lemma neg_log_one_sub_two_mul_le_two_sq (s : ℝ) (hs : |s| ≤ 1 / 4) :
    -s - (1/2) * Real.log (1 - 2*s) ≤ 2 * s^2 := by
  -- Equivalent: 2s² + s + (1/2) log(1-2s) ≥ 0.
  -- Set u = 2s, |u| ≤ 1/2. Want f(u) := u² + u + log(1-u) ≥ 0 = f(0).
  set f : ℝ → ℝ := fun x => x ^ 2 + x + Real.log (1 - x)
  have hf_zero : f 0 = 0 := taylorAux_zero
  have h_abs : |2*s| ≤ 1/2 := by
    rw [abs_mul]; simp only [abs_two]; linarith [abs_nonneg s]
  have h_two_s : (2*s : ℝ) ∈ Set.Icc (-(1/2 : ℝ)) (1/2) :=
    abs_le.mp h_abs
  -- Step 1: shared analytic scaffolding on the full interval `[-1/2, 1/2]`:
  -- `f` is continuous there (`1 - x > 0`) and differentiable on the interior.
  have hcont : ContinuousOn f (Set.Icc (-(1/2 : ℝ)) (1/2)) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    have h1mx : 0 < 1 - x := by linarith
    refine (continuous_pow 2).continuousAt.add ?_ |>.add ?_ |>.continuousWithinAt
    · exact continuousAt_id
    · exact (Real.continuousAt_log h1mx.ne').comp
        (continuous_const.sub continuous_id).continuousAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (-(1/2 : ℝ)) (1/2)) := by
    intro x hx
    simp only [Set.mem_Ioo] at hx
    exact (taylorAux_hasDerivAt x (by linarith)).differentiableAt.differentiableWithinAt
  -- Step 2: monotone on `[0, 1/2]`, since `f'(u) = u(1-2u)/(1-u) ≥ 0` there.
  have h_mono : MonotoneOn f (Set.Icc (0 : ℝ) (1/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact hcont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
    · rw [interior_Icc]
      exact hdiff.mono (Set.Ioo_subset_Ioo (by norm_num) le_rfl)
    · intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      rw [(taylorAux_hasDerivAt x (by linarith)).deriv]
      have h1 : 0 ≤ x := hx.1.le
      have h2 : 0 ≤ 1 - 2 * x := by linarith
      have h3 : 0 < 1 - x := by linarith
      positivity
  -- Step 3: antitone on `[-1/2, 0]`, since `f'(u) ≤ 0` there.
  have h_anti : AntitoneOn f (Set.Icc (-(1/2 : ℝ)) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact hcont.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
    · rw [interior_Icc]
      exact hdiff.mono (Set.Ioo_subset_Ioo le_rfl (by norm_num))
    · intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      rw [(taylorAux_hasDerivAt x (by linarith)).deriv]
      have h1 : x ≤ 0 := hx.2.le
      have h2 : 0 < 1 - 2 * x := by linarith
      have h3 : 0 < 1 - x := by linarith
      have h_num : x * (1 - 2 * x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2.le
      exact div_nonpos_of_nonpos_of_nonneg h_num h3.le
  -- Step 4: sign split — `f(2s) ≥ f(0) = 0` on either side of `0`.
  have h_nonneg : 0 ≤ f (2*s) := by
    by_cases h : 0 ≤ 2*s
    · -- 2s ∈ [0, 1/2]
      have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := by
        simp
      have h2s_mem : (2*s) ∈ Set.Icc (0 : ℝ) (1/2) := by
        refine ⟨h, ?_⟩
        linarith [h_two_s.2]
      have : f 0 ≤ f (2*s) := h_mono h0_mem h2s_mem h
      linarith [hf_zero]
    · -- 2s ∈ [-1/2, 0)
      push_neg at h
      have h0_mem : (0 : ℝ) ∈ Set.Icc (-(1/2 : ℝ)) 0 := by
        constructor
        · linarith
        · rfl
      have h2s_mem : (2*s) ∈ Set.Icc (-(1/2 : ℝ)) 0 := ⟨h_two_s.1, h.le⟩
      have : f 0 ≤ f (2*s) := h_anti h2s_mem h0_mem h.le
      linarith [hf_zero]
  -- Step 5: conclude — `f(2s) = 4s² + 2s + log(1-2s) ≥ 0`, divide by 2 and rearrange.
  have hf2s : f (2*s) = (2*s)^2 + 2*s + Real.log (1 - 2*s) := rfl
  have : 0 ≤ (2*s)^2 + 2*s + Real.log (1 - 2*s) := hf2s ▸ h_nonneg
  nlinarith

/-- **Standard Gaussian quadratic MGF closed form.**
For `Z ~ N(0, 1)` and every real `s` with `2s < 1`, the integral of `exp(s z²)` against
the standard Gaussian law equals `1/√(1 − 2s)`. This is the moment generating function of
a chi-squared variable with one degree of freedom, `E exp(sX²) = (1 − 2s)^{−1/2}`, used in
[DG03, proof of Lemma 2.2].

**Proof sketch.** Step 1: rewrite the integral against the Gaussian density
`(√(2π))⁻¹ exp(−z²/2)` and merge the two exponentials into
`(√(2π))⁻¹ exp(−(1/2 − s) z²)`. Step 2: pull out the constant and evaluate the Gaussian
integral `∫ exp(−b z²) = √(π/b)` with `b = 1/2 − s > 0` (Mathlib's `integral_gaussian`).
Step 3: simplify `(√(2π))⁻¹ √(π/(1/2 − s))` to `1/√(1 − 2s)` by clearing the square
roots. -/
private lemma integral_exp_mul_sq_standardGaussian
    (s : ℝ) (hs : 2 * s < 1) :
    ∫ z, Real.exp (s * z ^ 2) ∂(gaussianReal 0 1) =
      1 / Real.sqrt (1 - 2 * s) := by
  have hv1 : ((1 : ℝ≥0) : ℝ) ≠ 0 := by simp
  have hb_pos : 0 < (1 : ℝ) / 2 - s := by linarith
  -- Step 1: rewrite the integrand against the PDF.
  rw [integral_gaussianReal_eq_integral_smul (by simp : (1 : ℝ≥0) ≠ 0)]
  -- Combine the two exponentials: PDF is `(√(2π))⁻¹ exp(-z²/2)`, multiplying by `exp(s z²)`
  -- gives `(√(2π))⁻¹ exp(-(1/2 - s) z²)`.
  have h_int_eq : ∀ z : ℝ,
      gaussianPDFReal 0 1 z • Real.exp (s * z ^ 2)
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2 - s) * z ^ 2) := by
    intro z
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h_int_eq]
  -- Step 2: pull out the constant and evaluate the Gaussian integral.
  rw [integral_const_mul, integral_gaussian (1/2 - s)]
  -- Step 3: now show `(√(2π))⁻¹ * √(π / (1/2 - s)) = 1 / √(1 - 2s)`.
  -- Multiply both sides by √(2π) * √(1 - 2s) and check using sq_eq_sq.
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb_pos' : (0 : ℝ) < 1 - 2 * s := by linarith
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hdiv_pos : (0 : ℝ) < Real.pi / (1/2 - s) := div_pos hpi_pos hb_pos
  have h_sq2pi : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr h2pi_pos).ne'
  have h_sq1m2s : Real.sqrt (1 - 2 * s) ≠ 0 := (Real.sqrt_pos.mpr hb_pos').ne'
  rw [eq_div_iff h_sq1m2s]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1/2 - s)) * Real.sqrt (1 - 2*s)
        = (Real.sqrt (Real.pi / (1/2 - s)) * Real.sqrt (1 - 2*s)) / Real.sqrt (2 * Real.pi) by
      ring]
  rw [div_eq_one_iff_eq h_sq2pi]
  rw [← Real.sqrt_mul hdiv_pos.le]
  congr 1
  field_simp

/-- **Gaussian quadratic MGF closed form** for general variance.
For `Y ~ N(0, v)` with `v ≠ 0` and every real `t` with `2tv < 1`, the integral of
`exp(t y²)` against the law `N(0, v)` equals `1/√(1 − 2tv)`. This is the scaled form of
`E exp(sX²) = (1 − 2s)^{−1/2}` in [DG03, proof of Lemma 2.2].

**Proof sketch.** Step 1: `N(0, v)` is the pushforward of `N(0, 1)` under multiplication
by `√v` (Mathlib's `gaussianReal_map_const_mul`). Step 2: change variables in the
integral, so the integrand becomes `exp((tv) z²)` against `N(0, 1)`. Step 3: apply the
standard-Gaussian closed form `integral_exp_mul_sq_standardGaussian` with `s = tv`
(admissible since `2tv < 1`) and match the expression. -/
lemma integral_exp_mul_sq_gaussianReal_zero
    (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    ∫ y, Real.exp (t * y ^ 2) ∂(gaussianReal 0 v) =
      1 / Real.sqrt (1 - 2 * t * (v : ℝ)) := by
  -- Step 1: push forward N(0,1) by multiplication by √v to get N(0,v).
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hv_nonneg : (0 : ℝ) ≤ (v : ℝ) := hv_pos.le
  have h_sqrt_sq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv_nonneg
  -- Identity: (gaussianReal 0 1).map (√v * ·) = gaussianReal 0 v.
  have h_map : (gaussianReal 0 1).map (fun z => Real.sqrt (v : ℝ) * z)
      = gaussianReal 0 v := by
    have := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (v : ℝ))
    simp only [mul_zero] at this
    rw [this]
    congr 1
    rw [mul_one]
    apply NNReal.coe_injective
    simp [h_sqrt_sq]
  -- Step 2: reduce the integral to one against gaussianReal 0 1.
  rw [← h_map]
  rw [integral_map]
  · -- Now integral is ∫ z, exp(t * (√v * z)²) ∂(gaussianReal 0 1).
    have h_eq : ∀ z : ℝ, Real.exp (t * (Real.sqrt (v : ℝ) * z) ^ 2)
        = Real.exp ((t * (v : ℝ)) * z ^ 2) := by
      intro z
      congr 1
      rw [mul_pow, h_sqrt_sq]
      ring
    simp_rw [h_eq]
    -- Step 3: apply variance-1 lemma with s = t * v.
    have hs : 2 * (t * (v : ℝ)) < 1 := by
      have : 2 * t * (v : ℝ) = 2 * (t * (v : ℝ)) := by ring
      linarith [ht, this]
    rw [integral_exp_mul_sq_standardGaussian (t * (v : ℝ)) hs]
    congr 2
    ring
  · exact (measurable_const.mul measurable_id).aemeasurable
  · -- AEStronglyMeasurable of fun y => exp (t * y^2) under the pushforward
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul (measurable_id.pow_const _)).exp

/-- **Integrability of `exp(t · y²)` under `gaussianReal 0 v`.** For `v ≠ 0` and every
real `t` with `2tv < 1`, the function `y ↦ exp(t y²)` is integrable with respect to the
law `N(0, v)`. This is the integrability implicit in the finiteness of
`E exp(sX²) = (1 − 2s)^{−1/2}` in [DG03, proof of Lemma 2.2].

**Proof sketch.** Step 1: write `N(0, v)` as Lebesgue measure with the Gaussian density,
so integrability against it is integrability of the density times the integrand against
Lebesgue measure. Step 2: rewrite the product pointwise as
`(√(2πv))⁻¹ exp(−(1/(2v) − t) y²)`, where `b = 1/(2v) − t > 0` by the hypothesis.
Step 3: `exp(−b y²)` is Lebesgue-integrable for `b > 0` (Mathlib's
`integrable_exp_neg_mul_sq`); transfer along the pointwise identity. -/
lemma integrable_exp_mul_sq_gaussianReal_zero
    (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    Integrable (fun y => Real.exp (t * y ^ 2)) (gaussianReal 0 v) := by
  -- Step 1: convert `gaussianReal 0 v` to `volume.withDensity (gaussianPDF 0 v)`.
  rw [gaussianReal_of_var_ne_zero _ hv]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
       (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  -- Goal: Integrable (fun y => (gaussianPDF 0 v y).toReal • exp(t y²)) volume.
  -- Rewrite the integrand as `(√(2πv))⁻¹ * exp(-(1/(2v) - t) y²)`, then use
  -- `integrable_exp_neg_mul_sq` with `b = 1/(2v) - t > 0`.
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h2v_pos : 0 < 2 * (v : ℝ) := by linarith
  have hb_pos : 0 < 1 / (2 * (v : ℝ)) - t := by
    rw [sub_pos, lt_div_iff₀ h2v_pos]; linarith
  -- Step 2: pointwise rewrite of integrand.
  have h_eq : ∀ y : ℝ, (gaussianPDF 0 v y).toReal • Real.exp (t * y ^ 2) =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * y ^ 2) := by
    intro y
    rw [toReal_gaussianPDF, gaussianPDFReal, smul_eq_mul, sub_zero, mul_assoc,
        ← Real.exp_add]
    congr 2
    field_simp
    ring
  -- Step 3: integrability of the rewritten form.
  have h_int_rewritten : Integrable (fun y =>
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * y ^ 2)) volume :=
    Integrable.const_mul (integrable_exp_neg_mul_sq hb_pos) _
  -- Transfer to original integrand via AE-equality.
  exact h_int_rewritten.congr (ae_of_all _ (fun y => (h_eq y).symm))

/-- **Centered chi-squared MGF bound.**
For a measurable real random variable `Y` on a probability space with law `N(0, 1/k)`
(`k > 0`) and every real `t` with `|t| ≤ k/4`, the function `exp(t·(Y² − 1/k))` is
integrable and the moment generating function of the centered square `Y² − 1/k` at `t` is
at most `exp(2t²/k²)`. This is the single-summand MGF estimate of
[DG03, proof of Lemma 2.2], in the sub-exponential form of [Ver18, Lemma 2.7.6]
(Gaussian case).

Deviation from the sources: the bound is stated with the explicit sub-exponential
parameters `(2/k², k/4)` (obtained from the Taylor bound on `|t/k| ≤ 1/4`) rather than
DG03's exact optimization of the closed-form MGF.

**Proof sketch.** Write `v = 1/k` and `s = t/k`, so `|s| ≤ 1/4` and `2tv = 2s < 1`.
Step 1: `exp(t y²)` is integrable against `N(0, v)` (`integrable_exp_mul_sq_gaussianReal_zero`).
Step 2 (change of variables): transport this integrability along the law of `Y` to obtain
integrability of `exp(t Y²)` on `Ω`, and multiply by the constant `exp(−t/k)` to get
integrability of `exp(t(Y² − 1/k))`. Step 3: compute the MGF in closed form: pulling out
`exp(−t/k)` and changing variables to the Gaussian integral gives
`exp(−t/k) · 1/√(1 − 2s)` by `integral_exp_mul_sq_gaussianReal_zero`. Step 4: write
`1/√(1 − 2s) = exp(−½ log(1 − 2s))` and apply the Taylor inequality
`−s − ½ log(1 − 2s) ≤ 2s²` (`neg_log_one_sub_two_mul_le_two_sq`) to bound the product by
`exp(2s²) = exp(2t²/k²)`. -/
theorem centered_chi_squared_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 0 < k)
    (Y : Ω → ℝ) (hY_meas : Measurable Y)
    (hY_law : Measure.map Y μ = gaussianReal 0 ⟨1 / k, by positivity⟩)
    (t : ℝ) (ht : |t| ≤ (k : ℝ) / 4) :
    Integrable (fun ω => Real.exp (t * ((Y ω) ^ 2 - 1 / k))) μ ∧
    mgf (fun ω => (Y ω) ^ 2 - 1 / k) μ t ≤ Real.exp (2 * t ^ 2 / k ^ 2) := by
  -- Setup positivity / range facts.
  have hk_real_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
  set v : ℝ≥0 := ⟨1 / k, by positivity⟩ with hv_def
  have hv_real : (v : ℝ) = 1 / k := rfl
  have hv_pos : (0 : ℝ) < (v : ℝ) := by rw [hv_real]; positivity
  have hv_ne : v ≠ 0 := fun h => by
    rw [h] at hv_pos
    exact (lt_irrefl 0) (by exact_mod_cast hv_pos)
  -- `2tv < 1`: with `v = 1/k` and `|t| ≤ k/4`, `2tv = 2t/k ≤ 1/2 < 1`.
  have h_2tv_lt : 2 * t * (v : ℝ) < 1 := by
    rw [hv_real]
    have habs : t ≤ k/4 := (abs_le.mp ht).2
    rw [show (2 : ℝ) * t * (1/k) = 2*t/k from by field_simp]
    rw [div_lt_iff₀ hk_real_pos]
    nlinarith
  -- Step 1: `Integrable (exp(t y²)) (gaussianReal 0 v)`.
  have h_int_quad : Integrable (fun y => Real.exp (t * y ^ 2)) (gaussianReal 0 v) :=
    integrable_exp_mul_sq_gaussianReal_zero v hv_ne t h_2tv_lt
  -- Step 2: transfer integrability to Ω via change of variables (using `hY_law`).
  have h_int_pull : Integrable (fun ω => Real.exp (t * (Y ω) ^ 2)) μ := by
    have h_meas_quad : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (t * y ^ 2)) (μ.map Y) := by
      rw [hY_law]; exact h_int_quad.aestronglyMeasurable
    rw [show (fun ω => Real.exp (t * (Y ω) ^ 2)) =
        (fun y : ℝ => Real.exp (t * y ^ 2)) ∘ Y from rfl]
    rw [← MeasureTheory.integrable_map_measure h_meas_quad hY_meas.aemeasurable]
    rw [hY_law]; exact h_int_quad
  -- Multiply by exp(-t/k) to get integrability of `exp(t · (Y² - 1/k))`.
  have h_eq_pointwise : ∀ ω, Real.exp (t * ((Y ω) ^ 2 - 1 / k)) =
      Real.exp (-t / k) * Real.exp (t * (Y ω) ^ 2) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h_int_centered : Integrable (fun ω => Real.exp (t * ((Y ω) ^ 2 - 1 / k))) μ := by
    have h_int_scaled : Integrable
        (fun ω => Real.exp (-t / k) * Real.exp (t * (Y ω) ^ 2)) μ :=
      h_int_pull.const_mul _
    exact h_int_scaled.congr (ae_of_all _ (fun ω => (h_eq_pointwise ω).symm))
  -- Step 3: compute MGF closed form: `mgf = exp(-t/k) · 1/√(1 - 2t/k)`.
  have h_mgf_eq : mgf (fun ω => (Y ω) ^ 2 - 1 / k) μ t =
      Real.exp (-t / k) * (1 / Real.sqrt (1 - 2 * t * (v : ℝ))) := by
    -- mgf(W) μ t = ∫ exp(t·W) dμ where W = Y² - 1/k.
    rw [mgf]
    -- ∫ exp(t · (Y² - 1/k)) = ∫ exp(-t/k) · exp(t · Y²) = exp(-t/k) · ∫ exp(t · Y²).
    have h_pull_const : (fun ω => Real.exp (t * ((Y ω) ^ 2 - 1 / k))) =
        (fun ω => Real.exp (-t / k) * Real.exp (t * (Y ω) ^ 2)) := by
      funext ω; exact h_eq_pointwise ω
    rw [h_pull_const, integral_const_mul]
    -- Now: exp(-t/k) · ∫ exp(t · Y²) dμ
    -- Pull through Y to get a Gaussian integral.
    have h_change : ∫ ω, Real.exp (t * (Y ω) ^ 2) ∂μ =
        ∫ y, Real.exp (t * y ^ 2) ∂(gaussianReal 0 v) := by
      have h_meas : AEStronglyMeasurable
          (fun y : ℝ => Real.exp (t * y ^ 2)) (μ.map Y) := by
        rw [hY_law]; exact h_int_quad.aestronglyMeasurable
      rw [← hY_law, MeasureTheory.integral_map hY_meas.aemeasurable h_meas]
    rw [h_change, integral_exp_mul_sq_gaussianReal_zero v hv_ne t h_2tv_lt]
  -- Step 4: apply Taylor inequality: `exp(-s) · 1/√(1-2s) ≤ exp(2s²)` for `|s| ≤ 1/4`
  -- (with s = t/k). Setup: s := t/k.
  have hs_abs : |t / k| ≤ 1/4 := by
    rw [abs_div, abs_of_pos hk_real_pos, div_le_iff₀ hk_real_pos]
    have : |t| ≤ k / 4 := ht
    linarith
  have h_pos : 0 < 1 - 2 * (t/k) := by
    have : t / k ≤ 1 / 4 := (abs_le.mp hs_abs).2
    linarith
  have h_sqrt_pos : 0 < Real.sqrt (1 - 2 * (t/k)) := Real.sqrt_pos.mpr h_pos
  -- Taylor bound applied to s = t/k.
  have h_taylor_log : -(t/k) - (1/2) * Real.log (1 - 2 * (t/k)) ≤ 2 * (t/k)^2 :=
    neg_log_one_sub_two_mul_le_two_sq (t/k) hs_abs
  -- Rewrite `1/√(1 - 2s) = exp(-(1/2) log(1 - 2s))` for s = t/k.
  have h_inv_sqrt_exp : (1 : ℝ) / Real.sqrt (1 - 2 * (t/k))
      = Real.exp (-(1/2) * Real.log (1 - 2 * (t/k))) := by
    rw [one_div, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h_pos, ← Real.exp_neg]
    congr 1; ring
  -- The bound: exp(-t/k) · 1/√(1-2(t/k)) ≤ exp(2(t/k)²).
  have h_bound : Real.exp (-t / k) * (1 / Real.sqrt (1 - 2 * (t/k))) ≤
      Real.exp (2 * (t/k)^2) := by
    rw [h_inv_sqrt_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (-t : ℝ)/k = -(t/k) := by ring
    rw [this]; linarith
  -- Combine integrability and MGF bound.
  refine ⟨h_int_centered, ?_⟩
  rw [h_mgf_eq]
  -- mgf form has `1/√(1 - 2 * t * v)`; we want `1/√(1 - 2 * (t/k))`.
  rw [hv_real, show (2 : ℝ) * t * (1/k) = 2 * (t/k) from by field_simp]
  -- And RHS: `2 * t² / k² = 2 * (t/k)²`.
  rw [show (2 : ℝ) * t ^ 2 / k ^ 2 = 2 * (t/k)^2 from by field_simp]
  exact h_bound

/-- **Bernstein MGF instance for the centered chi-squared summand.**
For a measurable real random variable `Y` on a probability space with law `N(0, 1/k)`
(`k > 0`), the centered square `Y² − 1/k` has a Bernstein-type MGF with parameters
`(2/k², k/4)`: `exp(t(Y² − 1/k))` is integrable and its mean is at most `exp((2/k²) t²)`
for `|t| ≤ k/4`. This is the sub-exponential property of a centered chi-squared summand,
[Ver18, Lemma 2.7.6] (Gaussian case) with the explicit constants from
[DG03, proof of Lemma 2.2]; it packages `centered_chi_squared_step` into the abstract
Bernstein form so that the sum and tail-bound machinery in
`TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein` applies uniformly to Gaussian,
Rademacher, and other sub-Gaussian families. -/
theorem hasBernsteinMGF_centered_chi_squared
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 0 < k)
    (Y : Ω → ℝ) (hY_meas : Measurable Y)
    (hY_law : Measure.map Y μ = gaussianReal 0 ⟨1 / k, by positivity⟩) :
    HasBernsteinMGF (fun ω => (Y ω) ^ 2 - 1 / k) μ (2 / (k : ℝ) ^ 2) ((k : ℝ) / 4) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (centered_chi_squared_step μ k hk Y hY_meas hY_law t ht).1
  · intro t ht
    have h := (centered_chi_squared_step μ k hk Y hY_meas hY_law t ht).2
    -- `mgf ≤ exp(2 t²/k²)`. Match `c = 2/k²`, so `c · t² = 2 t²/k²`. ✓
    convert h using 2
    ring

/-- **Chi-squared tail bound.** If `Y_1, …, Y_k` (`k > 0`) are mutually independent
measurable real random variables on a probability space, each with law `N(0, 1/k)`, then
for every `0 < ε < 1` the probability that `Σᵢ Yᵢ²` deviates from `1` by more than `ε`
is at most `2·exp(−kε²/8)`. This is the concentration of a normalized chi-squared variable
with `k` degrees of freedom, [DG03, Lemma 2.2], obtained here as an instance of
Bernstein's inequality [Ver18, Thm 2.8.1].

Deviation from the source: DG03 prove the sharper one-sided bounds
`exp(k/2 (1 − β + ln β))` for `‖Ax‖² ≤ β‖x‖²` and its mirror; we state the two-sided
bound `2 exp(−kε²/8)`, obtained via the Bernstein parameters `(2/k², k/4)` of
`hasBernsteinMGF_centered_chi_squared`.

**Proof sketch.** Step 1: form the centered summands `S_i = Y_i² − 1/k`; they are
measurable and mutually independent. Step 2: each `S_i` has a Bernstein-type MGF with
parameters `(2/k², k/4)` by `hasBernsteinMGF_centered_chi_squared`. Step 3: by
`HasBernsteinMGF.sum_of_iIndepFun` the sum `Σ S_i` has parameters `(2/k, k/4)`. Step 4:
the bad event `{ε < |Σ Y_i² − 1|}` equals `{ε < |Σ S_i|}` since `Σ S_i = Σ Y_i² − 1`.
Step 5: `ε < 1 = 2·(2/k)·(k/4)` puts `ε` in the admissible range, so the two-sided
Bernstein bound `HasBernsteinMGF.measure_abs_gt_le` gives `2·exp(−ε²/(4·(2/k)))`.
Step 6: the exponent `−ε²/(8/k)` equals `−kε²/8`. -/
lemma chi_squared_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hk_pos : 0 < k)
    (Y : Fin k → Ω → ℝ)
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_law : ∀ i, Measure.map (Y i) μ =
      gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hY_indep : iIndepFun Y μ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (μ {ω | ε < |(∑ i, (Y i ω) ^ 2) - 1|}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  -- Route through the abstract Bernstein concentration in
  -- `TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein`. The Gaussian-specific step is
  -- `centered_chi_squared_step` (packaged as `hasBernsteinMGF_centered_chi_squared`);
  -- everything else is generic Bernstein/Chernoff bookkeeping.
  classical
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_ne_zero : (k : ℝ) ≠ 0 := hk_real_pos.ne'
  -- Step 1: centered chi-squared summands `S i := Y_i² − 1/k`.
  set S : Fin k → Ω → ℝ := fun i ω => (Y i ω) ^ 2 - 1 / k with hS_def
  have hS_meas : ∀ i, Measurable (S i) := fun i =>
    ((hY_meas i).pow_const 2).sub measurable_const
  have hS_indep : iIndepFun S μ :=
    hY_indep.comp (fun _ y => y ^ 2 - 1 / (k : ℝ)) (fun _ => by fun_prop)
  -- Step 2: each `S i` has Bernstein MGF `(2/k², k/4)` via the Gaussian step.
  have hS_bern : ∀ i, HasBernsteinMGF (S i) μ (2 / (k : ℝ) ^ 2) ((k : ℝ) / 4) :=
    fun i => hasBernsteinMGF_centered_chi_squared μ k hk_pos (Y i) (hY_meas i) (hY_law i)
  -- Step 3: sum has Bernstein MGF `(k · 2/k², k/4) = (2/k, k/4)` by closure under
  -- independent sums.
  have hSum_bern : HasBernsteinMGF (fun ω => ∑ i, S i ω) μ
      (2 / (k : ℝ)) ((k : ℝ) / 4) := by
    have h := HasBernsteinMGF.sum_of_iIndepFun hS_indep hS_meas
      (s := Finset.univ) (fun i _ => hS_bern i)
    -- ∑ i ∈ univ, 2/k² = k · 2/k² = 2/k.
    convert h using 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- Step 4: bad event reduces: `ε < |Σ Y_i² − 1|  ⇔  ε < |Σ S_i|`.
  have hsum_S : ∀ ω, ∑ i, S i ω = (∑ i, (Y i ω) ^ 2) - 1 := by
    intro ω
    simp only [S, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hbad_eq : {ω | ε < |(∑ i, (Y i ω) ^ 2) - 1|}
      = {ω | ε < |∑ i, S i ω|} := by
    ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum_S]
  rw [hbad_eq]
  -- Step 5: apply abstract Bernstein concentration (`measure_abs_gt_le`).
  -- Range: `2 · (2/k) · (k/4) = 1`, and `ε < 1`, so we're in range.
  have h2c_pos : 0 < 2 / (k : ℝ) := by positivity
  have hε_le_range : ε ≤ 2 * (2 / (k : ℝ)) * ((k : ℝ) / 4) := by
    have : 2 * (2 / (k : ℝ)) * ((k : ℝ) / 4) = 1 := by field_simp; norm_num
    rw [this]; linarith
  have h_concentration := hSum_bern.measure_abs_gt_le h2c_pos ε hε_pos.le hε_le_range
  -- Step 6: the exponent: `-ε² / (4 · 2/k) = -kε² / 8`.
  refine le_trans h_concentration ?_
  apply le_of_eq
  congr 2
  field_simp
  ring

end JLConcentration
