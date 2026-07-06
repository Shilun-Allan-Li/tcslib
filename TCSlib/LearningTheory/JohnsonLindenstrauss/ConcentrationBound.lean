/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein

/-!
# Concentration Bound for the Johnson–Lindenstrauss Random Projection

## Main results

- `BadSingle`: the "bad event" for a single vector — strict distortion exceeds ε‖x‖²
- `concentration_zero`: when x = 0 the bad event is empty and the bound holds trivially
- `map_const_mul_gaussian`: scalar multiple of a centered Gaussian restatement
- `sum_scaled_iid_gaussian_map`: sum of scaled i.i.d. Gaussians is Gaussian with scaled variance
- `rows_indep`: rows of Ax are independent given independent matrix rows
- `toEuclideanLin_apply_eq_sum`: coordinate-sum form of (A.toEuclideanLin x) i
- `norm_sq_toEuclideanLin`: ‖A.toEuclideanLin x‖² as a sum of squared row entries
- `centered_chi_squared_step`: Gaussian quadratic MGF closed form plus Taylor bound for one summand
- `hasBernsteinMGF_centered_chi_squared`: packages the chi-squared MGF bound into the Bernstein form
- `chi_squared_tail`: ℙ[|Σ Yᵢ² − 1| > ε] ≤ 2 exp(−k ε² / 8) for Yᵢ ~ N(0, 1/k) i.i.d.
- `jl_concentration_single_via_chi_squared`: main JL single-vector bound via chi-squared reduction
- `jl_concentration_single_via_bernstein`: distribution-agnostic JL concentration via Bernstein tails

## References

- Original formalization by Ganesh Sankar
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section JLConcentration

variable {d k : ℕ}

/-- Matrices as `m → n → α` inherit a Pi measurable space structure. -/
instance : MeasurableSpace (Matrix (Fin k) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin d → ℝ))

/-- The "bad event" for a single vector `x` (strict inequality form).

This matches `BadSingle` in `main.lean` but we re-state it locally so this
file can be developed independently. -/
def BadSingle (ε : ℝ) (A : Matrix (Fin k) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ε * ‖x‖ ^ 2 < |‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|

/-! ## Step 1: The `x = 0` case

When `x = 0`, the bad event is empty: `ε · 0 < |0 − 0|` simplifies to
`0 < 0`, which is false. So its measure is `0`, and the bound
`0 ≤ 2 · exp(−kε²/8)` holds trivially. -/

lemma concentration_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (ε : ℝ) :
    (μ {ω | BadSingle ε (A ω) (0 : EuclideanSpace ℝ (Fin d))}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  have hempty : {ω | BadSingle ε (A ω) (0 : EuclideanSpace ℝ (Fin d))} = ∅ := by
    ext ω
    simp only [BadSingle, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_lt]
    simp [map_zero]
  rw [hempty, measure_empty, ENNReal.toReal_zero]
  positivity

/-! ## Step 2: Distribution of a single row `(Ax)_i = Σⱼ Aᵢⱼ xⱼ`

If `Aᵢⱼ ~ N(0, σ²)` i.i.d. across `j`, then `Σⱼ xⱼ · Aᵢⱼ ~ N(0, σ² · Σⱼ xⱼ²)`.

The two ingredients are `gaussianReal_map_const_mul` (scalar multiple of a
Gaussian) and `gaussianReal_add_gaussianReal_of_indepFun` (sum of two
independent Gaussians). We induct on the Finset. -/

/-- Scalar multiple of a centered Gaussian. Auxiliary restatement of
`gaussianReal_map_const_mul` that is easier to apply. -/
lemma map_const_mul_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {σ₀ : NNReal}
    (hX_meas : Measurable X)
    (hX : Measure.map X μ = gaussianReal 0 σ₀)
    (c : ℝ) :
    Measure.map (fun ω => c * X ω) μ =
      gaussianReal 0 (⟨c ^ 2, sq_nonneg _⟩ * σ₀) := by
  have : (fun ω => c * X ω) = (fun r : ℝ => c * r) ∘ X := rfl
  rw [this, ← Measure.map_map (by fun_prop) hX_meas, hX,
    gaussianReal_map_const_mul]
  simp

/-- **Row-projection is Gaussian.**

If `Y j` are i.i.d. with law `N(0, σ²)` and `x j : ℝ`, then
`∑ j ∈ s, x j · Y j ω` has law `N(0, σ² · ∑ j ∈ s, (x j)²)` under `μ`,
proved by induction on the Finset `s`. -/
lemma sum_scaled_iid_gaussian_map
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {σ₀ : NNReal}
    (hY_meas : ∀ j, Measurable (Y j))
    (hY_law : ∀ j, Measure.map (Y j) μ = gaussianReal 0 σ₀)
    (hY_indep : iIndepFun Y μ)
    (x : ι → ℝ) (s : Finset ι) :
    Measure.map (fun ω => ∑ j ∈ s, x j * Y j ω) μ =
      gaussianReal 0
        (⟨∑ j ∈ s, (x j) ^ 2,
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩ * σ₀) := by
  classical
  -- The family `Z j := x j * Y j` is iid Gaussian by `iIndepFun.comp`.
  set Z : ι → Ω → ℝ := fun j ω => x j * Y j ω with hZ_def
  have hZ_meas : ∀ j, Measurable (Z j) := fun j => (hY_meas j).const_mul (x j)
  have hZ_law : ∀ j, Measure.map (Z j) μ =
      gaussianReal 0 (⟨(x j) ^ 2, sq_nonneg _⟩ * σ₀) := fun j =>
    map_const_mul_gaussian (hY_meas j) (hY_law j) (x j)
  have hZ_indep : iIndepFun Z μ :=
    hY_indep.comp (fun j r => x j * r) (fun j => measurable_const.mul measurable_id)
  -- Induction on `s`.
  induction s using Finset.induction_on with
  | empty =>
    -- The sum is constantly 0, so its law is `Dirac 0 = gaussianReal 0 0`.
    have hLHS : (fun ω => ∑ j ∈ (∅ : Finset ι), x j * Y j ω) = (fun _ => (0 : ℝ)) := by
      funext ω; simp
    rw [hLHS, Measure.map_const, measure_univ, one_smul,
        ← gaussianReal_zero_var (0 : ℝ), gaussianReal_ext_iff]
    refine ⟨rfl, ?_⟩
    apply NNReal.eq
    push_cast
    simp
  | insert j₀ s' hj₀ ih =>
    -- Split the sum and use independence + Gaussian add.
    have hsplit : (fun ω => ∑ j ∈ insert j₀ s', x j * Y j ω) =
        (Z j₀ + ∑ j ∈ s', Z j) := by
      funext ω
      change ∑ j ∈ insert j₀ s', x j * Y j ω = Z j₀ ω + (∑ j ∈ s', Z j) ω
      rw [Finset.sum_insert hj₀, Finset.sum_apply]
    rw [hsplit]
    -- Independence between `Z j₀` and the partial sum over `s'`.
    have hindep : IndepFun (Z j₀) (∑ j ∈ s', Z j) μ :=
      (hZ_indep.indepFun_finset_sum_of_notMem hZ_meas hj₀).symm
    -- Law of the partial sum: massage the IH from the `fun ω => ...` form to the
    -- Pi-sum form `∑ j ∈ s', Z j`.
    have hpartial_eq : (fun ω => ∑ j ∈ s', x j * Y j ω) = ∑ j ∈ s', Z j := by
      funext ω
      change _ = (∑ j ∈ s', Z j) ω
      rw [Finset.sum_apply]
    rw [hpartial_eq] at ih
    -- Combine using `gaussianReal_add_gaussianReal_of_indepFun`.
    rw [gaussianReal_add_gaussianReal_of_indepFun hindep (hZ_law j₀) ih]
    -- Match the variance form. Use `gaussianReal_ext_iff` to split into mean + variance.
    rw [gaussianReal_ext_iff]
    refine ⟨by ring, ?_⟩
    apply NNReal.eq
    push_cast
    rw [Finset.sum_insert hj₀]
    ring

/-! ## Step 3: Independence of rows

Because the matrix entries `A ω i j` are jointly independent in `(i, j)`,
the rows `(A ω).toEuclideanLin x i = Σⱼ (A ω i j) · x j` (indexed by `i`)
are independent: for distinct `i₁, i₂`, they depend on disjoint
sub-families of the i.i.d. entries. -/

/-- **Rows of `Ax` are independent.** Given that the row vectors of `A` are
mutually independent as `(Fin d → ℝ)`-valued random variables, the scalar
row-projections `(A ω).toEuclideanLin x i = ∑ⱼ A ω i j · x j` are
independent across `i` — they are measurable functions of disjoint row
vectors. -/
lemma rows_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (x : EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun (i : Fin k) ω => (A ω).toEuclideanLin x i) μ := by
  -- Apply `iIndepFun.comp` with the measurable per-row scalar product
  -- `g i := fun (r : Fin d → ℝ) ↦ ∑ j, r j * x j`.
  let g : Fin k → (Fin d → ℝ) → ℝ := fun _ r => ∑ j, r j * x j
  have hg : ∀ i, Measurable (g i) := fun _ =>
    Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).mul_const _)
  -- `(g i) ∘ (fun ω j => A ω i j) = fun ω => (A ω).toEuclideanLin x i`
  -- by definition of `toEuclideanLin` (a sum).
  exact hRowsIndep.comp g hg

/-! ## Step 4: Bad event in terms of the row-squared sum

With rows `Yᵢ := (Ax) i ~ N(0, ‖x‖²/k)` i.i.d., the squared norm
`‖Ax‖² = Σᵢ Yᵢ²`. The bad event reduces to `|Σ Yᵢ² − ‖x‖²| > ε‖x‖²`. After
rescaling by `‖x‖²` (valid when `x ≠ 0`), one gets
`|Σ Zᵢ² − 1| > ε` for `Zᵢ = Yᵢ / ‖x‖ · √k` — but we avoid this explicit
rescaling in the final combination step by working with the un-normalized
variables directly and using `chi_squared_tail` with variance `‖x‖²/k`. -/

/-- The coordinate-sum form of `(A.toEuclideanLin x) i`. -/
lemma toEuclideanLin_apply_eq_sum
    (A : Matrix (Fin k) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    (A.toEuclideanLin x) i = ∑ j, A i j * x j := rfl

/-- `‖A.toEuclideanLin x‖²` as a sum of row-squared entries. -/
lemma norm_sq_toEuclideanLin
    (A : Matrix (Fin k) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖A.toEuclideanLin x‖ ^ 2 = ∑ i, ((A.toEuclideanLin x) i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity)]
  simp [sq_abs]

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

private lemma taylorAux_zero : ((0 : ℝ) ^ 2 + (0 : ℝ) + Real.log (1 - (0 : ℝ))) = 0 := by
  simp

/-- **Taylor bound** for centered chi-squared log-MGF.
For `|s| ≤ 1/4`, `−s − (1/2) log(1 − 2 s) ≤ 2 s²`. -/
private lemma neg_log_one_sub_two_mul_le_two_sq (s : ℝ) (hs : |s| ≤ 1 / 4) :
    -s - (1/2) * Real.log (1 - 2*s) ≤ 2 * s^2 := by
  -- Equivalent: 2s² + s + (1/2) log(1-2s) ≥ 0.
  -- Set u = 2s, |u| ≤ 1/2. Want u² + u + log(1-u) ≥ 0.
  set f : ℝ → ℝ := fun x => x ^ 2 + x + Real.log (1 - x)
  have hf_zero : f 0 = 0 := taylorAux_zero
  -- Derivative: f'(u) = u(1-2u)/(1-u) for u < 1.
  -- Monotone on [0, 1/2], antitone on [-1/2, 0].
  have h_abs : |2*s| ≤ 1/2 := by
    rw [abs_mul]; simp only [abs_two]; linarith [abs_nonneg s]
  have h_two_s : (2*s : ℝ) ∈ Set.Icc (-(1/2 : ℝ)) (1/2) :=
    abs_le.mp h_abs
  -- Monotonicity on [0, 1/2]: f'(u) ≥ 0.
  have h_mono : MonotoneOn f (Set.Icc (0 : ℝ) (1/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · -- continuity on [0, 1/2]: each piece continuous, log continuous since 1 - x > 0 on this set
      intro x hx
      simp only [Set.mem_Icc] at hx
      have h1mx : 0 < 1 - x := by linarith
      refine (continuous_pow 2).continuousAt.add ?_ |>.add ?_ |>.continuousWithinAt
      · exact continuousAt_id
      · exact (Real.continuousAt_log h1mx.ne').comp
          (continuous_const.sub continuous_id).continuousAt
    · -- differentiable on (0, 1/2)
      intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      exact (taylorAux_hasDerivAt x (by linarith)).differentiableAt.differentiableWithinAt
    · -- derivative ≥ 0 on (0, 1/2)
      intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      have h_deriv := (taylorAux_hasDerivAt x (by linarith)).deriv
      rw [h_deriv]
      have h1 : 0 ≤ x := hx.1.le
      have h2 : 0 ≤ 1 - 2 * x := by linarith
      have h3 : 0 < 1 - x := by linarith
      positivity
  -- Antitonicity on [-1/2, 0]: f'(u) ≤ 0.
  have h_anti : AntitoneOn f (Set.Icc (-(1/2 : ℝ)) 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro x hx
      simp only [Set.mem_Icc] at hx
      have h1mx : 0 < 1 - x := by linarith
      refine (continuous_pow 2).continuousAt.add ?_ |>.add ?_ |>.continuousWithinAt
      · exact continuousAt_id
      · exact (Real.continuousAt_log h1mx.ne').comp
          (continuous_const.sub continuous_id).continuousAt
    · intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      exact (taylorAux_hasDerivAt x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      simp only [Set.mem_Ioo] at hx
      have h_deriv := (taylorAux_hasDerivAt x (by linarith)).deriv
      rw [h_deriv]
      have h1 : x ≤ 0 := hx.2.le
      have h2 : 0 < 1 - 2 * x := by linarith
      have h3 : 0 < 1 - x := by linarith
      have h_num : x * (1 - 2 * x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2.le
      exact div_nonpos_of_nonpos_of_nonneg h_num h3.le
  -- f(2s) ≥ 0 by case analysis on sign of s.
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
  -- Translate f(2s) ≥ 0 into the desired inequality.
  -- f(2s) = (2s)² + 2s + log(1 - 2s) = 4s² + 2s + log(1-2s) ≥ 0
  -- ⟹ 2s² + s + (1/2)log(1-2s) ≥ 0 (divide by 2)
  -- ⟹ -s - (1/2)log(1-2s) ≤ 2s².
  have hf2s : f (2*s) = (2*s)^2 + 2*s + Real.log (1 - 2*s) := rfl
  have : 0 ≤ (2*s)^2 + 2*s + Real.log (1 - 2*s) := hf2s ▸ h_nonneg
  nlinarith

/-- **Standard Gaussian quadratic MGF closed form.**
For `Z ~ N(0, 1)` and `2s < 1`,
`∫ z, exp(s z²) ∂(gaussianReal 0 1) = 1 / √(1 − 2s)`. -/
private lemma integral_exp_mul_sq_standardGaussian
    (s : ℝ) (hs : 2 * s < 1) :
    ∫ z, Real.exp (s * z ^ 2) ∂(gaussianReal 0 1) =
      1 / Real.sqrt (1 - 2 * s) := by
  have hv1 : ((1 : ℝ≥0) : ℝ) ≠ 0 := by simp
  have hb_pos : 0 < (1 : ℝ) / 2 - s := by linarith
  -- Rewrite the integrand against the PDF.
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
  rw [integral_const_mul, integral_gaussian (1/2 - s)]
  -- Now show `(√(2π))⁻¹ * √(π / (1/2 - s)) = 1 / √(1 - 2s)`.
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
For `Y ~ N(0, v)` (`v ≠ 0`) and `2 t v < 1`,
`∫ y, exp(t y²) ∂(gaussianReal 0 v) = 1 / √(1 − 2 t v)`. -/
private lemma integral_exp_mul_sq_gaussianReal_zero
    (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    ∫ y, Real.exp (t * y ^ 2) ∂(gaussianReal 0 v) =
      1 / Real.sqrt (1 - 2 * t * (v : ℝ)) := by
  -- Push forward N(0,1) by multiplication by √v to get N(0,v).
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    have := v.coe_nonneg
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exfalso; apply hv; exact NNReal.coe_injective h.symm
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
  -- Reduce the integral to one against gaussianReal 0 1.
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
    -- Apply variance-1 lemma with s = t * v.
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

/-- **Integrability of `exp(t · y²)` under `gaussianReal 0 v`** for
`2 t v < 1`. -/
private lemma integrable_exp_mul_sq_gaussianReal_zero
    (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    Integrable (fun y => Real.exp (t * y ^ 2)) (gaussianReal 0 v) := by
  -- Convert `gaussianReal 0 v` to `volume.withDensity (gaussianPDF 0 v)`.
  rw [gaussianReal_of_var_ne_zero _ hv]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
       (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  -- Goal: Integrable (fun y => (gaussianPDF 0 v y).toReal • exp(t y²)) volume.
  -- Rewrite the integrand as `(√(2πv))⁻¹ * exp(-(1/(2v) - t) y²)`, then use
  -- `integrable_exp_neg_mul_sq` with `b = 1/(2v) - t > 0`.
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    have := v.coe_nonneg
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exfalso; apply hv; exact NNReal.coe_injective h.symm
  have h2v_pos : 0 < 2 * (v : ℝ) := by linarith
  have hb_pos : 0 < 1 / (2 * (v : ℝ)) - t := by
    rw [sub_pos, lt_div_iff₀ h2v_pos]; linarith
  -- Pointwise rewrite of integrand.
  have h_eq : ∀ y : ℝ, (gaussianPDF 0 v y).toReal • Real.exp (t * y ^ 2) =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * y ^ 2) := by
    intro y
    rw [toReal_gaussianPDF, gaussianPDFReal, smul_eq_mul, sub_zero, mul_assoc,
        ← Real.exp_add]
    congr 2
    field_simp
    ring
  -- Integrable of the rewritten form.
  have h_int_rewritten : Integrable (fun y =>
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (-(1 / (2 * (v : ℝ)) - t) * y ^ 2)) volume :=
    Integrable.const_mul (integrable_exp_neg_mul_sq hb_pos) _
  -- Transfer to original integrand via AE-equality.
  exact h_int_rewritten.congr (ae_of_all _ (fun y => (h_eq y).symm))

/-- **Centered chi-squared MGF bound.**
For `Y ~ N(0, 1/k)`, the MGF of `Y² − 1/k` is bounded by `exp(2 t²/k²)` for
`|t| ≤ k/4`, with integrability of `exp(t · (Y² − 1/k))` on the same range.

**Proof.** Combine
* `integral_exp_mul_sq_gaussianReal_zero` (Gaussian quadratic MGF closed
  form: `∫ exp(s y²) ∂(gaussianReal 0 v) = 1/√(1 − 2 s v)` for `2 s v < 1`);
* `integrable_exp_mul_sq_gaussianReal_zero` (integrability under the same
  range);
* `neg_log_one_sub_two_mul_le_two_sq` (Taylor inequality
  `−s − ½ log(1 − 2 s) ≤ 2 s²` for `|s| ≤ 1/4`),
applied with `s := t / k`. -/
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
  -- `Integrable (exp(t y²)) (gaussianReal 0 v)`.
  have h_int_quad : Integrable (fun y => Real.exp (t * y ^ 2)) (gaussianReal 0 v) :=
    integrable_exp_mul_sq_gaussianReal_zero v hv_ne t h_2tv_lt
  -- Transfer integrability to Ω via change of variables (using `hY_law`).
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
  -- Compute MGF closed form: `mgf = exp(-t/k) · 1/√(1 - 2t/k)`.
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
  -- Apply Taylor inequality: `exp(-s) · 1/√(1-2s) ≤ exp(2s²)` for `|s| ≤ 1/4` (with s = t/k).
  -- Setup: s := t/k.
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
For `Y ~ N(0, 1/k)` (`k > 0`), the centered summand `Y² − 1/k` has
`HasBernsteinMGF (2/k², k/4)`. This packages `centered_chi_squared_step`
into the abstract Bernstein form so that the iid-sum + tail bound machinery
in `bernstein.lean` applies uniformly to Gaussian, Rademacher, and other
sub-Gaussian families. -/
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
  -- Refactored: route through the abstract Bernstein concentration in
  -- `bernstein.lean`. The Gaussian-specific step is `centered_chi_squared_step`
  -- (now packaged as `hasBernsteinMGF_centered_chi_squared`); everything else
  -- is generic Bernstein/Chernoff bookkeeping.
  classical
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_ne_zero : (k : ℝ) ≠ 0 := hk_real_pos.ne'
  -- Centered chi-squared summands `S i := Y_i² − 1/k`.
  set S : Fin k → Ω → ℝ := fun i ω => (Y i ω) ^ 2 - 1 / k with hS_def
  have hS_meas : ∀ i, Measurable (S i) := fun i =>
    ((hY_meas i).pow_const 2).sub measurable_const
  have hS_indep : iIndepFun S μ :=
    hY_indep.comp (fun _ y => y ^ 2 - 1 / (k : ℝ)) (fun _ => by fun_prop)
  -- Each `S i` has Bernstein MGF `(2/k², k/4)` via the Gaussian step.
  have hS_bern : ∀ i, HasBernsteinMGF (S i) μ (2 / (k : ℝ) ^ 2) ((k : ℝ) / 4) :=
    fun i => hasBernsteinMGF_centered_chi_squared μ k hk_pos (Y i) (hY_meas i) (hY_law i)
  -- Sum has Bernstein MGF `(k · 2/k², k/4) = (2/k, k/4)` by iid closure.
  have hSum_bern : HasBernsteinMGF (fun ω => ∑ i, S i ω) μ
      (2 / (k : ℝ)) ((k : ℝ) / 4) := by
    have h := HasBernsteinMGF.sum_of_iIndepFun hS_indep hS_meas
      (s := Finset.univ) (fun i _ => hS_bern i)
    -- ∑ i ∈ univ, 2/k² = k · 2/k² = 2/k.
    convert h using 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- Bad event reduces: `ε < |Σ Y_i² − 1|  ⇔  ε < |Σ S_i|`.
  have hsum_S : ∀ ω, ∑ i, S i ω = (∑ i, (Y i ω) ^ 2) - 1 := by
    intro ω
    simp only [S, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hbad_eq : {ω | ε < |(∑ i, (Y i ω) ^ 2) - 1|}
      = {ω | ε < |∑ i, S i ω|} := by
    ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum_S]
  rw [hbad_eq]
  -- Apply abstract Bernstein concentration (`measure_abs_gt_le`).
  -- Range: `2 · (2/k) · (k/4) = 1`, and `ε < 1`, so we're in range.
  have h2c_pos : 0 < 2 / (k : ℝ) := by positivity
  have hε_le_range : ε ≤ 2 * (2 / (k : ℝ)) * ((k : ℝ) / 4) := by
    have : 2 * (2 / (k : ℝ)) * ((k : ℝ) / 4) = 1 := by field_simp; norm_num
    rw [this]; linarith
  have h_concentration := hSum_bern.measure_abs_gt_le h2c_pos ε hε_pos.le hε_le_range
  -- The exponent: `-ε² / (4 · 2/k) = -kε² / 8`.
  refine le_trans h_concentration ?_
  apply le_of_eq
  congr 2
  field_simp
  ring

/-! ## Step 6: Combining the pieces

The main theorem. On `x = 0` we apply `concentration_zero`. Otherwise we
use:

* `sum_scaled_iid_gaussian_map` to get `(Ax) i ~ N(0, ‖x‖²/k)`,
* `rows_indep` to get i.i.d.-ness across rows,
* then reduce the bad event to the chi-squared form and apply
  `chi_squared_tail`.

The combination matches up the events `{ω | ε ‖x‖² < |‖Ax‖² − ‖x‖²|}` and
`{ω | ε < |Σ Yᵢ² − 1|}` via the rescaling `Yᵢ = (Ax)ᵢ / ‖x‖`, and is fully
proved below. -/

/-- **Main concentration theorem** (matching `jl_concentration_single` in
`main.lean`), assuming the chi-squared tail lemma `chi_squared_tail`. -/
theorem jl_concentration_single_via_chi_squared (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (hA_law : ∀ (i : Fin k) (j : Fin d),
      Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hRowEntryIndep : ∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (x : EuclideanSpace ℝ (Fin d))
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (μ {ω | BadSingle ε (A ω) x}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  by_cases hx : x = 0
  · subst hx
    exact concentration_zero μ A ε
  -- Otherwise ‖x‖ > 0. **Outline of the remaining proof:**
  --
  -- 1. Set `Y i ω := (A ω).toEuclideanLin x i = ∑ j, A ω i j · x j`.
  --    By `sum_scaled_iid_gaussian_map` (with coefficients `x j`), each row
  --    has law `Y i ~ N(0, ‖x‖² / k)`.
  -- 2. By `rows_indep`, the family `{Y i}` is iid.
  -- 3. Define `Z i ω := Y i ω / ‖x‖`. Scalar division is measurable and
  --    applying `map_const_mul_gaussian` rescales the variance to `1/k`:
  --    `Z i ~ N(0, 1/k)`. Independence is preserved by `iIndepFun.comp`.
  -- 4. The key identity: `‖A.toEuclideanLin x ω‖² = ∑ i, (Y i ω)² =
  --    ‖x‖² · ∑ i, (Z i ω)²`, via `norm_sq_toEuclideanLin` and the
  --    definition of `Z`.
  -- 5. The bad event simplifies:
  --    `ε · ‖x‖² < |‖A.toEuclideanLin x ω‖² − ‖x‖²|`
  --       `⇔  ε · ‖x‖² < ‖x‖² · |∑ (Z i ω)² − 1|`
  --       `⇔  ε < |∑ (Z i ω)² − 1|`  (since ‖x‖² > 0).
  --    The corresponding set-level equality is then an event-wise rewrite.
  -- 6. Apply `chi_squared_tail` to `Z` with the same `ε`, getting the bound
  --    `2 · exp(-k ε² / 8)`.
  --
  -- Each step is mechanical measure-theoretic bookkeeping once steps 2–3
  -- of Section 2 (`sum_scaled_iid_gaussian_map`, `rows_indep`) are filled
  -- in. Step 5 is a purely real-analytic equivalence of sets.
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_norm_sq_pos : 0 < ‖x‖ ^ 2 := by positivity
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  -- Helper: ‖x‖² = ∑ j, (x j)²
  have hxnorm_sq : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [sq_abs]
  -- Step 1+2: Define `Y i := (A·).toEuclideanLin x i` and establish its
  -- distribution and independence.
  set Y : Fin k → Ω → ℝ :=
    fun i ω => (A ω).toEuclideanLin x i with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    have heq : Y i = fun ω => ∑ j, (A ω) i j * x j := by
      funext ω
      change (A ω).toEuclideanLin x i = ∑ j, (A ω) i j * x j
      rfl
    rw [heq]
    exact Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA_meas)).mul_const _)
  -- Each `Y i` has distribution `N(0, ‖x‖²/k)`.
  have hY_law : ∀ i, Measure.map (Y i) μ =
      gaussianReal 0 ⟨‖x‖ ^ 2 / k, by positivity⟩ := by
    intro i
    -- Apply `sum_scaled_iid_gaussian_map` to the i-th row.
    have hrow_law : ∀ j, Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩ := fun j => hA_law i j
    have hrow_meas : ∀ j, Measurable (fun ω => A ω i j) := fun j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA_meas)
    have hrow_indep : iIndepFun (fun (j : Fin d) ω => A ω i j) μ := hRowEntryIndep i
    have hY_eq : Y i = fun ω => ∑ j, x j * (A ω i j) := by
      funext ω
      change (A ω).toEuclideanLin x i = _
      rw [toEuclideanLin_apply_eq_sum]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [hY_eq]
    have := sum_scaled_iid_gaussian_map (Y := fun j ω => A ω i j)
      hrow_meas hrow_law hrow_indep x Finset.univ
    rw [this]
    -- Match the variance: ⟨∑j, (x j)², _⟩ * ⟨1/k, _⟩ = ⟨‖x‖²/k, _⟩
    rw [gaussianReal_ext_iff]
    refine ⟨rfl, ?_⟩
    apply NNReal.eq
    push_cast
    rw [← hxnorm_sq]
    ring
  -- Rows are iid as scalar projections.
  have hY_indep : iIndepFun Y μ := rows_indep A hRowsIndep x
  -- Step 3: Define `Z i := (1/‖x‖) · Y i`. Each `Z i ~ N(0, 1/k)`.
  set Z : Fin k → Ω → ℝ := fun i ω => (1 / ‖x‖) * Y i ω with hZ_def
  have hZ_meas : ∀ i, Measurable (Z i) := fun i => (hY_meas i).const_mul _
  have hZ_law : ∀ i, Measure.map (Z i) μ =
      gaussianReal 0 ⟨1 / k, by positivity⟩ := by
    intro i
    have := map_const_mul_gaussian (hY_meas i) (hY_law i) (1 / ‖x‖)
    rw [this]
    rw [gaussianReal_ext_iff]
    refine ⟨by ring, ?_⟩
    apply NNReal.eq
    push_cast
    field_simp
  have hZ_indep : iIndepFun Z μ :=
    hY_indep.comp (fun _ r => (1 / ‖x‖) * r)
      (fun _ => measurable_const.mul measurable_id)
  -- Step 4+5: The bad event matches `{ω | ε < |∑ i, (Z i ω)² - 1|}`.
  have hY_eq_xZ : ∀ i ω, Y i ω = ‖x‖ * Z i ω := by
    intro i ω
    simp only [Z]
    field_simp
  have hsum_sq : ∀ ω, ∑ i, (Y i ω) ^ 2 = ‖x‖ ^ 2 * ∑ i, (Z i ω) ^ 2 := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hY_eq_xZ i ω]
    ring
  have hbad_eq : {ω | BadSingle ε (A ω) x} = {ω | ε < |(∑ i, (Z i ω) ^ 2) - 1|} := by
    ext ω
    simp only [BadSingle, Set.mem_setOf_eq]
    rw [norm_sq_toEuclideanLin]
    show ε * ‖x‖ ^ 2 < _ ↔ _
    rw [show (∑ i, ((A ω).toEuclideanLin x i) ^ 2) = ∑ i, (Y i ω) ^ 2 from rfl,
        hsum_sq]
    rw [show ‖x‖ ^ 2 * (∑ i, (Z i ω) ^ 2) - ‖x‖ ^ 2 =
            ‖x‖ ^ 2 * ((∑ i, (Z i ω) ^ 2) - 1) from by ring]
    rw [abs_mul, abs_of_pos hx_norm_sq_pos]
    constructor
    · intro h; nlinarith [hx_norm_sq_pos, h]
    · intro h; nlinarith [hx_norm_sq_pos, h, abs_nonneg ((∑ i, (Z i ω) ^ 2) - 1)]
  rw [hbad_eq]
  -- Step 6: Apply `chi_squared_tail`.
  exact chi_squared_tail μ hk_pos Z hZ_meas hZ_law hZ_indep ε hε_pos hε_lt

/-! ## Distribution-agnostic export

The following theorem is the **architectural centrepiece** for sub-Gaussian
extensibility: it gives the JL concentration bound for any random matrix
whose rows have iid scalar projections and whose centered squared row
projections satisfy a Bernstein MGF condition. Both Gaussian matrices
(via `hasBernsteinMGF_centered_chi_squared`) and Rademacher / sub-Gaussian
matrices (via Hoeffding + a Hanson-Wright-style chaos bound) are
specializations of this single theorem. -/

/-- **Distribution-agnostic JL single-vector concentration.**

For a random matrix `A` whose row-projections `(Ax)_i` are iid (in the
scalar-valued sense, after fixing `x`) and whose centered squared
projections `((Ax)_i)² − ‖x‖²/k` satisfy `HasBernsteinMGF (c, tmax)`, the
distortion event `ε ‖x‖² < |‖Ax‖² − ‖x‖²|` is bounded by a Bernstein tail.

The Gaussian case recovers `2 · exp(−k ε² / 8)` with `c = 2 ‖x‖⁴ / k²`,
`tmax = k / (4 ‖x‖²)`, `ε ≤ 1`.

This theorem does NOT require any specific distribution on the matrix
entries — only that the centered squared row projections satisfy the
Bernstein MGF condition. -/
theorem jl_concentration_single_via_bernstein (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (h_proj_meas : ∀ i, Measurable (fun ω => (A ω).toEuclideanLin x i))
    (h_proj_indep : iIndepFun (fun (i : Fin k) ω => (A ω).toEuclideanLin x i) μ)
    (c tmax : ℝ) (hc : 0 < c)
    (h_bern : ∀ i, HasBernsteinMGF
        (fun ω => ((A ω).toEuclideanLin x i) ^ 2 - ‖x‖ ^ 2 / k) μ c tmax)
    (s : ℝ) (hs_pos : 0 ≤ s) (hs_le : s ≤ 2 * (k : ℝ) * c * tmax) :
    (μ {ω | s < |‖(A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|}).toReal ≤
      2 * Real.exp (-s ^ 2 / (4 * (k : ℝ) * c)) := by
  -- Apply the abstract centered-squared iid tail with σ² := ‖x‖²/k.
  have h_concentration := centered_squared_iid_tail h_proj_meas h_proj_indep hc h_bern
    s hs_pos (by simp only [Fintype.card_fin]; exact hs_le)
  -- The bad event matches.
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk_pos.ne'
  have h_set_eq : ∀ ω, ‖(A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2 =
      (∑ i, ((A ω).toEuclideanLin x i) ^ 2) -
        (Fintype.card (Fin k) : ℝ) * (‖x‖ ^ 2 / k) := by
    intro ω
    rw [norm_sq_toEuclideanLin, Fintype.card_fin]
    field_simp
  have hbad_eq : {ω | s < |‖(A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|}
      = {ω | s < |(∑ i, ((A ω).toEuclideanLin x i) ^ 2) -
        (Fintype.card (Fin k) : ℝ) * (‖x‖ ^ 2 / k)|} := by
    ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_set_eq]
  rw [hbad_eq]
  simpa only [Fintype.card_fin] using h_concentration

end JLConcentration
