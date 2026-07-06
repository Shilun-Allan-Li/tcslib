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
# JL for Rademacher / sub-Gaussian Random Matrices

## Main results

- `subgaussian_centered_sq_bernstein`: axiom (Vershynin 2.7.6) — sub-Gaussian `Z` with variance `σ²` implies `Z² − σ²` has Bernstein MGF `(2σ⁴, 1/(4σ²))`.
- `jl_concentration_single_subgaussian`: distribution-agnostic JL single-vector concentration bound for sub-Gaussian row projections.
- `rademacherReal`: the Rademacher distribution on `ℝ` (half mass at `-1`, half at `+1`).
- `rademacherReal_mem_Icc`: the Rademacher distribution is supported in `[-1, 1]`.
- `integral_id_rademacherReal`: mean of the Rademacher distribution is zero.
- `integral_sq_rademacherReal`: second moment of the Rademacher distribution is 1.
- `hasSubgaussianMGF_id_rademacherReal`: identity is sub-Gaussian with parameter 1 under Rademacher (Hoeffding).
- `radMatrix`: the explicit `±1/√k` Rademacher random matrix on the nested-Pi sample space.
- `hasSubgaussianMGF_row_proj`: row projection is sub-Gaussian with parameter `‖x‖²/k` via Hoeffding + independence.
- `variance_row_proj`: variance of each row projection is `‖x‖²/k` exactly.
- `radMatrix_proj_indep`: row projections of the Rademacher matrix are mutually independent.
- `jl_concentration_single_rademacher`: JL concentration bound `ℙ[ε‖x‖² < |‖Ax‖² − ‖x‖²|] ≤ 2 exp(−kε²/8)` for the Rademacher matrix.

## References

- Original formalization by Ganesh Sankar
-/

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section JLSubGaussian

variable {d k : ℕ}

/-! # Part I — Sub-Gaussian abstraction layer

The sub-Gaussian path declares **one** classical-fact axiom (Hanson-Wright /
Vershynin 2.7.6) and uses it to prove a distribution-agnostic JL
concentration theorem. This is the architectural lever that lets the
Rademacher specialization in Part II plug into the JL machinery for free. -/

/-! ## §1. Sub-Gaussian → sub-exponential-squared (axiom)

The classical inequality: if `Z` is sub-Gaussian with parameter `σ²`
(meaning `mgf Z μ t ≤ exp(σ² · t² / 2)` for all `t`) and `E[Z²] = σ²`, then
`Z² − σ²` is sub-exponential, with centered MGF bounded by `exp(2 σ⁴ t²)`
on `|t| ≤ 1/(4 σ²)`.

This recovers the Gaussian centered-chi-squared bound in the special case
where `Z ~ N(0, σ²)`. For Rademacher rows `Z = Σⱼ εⱼ xⱼ / √k` (`εⱼ ∈ {±1}`
iid), Hoeffding's lemma gives `Z` sub-Gaussian with parameter `‖x‖²/k`,
so the same bound applies. -/

/-- **Sub-Gaussian → sub-exponential-squared centered MGF bound** (axiom;
Vershynin, *High-Dimensional Probability*, Lemma 2.7.6 — the scalar
case of Hanson-Wright).

For sub-Gaussian `Z` with variance `σ²`, `Z² − σ²` has Bernstein MGF
`(2 σ⁴, 1/(4 σ²))`, i.e. `mgf (Z² − σ²) μ t ≤ exp(2 σ⁴ · t²)` on
`|t| ≤ 1/(4 σ²)`.

## Proof sketch (positive-`t` side — fully classical, ~150 LoC of Lean
   given the right Fubini/independence-extension scaffolding).

For `t ≥ 0`, one uses **Gaussian decoupling**: introducing an auxiliary
`W ~ N(0, 1)` independent of `Z` on a product space, the Gaussian MGF
gives the pointwise identity `exp(t·z²) = E_W[exp(√(2t)·z·W)]`. Then
Fubini-Tonelli swaps the two integrals:

```
E_Z[exp(t·Z²)]
  = E_Z E_W[exp(√(2t)·Z·W)]
  = E_W E_Z[exp((√(2t)·W)·Z)]                  -- Fubini
  ≤ E_W[exp(σ² · (√(2t)·W)² / 2)]              -- sub-Gaussian on Z
  = E_W[exp(σ² · t · W²)]
  = (1 − 2σ²t)^{−1/2}                           -- Gaussian quadratic integral
```

Centering by `exp(−tσ²)` and taking logs gives
`log mgf (Z² − σ²) μ t ≤ −tσ² − ½ log(1 − 2σ²t)`. Setting `s = σ²t`,
the project's Taylor inequality `neg_log_one_sub_two_mul_le_two_sq`
(proved in `concentration_bound.lean`) gives `−s − ½ log(1 − 2s) ≤ 2s²`
on `|s| ≤ 1/4`, i.e. for `|t| ≤ 1/(4σ²)`.

## Negative-`t` side — why the axiom is left in.

For `t ≤ 0`, the decoupling identity fails (`√(2t) ∉ ℝ`). Vershynin's
two-sided proof goes through the **Orlicz `ψ₁`-norm** of `Z²` and the
sub-exponential MGF characterization `‖Y‖_{ψ₁} ≤ K ⇒ mgf Y t ≤ exp(C K² t²)`
for `|t| ≤ c/K`. The chain is:

```
‖Z‖_{ψ₂} ≤ K   ⇒   ‖Z²‖_{ψ₁} ≤ K²   ⇒   two-sided Bernstein MGF on Z² − σ².
```

**Mathlib (as of v4.29.0-rc8) has no Orlicz-norm machinery.** A dedicated
TODO in `Mathlib/Probability/Moments/SubGaussian.lean` calls this out
explicitly. Discharging this axiom in the project would therefore
require either:

* formalizing Orlicz `ψ_p`-norms and the `ψ₁/ψ₂` chain rule, plus
  the sub-exponential MGF characterization (a substantial Mathlib
  contribution, certainly multi-day);
* OR finding an alternative two-sided proof that bypasses Orlicz norms
  (no such proof is known to the author; the literature uniformly
  routes through `ψ_p` or Hanson-Wright's original exchangeable-pairs
  argument, which is itself non-trivial to formalize).

The positive-`t` half is fully formalizable from existing pieces: the
project already proves the Gaussian quadratic integral
(`integral_exp_mul_sq_gaussianReal_zero` style) AND the Taylor inequality
(`neg_log_one_sub_two_mul_le_two_sq`). The remaining gap is purely the
independence-extension + Fubini infrastructure — ~150 LoC. We leave the
full discharge as future work and cite Vershynin instead. -/
axiom subgaussian_centered_sq_bernstein
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (σ_sq : ℝ) (hσ_pos : 0 < σ_sq)
    (hZ_subG : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ ∧
        mgf Z μ t ≤ Real.exp (σ_sq * t ^ 2 / 2))
    (hZ_var : ∫ ω, (Z ω) ^ 2 ∂μ = σ_sq) :
    HasBernsteinMGF (fun ω => (Z ω) ^ 2 - σ_sq) μ
      (2 * σ_sq ^ 2) (1 / (4 * σ_sq))

/-! ## (Note) Gaussian specialization: `(Ax)_i` for Gaussian matrix

We can derive `HasBernsteinMGF (Y² − σ²)` for `Y ~ N(0, σ²)` from our
already-proved `centered_chi_squared_step`, generalized from `1/k` to
arbitrary variance. This shows the axiom `subgaussian_centered_sq_bernstein`
is **redundant** for the Gaussian case (we prove it directly via
`integral_gaussian` + Taylor); it is needed only for genuinely sub-Gaussian
distributions like Rademacher. -/

-- For reference, the Gaussian case is fully proved in
-- `concentration_bound.lean` as `hasBernsteinMGF_centered_chi_squared`.
-- A general-variance version (for `‖x‖²/k` instead of `1/k`) would follow
-- by change of variables, similar to `integral_exp_mul_sq_gaussianReal_zero`.

/-! ## §2. Distribution-agnostic JL concentration (proved using the axiom)

Given the sub-Gaussian → sub-exponential-squared axiom (or, in the
Gaussian case, the proved analogue), `jl_concentration_single_via_bernstein`
in `concentration_bound.lean` immediately gives the JL concentration bound.

For a matrix `A` with sub-Gaussian rows of variance `‖x‖²/k`:

  ℙ[ ε ‖x‖² < |‖A x‖² − ‖x‖²| ] ≤ 2 · exp(−ε² k / 8)

— the standard JL bound, identical for Gaussian and Rademacher inputs.

The full theorem statement and proof would mirror
`jl_concentration_single_via_chi_squared`, with sub-Gaussian + variance
hypotheses replacing the explicit Gaussian-law hypothesis. -/

/-- **Distribution-agnostic JL single-vector concentration.**

For a random matrix `A` whose row-projections `(Ax)_i` are independent and
each sub-Gaussian with variance `‖x‖²/k`, the JL concentration bound holds:

  ℙ[ ε ‖x‖² < |‖A x‖² − ‖x‖²| ] ≤ 2 · exp(−ε² k / 8).

This is Rademacher / sub-Gaussian JL: in particular, applying it to a
Rademacher matrix (where `(Ax)_i = (1/√k) Σⱼ εᵢⱼ xⱼ` is Hoeffding
sub-Gaussian with variance `‖x‖²/k`) recovers Achlioptas's original
`±1`-entries variant of JL with the same constants as Dasgupta-Gupta. -/
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
  -- Derive Bernstein MGF for centered row-square via the sub-Gaussian → sub-exp-sq axiom.
  have h_bern : ∀ i, HasBernsteinMGF
      (fun ω => ((A ω).toEuclideanLin x i) ^ 2 - ‖x‖ ^ 2 / k) μ
      (2 * (‖x‖ ^ 2 / k) ^ 2) (1 / (4 * (‖x‖ ^ 2 / k))) := fun i =>
    subgaussian_centered_sq_bernstein μ
      (fun ω => (A ω).toEuclideanLin x i) (h_proj_meas i)
      (‖x‖ ^ 2 / k) hσ_pos (h_proj_subG i) (h_proj_var i)
  -- Apply the abstract distribution-agnostic JL concentration.
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
  have h_concentration := jl_concentration_single_via_bernstein hk_pos μ A x
    h_proj_meas h_proj_indep _ _ (by positivity) h_bern s hs_pos hs_le
  -- Match the exponent: -s²/(4 k c) = -ε² ‖x‖⁴ / (4 k · 2 (‖x‖²/k)²) = -ε² k / 8.
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

/-! # Part II — Rademacher matrix specialization

We construct an explicit Rademacher random matrix and prove its row
projections satisfy the hypotheses of `jl_concentration_single_subgaussian`.

The matrix entries `A i j` are `±1/√k`, each with probability `1/2`,
mutually independent across all `(i, j)`. The row projection
`(A x)_i = (1/√k) Σⱼ εᵢⱼ xⱼ` is then sub-Gaussian with parameter
`‖x‖²/k` by Hoeffding's lemma applied to each summand and additivity
across independent summands.

This recovers Achlioptas's `±1`-entries variant of JL with the same
exponent `k ε² / 8` as Dasgupta–Gupta. -/

noncomputable section RademacherMatrix

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

/-! ## §3. The Rademacher distribution on `ℝ` -/

/-- The Rademacher distribution on `ℝ`: half mass at `-1`, half mass at `+1`. -/
noncomputable def rademacherReal : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)

private lemma rad_half_ne_top : (1/2 : ℝ≥0∞) ≠ ⊤ := by
  intro h
  have : (1/2 : ℝ≥0∞) < ⊤ := by
    refine ENNReal.div_lt_top ?_ ?_
    · exact ENNReal.one_ne_top
    · exact two_ne_zero
  exact this.ne h

instance : IsProbabilityMeasure rademacherReal where
  measure_univ := by
    unfold rademacherReal
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        measure_univ, measure_univ]
    simp [ENNReal.inv_two_add_inv_two]

instance : IsFiniteMeasure rademacherReal := inferInstance

/-- Rademacher is supported in `[-1, 1]`. -/
lemma rademacherReal_mem_Icc :
    ∀ᵐ y ∂rademacherReal, y ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  have hms : MeasurableSet {y : ℝ | ¬ y ∈ Set.Icc (-1 : ℝ) 1} :=
    measurableSet_Icc.compl
  unfold rademacherReal
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hms, Measure.dirac_apply' _ hms]
  simp

/-- Integrability of bounded measurable functions under a smul-of-dirac. -/
private lemma integrable_smul_dirac {f : ℝ → ℝ} (a : ℝ) :
    Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac a) :=
  (integrable_dirac (a := a) (f := f) (by simp)).smul_measure rad_half_ne_top

/-- Any function with values in ℝ is integrable under the Rademacher measure. -/
lemma integrable_rademacherReal (f : ℝ → ℝ) :
    Integrable f rademacherReal := by
  unfold rademacherReal
  exact (integrable_smul_dirac (-1 : ℝ)).add_measure (integrable_smul_dirac (1 : ℝ))

/-- The mean of the Rademacher distribution is zero. -/
lemma integral_id_rademacherReal : ∫ y, y ∂rademacherReal = 0 := by
  unfold rademacherReal
  rw [integral_add_measure (integrable_smul_dirac _) (integrable_smul_dirac _),
      integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
  simp

/-- The second moment of the Rademacher distribution is 1. -/
lemma integral_sq_rademacherReal : ∫ y, y ^ 2 ∂rademacherReal = 1 := by
  unfold rademacherReal
  rw [integral_add_measure (integrable_smul_dirac _) (integrable_smul_dirac _),
      integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
  simp; norm_num

/-- The identity function `id : ℝ → ℝ` is sub-Gaussian with parameter `1`
under the Rademacher distribution. This follows from Hoeffding's lemma
(any centered random variable in `[-1, 1]` is sub-Gaussian with parameter
`((1 - (-1))/2)² = 1`). -/
lemma hasSubgaussianMGF_id_rademacherReal :
    HasSubgaussianMGF (id : ℝ → ℝ) 1 rademacherReal := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := rademacherReal) (X := id)
    (aemeasurable_id) rademacherReal_mem_Icc
    (by simpa using integral_id_rademacherReal)
  convert h using 1
  have : ‖(1 : ℝ) - (-1)‖₊ = 2 := by
    rw [show (1 : ℝ) - (-1) = 2 from by norm_num]
    simp
  rw [this]
  norm_num

/-! ## §4. Rademacher matrix construction

We build the random matrix on the sample space `Fin k → Fin d → ℝ` with
nested product measure (iid Rademacher per entry). The matrix
`radMatrix ω i j = ω i j / √k` rescales the raw `±1` entries to give the
correct row variance `‖x‖² / k`. -/

/-- Sample space for the Rademacher matrix: indexed by `(i, j) ∈ Fin k × Fin d`. -/
abbrev RadΩ (k d : ℕ) : Type := Fin k → Fin d → ℝ

instance (k d : ℕ) : MeasurableSpace (RadΩ k d) := inferInstance

/-- The joint product measure on `RadΩ k d`: each entry iid Rademacher. -/
noncomputable def radJointMeasure (k d : ℕ) : Measure (RadΩ k d) :=
  Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => rademacherReal))

instance (k d : ℕ) : IsProbabilityMeasure (radJointMeasure k d) := by
  unfold radJointMeasure; infer_instance

/-- The Rademacher matrix: scale raw `±1` entries by `1/√k`. -/
def radMatrix (k d : ℕ) : RadΩ k d → Matrix (Fin k) (Fin d) ℝ :=
  fun ω i j => ω i j / Real.sqrt k

lemma measurable_radMatrix (k d : ℕ) : Measurable (radMatrix k d) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).div_const _

/-- Marginal of the `i`-th row of the joint measure is the inner Pi (iid Rademacher). -/
private lemma radJointMeasure_row_marginal (k d : ℕ) (i : Fin k) :
    Measure.map (fun (ω : RadΩ k d) => ω i) (radJointMeasure k d) =
      Measure.pi (fun _ : Fin d => rademacherReal) := by
  unfold radJointMeasure
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin k => Measure.pi (fun _ : Fin d => rademacherReal)) i).map_eq

/-- Marginal of the `(i, j)` entry of the joint measure is `rademacherReal`. -/
lemma radJointMeasure_entry_marginal (k d : ℕ) (i : Fin k) (j : Fin d) :
    Measure.map (fun (ω : RadΩ k d) => ω i j) (radJointMeasure k d) =
      rademacherReal := by
  have hcoord : Measure.map (fun (r : Fin d → ℝ) => r j)
      (Measure.pi (fun _ : Fin d => rademacherReal)) = rademacherReal :=
    (MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin d => rademacherReal) j).map_eq
  have hrow := radJointMeasure_row_marginal k d i
  have heq : (fun (ω : RadΩ k d) => ω i j) =
      (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
  rw [heq, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
      hrow, hcoord]

/-- Within row `i`, the entries `j ↦ ω i j` are iid Rademacher (mutually independent). -/
lemma radJointMeasure_row_iid (k d : ℕ) (i : Fin k) :
    iIndepFun (fun (j : Fin d) (ω : RadΩ k d) => ω i j) (radJointMeasure k d) := by
  have hrow := radJointMeasure_row_marginal k d i
  have hentry : ∀ j : Fin d, Measure.map
      (fun (ω : RadΩ k d) => ω i j) (radJointMeasure k d) = rademacherReal :=
    fun j => radJointMeasure_entry_marginal k d i j
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun j => Measurable.aemeasurable (by fun_prop))]
  -- LHS: joint distribution of `(j ↦ ω i j)` is the inner Pi.
  have hLHS : Measure.map (fun (ω : RadΩ k d) (j : Fin d) => ω i j)
      (radJointMeasure k d) = Measure.pi (fun _ : Fin d => rademacherReal) := by
    have hfn : (fun (ω : RadΩ k d) (j : Fin d) => ω i j) = fun ω => ω i := rfl
    rw [hfn, hrow]
  rw [hLHS]
  -- RHS: product of marginals is also inner Pi.
  congr 1
  funext j
  exact (hentry j).symm

/-- Rows are mutually independent: the `Fin d → ℝ`-valued row vectors are iid. -/
lemma radJointMeasure_rows_iid (k d : ℕ) :
    iIndepFun (fun (i : Fin k) (ω : RadΩ k d) (j : Fin d) => ω i j)
      (radJointMeasure k d) := by
  unfold radJointMeasure
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-! ## §5. Sub-Gaussian property of the row projection -/

/-- Each entry `ω i j`, viewed as a function of the joint sample, is sub-Gaussian
with parameter `1` under the joint Pi measure. -/
lemma hasSubgaussianMGF_entry (k d : ℕ) (i : Fin k) (j : Fin d) :
    HasSubgaussianMGF (fun (ω : RadΩ k d) => ω i j) 1 (radJointMeasure k d) := by
  have hY : AEMeasurable (fun (ω : RadΩ k d) => ω i j) (radJointMeasure k d) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable
  have hmap : (radJointMeasure k d).map (fun ω => ω i j) = rademacherReal :=
    radJointMeasure_entry_marginal k d i j
  have hSG : HasSubgaussianMGF (id : ℝ → ℝ) 1
      ((radJointMeasure k d).map (fun ω => ω i j)) := by
    rw [hmap]; exact hasSubgaussianMGF_id_rademacherReal
  exact HasSubgaussianMGF.of_map hY hSG

/-- For nonzero `k`, each scaled summand `(x j / √k) * ω i j` is sub-Gaussian
with parameter `x j ^ 2 / k`. -/
lemma hasSubgaussianMGF_scaled_entry (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) (j : Fin d) :
    HasSubgaussianMGF (fun (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      ⟨(x j) ^ 2 / k, by positivity⟩ (radJointMeasure k d) := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hsqrt_sq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk_real_pos.le
  set c := x j / Real.sqrt k
  -- Step 1: c · y is sub-Gaussian with parameter c² under rademacherReal (Hoeffding).
  have hSG_rad : HasSubgaussianMGF (fun y : ℝ => c * y)
      ⟨c ^ 2, by positivity⟩ rademacherReal := by
    have hmem : ∀ᵐ y ∂rademacherReal, c * y ∈ Set.Icc (-(|c|)) (|c|) := by
      filter_upwards [rademacherReal_mem_Icc] with y hy
      have habs_y : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
      have habs : |c * y| ≤ |c| :=
        calc |c * y| = |c| * |y| := abs_mul c y
          _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left habs_y (abs_nonneg c)
          _ = |c| := mul_one _
      exact ⟨by linarith [neg_abs_le (c * y)], (le_abs_self _).trans habs⟩
    have hmean : ∫ y, c * y ∂rademacherReal = 0 := by
      have := integral_id_rademacherReal
      calc ∫ y, c * y ∂rademacherReal
          = c * ∫ y, y ∂rademacherReal := by
            rw [MeasureTheory.integral_const_mul]
        _ = c * 0 := by rw [this]
        _ = 0 := mul_zero c
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := rademacherReal) (X := fun y => c * y) (a := -(|c|)) (b := |c|)
      (measurable_const.mul measurable_id).aemeasurable hmem hmean
    convert h using 1
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_mk,
               Real.nnnorm_of_nonneg (show (0 : ℝ) ≤ |c| - -|c| by linarith [abs_nonneg c])]
    rw [show |c| - -|c| = 2 * |c| from by ring]
    nlinarith [sq_abs c, abs_nonneg c]
  -- Step 2: lift to the joint measure via the coordinate marginal.
  have hY : AEMeasurable (fun ω : RadΩ k d => ω i j) (radJointMeasure k d) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable
  have hSG_entry : HasSubgaussianMGF (fun y => c * y) ⟨c ^ 2, by positivity⟩
      ((radJointMeasure k d).map (fun ω => ω i j)) := by
    rw [radJointMeasure_entry_marginal]; exact hSG_rad
  -- Step 3: match the parameter c² = (x j)² / k.
  have hparam : (⟨c ^ 2, by positivity⟩ : ℝ≥0) = ⟨(x j) ^ 2 / k, by positivity⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_mk]
    rw [div_pow, hsqrt_sq]
  rw [← hparam]
  exact HasSubgaussianMGF.of_map hY hSG_entry

/-- The row projection `(radMatrix ω).toEuclideanLin x i = (1/√k) Σⱼ ω i j · x j`
is sub-Gaussian with parameter `‖x‖² / k`. Composes per-summand Hoeffding
(`hasSubgaussianMGF_scaled_entry`) with `HasSubgaussianMGF.sum_of_iIndepFun`
and within-row independence (`radJointMeasure_row_iid`). -/
lemma hasSubgaussianMGF_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    HasSubgaussianMGF (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i)
      ⟨‖x‖ ^ 2 / k, by positivity⟩ (radJointMeasure k d) := by
  -- Step 1: Independence within row.
  have h_row_iid := radJointMeasure_row_iid k d i
  -- Step 2: Sub-Gaussian per scaled summand.
  have h_scaled : ∀ j : Fin d, HasSubgaussianMGF
      (fun (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      ⟨(x j) ^ 2 / k, by positivity⟩ (radJointMeasure k d) := fun j =>
    hasSubgaussianMGF_scaled_entry k d hk_pos x i j
  -- Step 3: Independence of the scaled summands.
  have h_scaled_iid : iIndepFun
      (fun (j : Fin d) (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      (radJointMeasure k d) := by
    let g : Fin d → ℝ → ℝ := fun j r => (x j / Real.sqrt k) * r
    have hg : ∀ j, Measurable (g j) := fun j => measurable_const.mul measurable_id
    exact h_row_iid.comp g hg
  -- Step 4: Sum of independent sub-Gaussians.
  have h_sum := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ)
    h_scaled_iid (fun j _ => h_scaled j)
  -- Step 5: Match the row-projection function and the parameter.
  have h_eq_fun : (fun (ω : RadΩ k d) =>
      ∑ j, (x j / Real.sqrt k) * ω i j) =
      (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i) := by
    funext ω
    change _ = ∑ j, (radMatrix k d ω) i j * x j
    apply Finset.sum_congr rfl
    intro j _
    unfold radMatrix
    ring
  rw [h_eq_fun] at h_sum
  convert h_sum using 1
  -- Parameter: ⟨‖x‖²/k, _⟩ = ∑ j, ⟨x_j²/k, _⟩ (because ‖x‖² = ∑ j, x_j²).
  apply NNReal.eq
  push_cast
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, sq_abs]

/-! ## §6. Variance of the row projection -/

/-- Variance of the identity function under the Rademacher distribution is 1. -/
lemma variance_id_rademacherReal : Var[(id : ℝ → ℝ); rademacherReal] = 1 := by
  have hMemLp : MemLp (id : ℝ → ℝ) 2 rademacherReal :=
    memLp_of_bounded rademacherReal_mem_Icc
      (Measurable.aestronglyMeasurable measurable_id) 2
  rw [variance_eq_sub hMemLp]
  have h1 : ∫ x, ((id : ℝ → ℝ) ^ 2) x ∂rademacherReal = 1 := by
    simp only [Pi.pow_apply, id]
    exact integral_sq_rademacherReal
  have h2 : ∫ x, (id : ℝ → ℝ) x ∂rademacherReal = 0 := by
    simp only [id]
    exact integral_id_rademacherReal
  rw [h1, h2]
  ring

/-- Variance of an entry `ω i j` under the joint measure is `1`. -/
lemma variance_entry (k d : ℕ) (i : Fin k) (j : Fin d) :
    Var[(fun (ω : RadΩ k d) => ω i j); radJointMeasure k d] = 1 := by
  have hY : AEMeasurable (fun (ω : RadΩ k d) => ω i j) (radJointMeasure k d) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable
  rw [← variance_id_map hY, radJointMeasure_entry_marginal,
      variance_id_rademacherReal]

/-- Mean of an entry `ω i j` under the joint measure is `0`. -/
lemma integral_entry (k d : ℕ) (i : Fin k) (j : Fin d) :
    ∫ ω, (ω i j : ℝ) ∂(radJointMeasure k d) = 0 := by
  have hY : AEMeasurable (fun (ω : RadΩ k d) => ω i j) (radJointMeasure k d) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable
  have hint : ∫ ω, id (ω i j) ∂(radJointMeasure k d) =
      ∫ y, id y ∂rademacherReal := by
    rw [← integral_map hY (Measurable.aestronglyMeasurable measurable_id),
        radJointMeasure_entry_marginal]
  calc ∫ ω, (ω i j : ℝ) ∂(radJointMeasure k d)
      = ∫ ω, id (ω i j) ∂(radJointMeasure k d) := rfl
    _ = ∫ y, id y ∂rademacherReal := hint
    _ = 0 := by simpa using integral_id_rademacherReal

/-- Each scaled summand `(x j / √k) * ω i j` is in `MemLp 2`. -/
private lemma memLp_scaled_entry (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) (j : Fin d) :
    MemLp (fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j) 2 (radJointMeasure k d) := by
  set c := x j / Real.sqrt k
  have hY : Measurable (fun ω : RadΩ k d => ω i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hentry_ae : ∀ᵐ ω ∂radJointMeasure k d, ω i j ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    rw [show {ω : RadΩ k d | ω i j ∉ Set.Icc (-1 : ℝ) 1} =
        (fun ω => ω i j) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ from by ext; simp]
    rw [← Measure.map_apply hY measurableSet_Icc.compl, radJointMeasure_entry_marginal]
    exact ae_iff.mp rademacherReal_mem_Icc
  have hscaled_ae : ∀ᵐ ω ∂radJointMeasure k d, c * ω i j ∈ Set.Icc (-(|c|)) (|c|) := by
    filter_upwards [hentry_ae] with ω hω
    have habs_y : |ω i j| ≤ 1 := abs_le.mpr ⟨hω.1, hω.2⟩
    have habs : |c * ω i j| ≤ |c| :=
      calc |c * ω i j| = |c| * |ω i j| := abs_mul c _
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left habs_y (abs_nonneg c)
        _ = |c| := mul_one _
    exact ⟨by linarith [neg_abs_le (c * ω i j)], (le_abs_self _).trans habs⟩
  exact memLp_of_bounded hscaled_ae
    (measurable_const.mul hY).aestronglyMeasurable 2

/-- Variance of `(x j / √k) * ω i j` is `x_j² / k`. -/
lemma variance_scaled_entry (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) (j : Fin d) :
    Var[(fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j); radJointMeasure k d] =
      (x j) ^ 2 / k := by
  have hvc := variance_mul (x j / Real.sqrt k)
    (fun ω : RadΩ k d => ω i j) (μ := radJointMeasure k d)
  -- variance_mul gives: Var[c * X] = c² * Var[X]
  have hve := variance_entry k d i j
  -- Stitch: Var[c * X] = c² * 1 = c² = (x j / √k)² = x_j² / k
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hsqrt_sq : (Real.sqrt k) ^ 2 = k := Real.sq_sqrt hk_real_pos.le
  rw [hvc, hve, mul_one, div_pow, hsqrt_sq]

/-- Variance of the row projection is `‖x‖² / k`. Composes
`IndepFun.variance_sum` with `variance_scaled_entry` (per-summand
variance) and `radJointMeasure_row_iid` (within-row independence). -/
lemma variance_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    Var[(fun ω : RadΩ k d => (radMatrix k d ω).toEuclideanLin x i);
      radJointMeasure k d] = ‖x‖ ^ 2 / k := by
  -- Express row projection as a Finset sum of scaled summands.
  have h_eq : (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i) =
      fun (ω : RadΩ k d) =>
        ∑ j, (x j / Real.sqrt k) * ω i j := by
    funext ω
    change ∑ j, (radMatrix k d ω) i j * x j = _
    apply Finset.sum_congr rfl
    intro j _
    unfold radMatrix
    ring
  rw [h_eq]
  -- Apply IndepFun.variance_sum.
  have h_row_iid := radJointMeasure_row_iid k d i
  have h_scaled_iid : iIndepFun
      (fun (j : Fin d) (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      (radJointMeasure k d) := by
    let g : Fin d → ℝ → ℝ := fun j r => (x j / Real.sqrt k) * r
    have hg : ∀ j, Measurable (g j) := fun j => measurable_const.mul measurable_id
    exact h_row_iid.comp g hg
  rw [show (fun ω : RadΩ k d => ∑ j, (x j / Real.sqrt k) * ω i j) =
      (∑ j, fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j) from by
    funext ω; simp [Finset.sum_apply]]
  rw [IndepFun.variance_sum
    (fun j _ => memLp_scaled_entry k d hk_pos x i j)
    (fun j _ j' _ hjj' => h_scaled_iid.indepFun hjj')]
  -- Sum of variances = ∑ x_j²/k = ‖x‖²/k
  rw [show (∑ j, Var[(fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j); radJointMeasure k d]) =
      ∑ j, (x j) ^ 2 / k from
        Finset.sum_congr rfl (fun j _ => variance_scaled_entry k d hk_pos x i j)]
  -- ∑ j, x_j²/k = ‖x‖²/k
  rw [← Finset.sum_div]
  congr 1
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, sq_abs]

/-- Mean of the row projection is `0`. -/
lemma integral_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    ∫ ω, (radMatrix k d ω).toEuclideanLin x i ∂(radJointMeasure k d) = 0 := by
  have h_eq : (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i) =
      fun (ω : RadΩ k d) =>
        ∑ j, (x j / Real.sqrt k) * ω i j := by
    funext ω
    change ∑ j, (radMatrix k d ω) i j * x j = _
    apply Finset.sum_congr rfl
    intro j _
    unfold radMatrix
    ring
  rw [h_eq]
  rw [integral_finset_sum _
    (fun j _ => (memLp_scaled_entry k d hk_pos x i j).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  apply Finset.sum_eq_zero
  intro j _
  rw [show (fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j) =
      fun ω => (x j / Real.sqrt k) * (ω i j) from rfl,
      integral_const_mul, integral_entry, mul_zero]

/-- The hypothesis required by `subgaussian_centered_sq_bernstein` axiom:
    `∫ Z² = σ²` for the row projection with `σ² = ‖x‖²/k`.
    Follows from `variance_row_proj` and `integral_row_proj` via
    `variance_eq_sub`: `∫ Y² = Var[Y] + (∫ Y)² = ‖x‖²/k + 0`. -/
lemma integral_sq_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    ∫ ω, ((radMatrix k d ω).toEuclideanLin x i) ^ 2 ∂(radJointMeasure k d) =
      ‖x‖ ^ 2 / k := by
  -- ∫ Y² = Var[Y] + (∫ Y)² = ‖x‖²/k + 0² = ‖x‖²/k.
  have h_sub : HasSubgaussianMGF (fun ω : RadΩ k d =>
      (radMatrix k d ω).toEuclideanLin x i)
      ⟨‖x‖ ^ 2 / k, by positivity⟩ (radJointMeasure k d) :=
    hasSubgaussianMGF_row_proj k d hk_pos x i
  have hMemLp : MemLp
      (fun ω : RadΩ k d => (radMatrix k d ω).toEuclideanLin x i) 2
      (radJointMeasure k d) := by
    have h_eq : (fun ω : RadΩ k d => (radMatrix k d ω).toEuclideanLin x i) =
        fun ω => ∑ j, (x j / Real.sqrt k) * ω i j := by
      funext ω; change ∑ j, (radMatrix k d ω) i j * x j = _
      exact Finset.sum_congr rfl (fun j _ => by unfold radMatrix; ring)
    rw [h_eq]
    exact memLp_finset_sum Finset.univ
      (fun j _ => memLp_scaled_entry k d hk_pos x i j)
  have h_var := variance_row_proj k d hk_pos x i
  have h_mean := integral_row_proj k d hk_pos x i
  rw [variance_eq_sub hMemLp] at h_var
  rw [h_mean] at h_var
  simp only [Pi.pow_apply] at h_var
  linarith

/-! ## §7. Row-projection independence and the JL concentration bound -/

/-- Row projections of the Rademacher matrix are mutually independent. -/
lemma radMatrix_proj_indep (k d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun (i : Fin k) (ω : RadΩ k d) =>
      (radMatrix k d ω).toEuclideanLin x i) (radJointMeasure k d) := by
  have h_rows := radJointMeasure_rows_iid k d
  let g : Fin k → (Fin d → ℝ) → ℝ := fun _ r => ∑ j, (r j / Real.sqrt k) * x j
  have hg : ∀ i, Measurable (g i) := fun _ =>
    Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).div_const _).mul_const _)
  exact h_rows.comp g hg

/-- Each row projection is measurable. -/
lemma radMatrix_proj_meas (k d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    Measurable (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i) := by
  change Measurable (fun ω => ∑ j, (radMatrix k d ω) i j * x j)
  exact Finset.measurable_sum _ (fun j _ =>
    (((measurable_pi_apply j).comp (measurable_pi_apply i)).div_const _).mul_const _)

/-- **JL concentration for the Rademacher matrix.**

For the explicit Rademacher matrix `radMatrix k d` on the joint Pi-Rademacher
sample space, the JL concentration bound holds with the same exponent as
the Gaussian case:

  ℙ[ ε ‖x‖² < |‖A x‖² − ‖x‖²| ] ≤ 2 · exp(−ε² k / 8).

This recovers Achlioptas's `±1`-entries variant of JL with the
Dasgupta–Gupta exponent. The proof composes:

* `hasSubgaussianMGF_row_proj` — row projection is sub-Gaussian via
  Hoeffding + sum-of-independent-sub-Gaussians (no axioms).
* `integral_sq_row_proj` — variance of row projection is `‖x‖²/k`
  (no axioms).
* `radMatrix_proj_indep` — rows are independent.
* `jl_concentration_single_subgaussian` — distribution-agnostic bound
  (uses the `subgaussian_centered_sq_bernstein` axiom).

The Hanson-Wright axiom is the only project-local axiom invoked in the
chain. -/
theorem jl_concentration_single_rademacher (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (radJointMeasure k d {ω | ε * ‖x‖ ^ 2 <
      |‖(radMatrix k d ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  refine jl_concentration_single_subgaussian hk_pos (radJointMeasure k d)
    (radMatrix k d) x hx
    (radMatrix_proj_meas k d x)
    (radMatrix_proj_indep k d x)
    ?_ ?_ ε hε_pos hε_lt
  · intro i t
    have h_sub := hasSubgaussianMGF_row_proj k d hk_pos x i
    refine ⟨h_sub.integrable_exp_mul t, ?_⟩
    have hmgf := h_sub.mgf_le t
    -- The parameter ⟨‖x‖²/k, _⟩ : ℝ≥0 projects to ‖x‖²/k : ℝ.
    simpa using hmgf
  · intro i
    exact integral_sq_row_proj k d hk_pos x i

end RademacherMatrix
