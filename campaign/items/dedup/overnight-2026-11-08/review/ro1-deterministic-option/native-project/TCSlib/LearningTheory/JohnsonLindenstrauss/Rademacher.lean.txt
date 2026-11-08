/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import TCSlib.LearningTheory.JohnsonLindenstrauss.SubGaussian
import Mathlib.Probability.Moments.SubGaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# JL for Rademacher Random Matrices

## Main definitions

- `rademacherReal`: the Rademacher distribution on `ℝ` (half mass at `-1`, half at `+1`).
- `RadΩ`, `radJointMeasure`: the nested-Pi sample space and its product Rademacher measure.
- `radMatrix`: the explicit `±1/√k` Rademacher random matrix on the nested-Pi sample space.

## Main results

- `rademacherReal_mem_Icc`: the Rademacher distribution is supported in `[-1, 1]`.
- `integral_id_rademacherReal`: mean of the Rademacher distribution is zero.
- `integral_sq_rademacherReal`: second moment of the Rademacher distribution is 1.
- `hasSubgaussianMGF_id_rademacherReal`: the identity is sub-Gaussian with parameter `1` under
  the Rademacher distribution (Hoeffding's lemma).
- `hasSubgaussianMGF_const_mul`: scaling a sub-Gaussian variable by `c` scales the parameter
  by `c²`.
- `hasSubgaussianMGF_row_proj`: each row projection is sub-Gaussian with parameter `‖x‖²/k`
  (Hoeffding + independence).
- `variance_row_proj`: variance of each row projection is `‖x‖²/k` exactly.
- `radMatrix_proj_indep`: row projections of the Rademacher matrix are mutually independent.
- `jl_concentration_single_rademacher`: the JL concentration bound
  `ℙ[ε‖x‖² < |‖Ax‖² − ‖x‖²|] ≤ 2 exp(−kε²/8)` for the Rademacher matrix.

## References

* [Ach03] D. Achlioptas, "Database-friendly random projections: Johnson–Lindenstrauss with
  binary coins", *J. Comput. Syst. Sci.* 66(4):671–687, 2003.
* [Ver18] R. Vershynin, *High-Dimensional Probability: An Introduction with Applications in
  Data Science*, Cambridge University Press, 2018.

Original formalization by Ganesh Sankar.
-/

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

/-! ## Part II — Rademacher matrix specialization

We construct an explicit Rademacher random matrix and prove its row
projections satisfy the hypotheses of `jl_concentration_single_subgaussian`.

The matrix entries `A i j` are `±1/√k`, each with probability `1/2`,
mutually independent across all `(i, j)`. The row projection
`(A x)_i = (1/√k) Σⱼ εᵢⱼ xⱼ` is then sub-Gaussian with parameter
`‖x‖²/k` by Hoeffding's lemma applied to each summand and additivity
across independent summands.

This recovers Achlioptas's `±1`-entries variant of JL [Ach03, Thm 1.1] with the
same exponent `k ε² / 8` as Dasgupta–Gupta. -/

noncomputable section RademacherMatrix

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

/-! ## §3. The Rademacher distribution on `ℝ` -/

/-- The Rademacher distribution on `ℝ`: the probability measure with mass `1/2` at `-1` and
mass `1/2` at `+1`, the law of one `±1` coin of the random matrix in [Ach03, §1 / Thm 1.1]. -/
noncomputable def rademacherReal : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)

/-- The scalar `1/2` in `ℝ≥0∞` is finite (needed to scale Dirac measures by it). -/
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

/-- Almost every sample of the Rademacher distribution lies in the interval `[-1, 1]`: the
complement of `[-1, 1]` contains neither `-1` nor `1`, so it has measure zero. -/
lemma rademacherReal_mem_Icc :
    ∀ᵐ y ∂rademacherReal, y ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  have hms : MeasurableSet {y : ℝ | ¬ y ∈ Set.Icc (-1 : ℝ) 1} :=
    measurableSet_Icc.compl
  unfold rademacherReal
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hms, Measure.dirac_apply' _ hms]
  simp

/-- Every real function is integrable with respect to `(1/2) • dirac a`, a finite multiple
of a Dirac mass (no boundedness or measurability hypothesis is needed). -/
private lemma integrable_smul_dirac {f : ℝ → ℝ} (a : ℝ) :
    Integrable f ((1/2 : ℝ≥0∞) • Measure.dirac a) :=
  (integrable_dirac (a := a) (f := f) (by simp)).smul_measure rad_half_ne_top

/-- Every real-valued function on `ℝ` is integrable with respect to the Rademacher
distribution, which is a finite sum of scaled Dirac masses. -/
lemma integrable_rademacherReal (f : ℝ → ℝ) :
    Integrable f rademacherReal := by
  unfold rademacherReal
  exact (integrable_smul_dirac (-1 : ℝ)).add_measure (integrable_smul_dirac (1 : ℝ))

/-- The mean of the Rademacher distribution is zero: the integral of the identity is
`(1/2)·(-1) + (1/2)·1 = 0`. -/
lemma integral_id_rademacherReal : ∫ y, y ∂rademacherReal = 0 := by
  unfold rademacherReal
  rw [integral_add_measure (integrable_smul_dirac _) (integrable_smul_dirac _),
      integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
  simp

/-- The second moment of the Rademacher distribution is `1`: the integral of `y ↦ y²` is
`(1/2)·1 + (1/2)·1 = 1`. -/
lemma integral_sq_rademacherReal : ∫ y, y ^ 2 ∂rademacherReal = 1 := by
  unfold rademacherReal
  rw [integral_add_measure (integrable_smul_dirac _) (integrable_smul_dirac _),
      integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
  simp; norm_num

/-- The identity function `id : ℝ → ℝ` is sub-Gaussian with parameter `1` under the
Rademacher distribution, i.e. its moment generating function at `t` is at most `exp(t²/2)`
[Ver18, proof of Thm 2.2.2]. The source computes `E exp(tε) = cosh t ≤ exp(t²/2)`
directly; here the bound is obtained from Hoeffding's lemma in Mathlib's API
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`): any centered random variable with
values in `[-1, 1]` is sub-Gaussian with parameter `((1 - (-1))/2)² = 1`. -/
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

/-- Sample space for the Rademacher matrix: the functions `Fin k → Fin d → ℝ`, one real
coordinate for each entry `(i, j) ∈ Fin k × Fin d` of the matrix in [Ach03, §1 / Thm 1.1]. -/
abbrev RadΩ (k d : ℕ) : Type := Fin k → Fin d → ℝ

instance (k d : ℕ) : MeasurableSpace (RadΩ k d) := inferInstance

/-- The joint law of the raw `±1` entries: the nested product measure on `RadΩ k d` under
which the `k·d` coordinates `ω i j` are iid Rademacher [Ach03, §1 / Thm 1.1]. -/
noncomputable def radJointMeasure (k d : ℕ) : Measure (RadΩ k d) :=
  Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => rademacherReal))

instance (k d : ℕ) : IsProbabilityMeasure (radJointMeasure k d) := by
  unfold radJointMeasure; infer_instance

/-- The Rademacher random matrix `A ω i j = ω i j / √k` of [Ach03, §1 / Thm 1.1]: the raw
`±1` entries of the sample `ω` scaled by `1/√k`, so that each row projection `(A x)ᵢ` has
variance `‖x‖²/k`. Deviation: Achlioptas keeps `±1` entries and scales the projection by
`1/√k`; here the scaling is folded into the entries. -/
def radMatrix (k d : ℕ) : RadΩ k d → Matrix (Fin k) (Fin d) ℝ :=
  fun ω i j => ω i j / Real.sqrt k

/-- The Rademacher matrix `radMatrix k d` is a measurable function of the sample `ω`: each
entry is a coordinate projection divided by the constant `√k`. -/
lemma measurable_radMatrix (k d : ℕ) : Measurable (radMatrix k d) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).div_const _

/-- The law of the `i`-th row `ω ↦ ω i` under the joint measure is the inner product
measure, i.e. `d` iid Rademacher coordinates. -/
private lemma radJointMeasure_row_marginal (k d : ℕ) (i : Fin k) :
    Measure.map (fun (ω : RadΩ k d) => ω i) (radJointMeasure k d) =
      Measure.pi (fun _ : Fin d => rademacherReal) := by
  unfold radJointMeasure
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin k => Measure.pi (fun _ : Fin d => rademacherReal)) i).map_eq

/-- The law of the single entry `ω ↦ ω i j` under the joint measure is the Rademacher
distribution (compose the row marginal with the coordinate marginal of the inner product). -/
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

/-- Within a fixed row `i`, the entries `ω ↦ ω i j` for `j : Fin d` are mutually independent
under the joint measure (each with Rademacher law): the joint law of the row is the inner
product measure, which is also the product of the entry marginals. -/
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

/-- The rows `ω ↦ ω i` for `i : Fin k`, viewed as `(Fin d → ℝ)`-valued random variables, are
mutually independent under the joint measure (coordinates of an outer product measure). -/
lemma radJointMeasure_rows_iid (k d : ℕ) :
    iIndepFun (fun (i : Fin k) (ω : RadΩ k d) (j : Fin d) => ω i j)
      (radJointMeasure k d) := by
  unfold radJointMeasure
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-! ## §5. Sub-Gaussian property of the row projection -/

/-- Each entry `ω ↦ ω i j`, viewed as a random variable on the joint sample space, is
sub-Gaussian with parameter `1` under the joint measure — the per-summand input to
[Ver18, Prop 2.6.1]. Obtained by transporting `hasSubgaussianMGF_id_rademacherReal` along
the entry marginal `radJointMeasure_entry_marginal`. -/
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

/-- If `X` is sub-Gaussian with parameter `σ` then `c·X` is sub-Gaussian with parameter
`c²·σ` (the sub-Gaussian parameter is homogeneous of degree two under scaling):
`mgf (c·X) t = mgf X (t·c) ≤ exp (σ (t c)² / 2) = exp ((c² σ) t² / 2)`. -/
lemma hasSubgaussianMGF_const_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {σ : ℝ≥0} (h : HasSubgaussianMGF X σ μ) (c : ℝ) :
    HasSubgaussianMGF (fun ω => c * X ω) ⟨c ^ 2 * σ, by positivity⟩ μ where
  integrable_exp_mul t := by
    simpa only [mul_assoc] using h.integrable_exp_mul (t * c)
  mgf_le t := by
    have hmgf : mgf (fun ω => c * X ω) μ t = mgf X μ (t * c) := by
      simp only [mgf, mul_assoc]
    rw [hmgf]
    refine (h.mgf_le (t * c)).trans (le_of_eq ?_)
    congr 1
    simp only [NNReal.coe_mk]
    ring

/-- For `k > 0`, the scaled entry `ω ↦ (x j / √k) · ω i j` is sub-Gaussian with parameter
`x_j² / k` under the joint measure — the per-summand input to [Ver18, Prop 2.6.1]. Scale
`hasSubgaussianMGF_entry` by `x j / √k` via `hasSubgaussianMGF_const_mul` and simplify the
parameter `(x j / √k)² · 1 = x_j² / k`. -/
lemma hasSubgaussianMGF_scaled_entry (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) (j : Fin d) :
    HasSubgaussianMGF (fun (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      ⟨(x j) ^ 2 / k, by positivity⟩ (radJointMeasure k d) := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  have hsqrt_sq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk_real_pos.le
  -- Step 1: scale the entry's sub-Gaussian bound (`hasSubgaussianMGF_entry`) by `x j / √k`.
  have h_scaled :=
    hasSubgaussianMGF_const_mul (hasSubgaussianMGF_entry k d i j) (x j / Real.sqrt k)
  -- Step 2: match the parameter `(x j / √k)² · 1 = (x j)² / k`.
  convert h_scaled using 1
  apply NNReal.eq
  simp only [NNReal.coe_mk, NNReal.coe_one, mul_one, div_pow, hsqrt_sq]

/-- The row projection `(radMatrix ω).toEuclideanLin x i` is the sum of the scaled
entries `(x j / √k) * ω i j`. -/
private lemma radMatrix_row_proj_eq_sum (k d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i) =
      fun ω => ∑ j, (x j / Real.sqrt k) * ω i j := by
  funext ω
  change ∑ j, (radMatrix k d ω) i j * x j = _
  exact Finset.sum_congr rfl (fun j _ => by unfold radMatrix; ring)

/-- Within row `i`, the scaled entries `j ↦ (x j / √k) * ω i j` are mutually independent. -/
private lemma radMatrix_scaled_row_iid (k d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    iIndepFun (fun (j : Fin d) (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      (radJointMeasure k d) :=
  (radJointMeasure_row_iid k d i).comp (fun j r => (x j / Real.sqrt k) * r)
    (fun _ => measurable_const.mul measurable_id)

/-- `‖x‖² / k = ∑ j, x_j² / k` for `x` in Euclidean space. -/
private lemma norm_sq_div_eq_sum (k : ℕ) {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 / k = ∑ j, (x j) ^ 2 / k := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by rw [Real.norm_eq_abs, sq_abs])

/-- For `k > 0` and any `x ∈ ℝ^d`, the row projection
`ω ↦ ((radMatrix ω).toEuclideanLin x) i = (1/√k) Σⱼ ω i j · x j` is sub-Gaussian with
parameter `‖x‖² / k` under the joint measure [Ver18, Prop 2.6.1] (a sum of independent
sub-Gaussian variables is sub-Gaussian with the sum of the parameters).

**Proof sketch.** Step 1: each scaled summand `(x j / √k) · ω i j` is sub-Gaussian with
parameter `x_j² / k` (`hasSubgaussianMGF_scaled_entry`, i.e. Hoeffding's lemma plus
scaling). Step 2: the summands are independent within the row
(`radMatrix_scaled_row_iid`), so their sum is sub-Gaussian with parameter `Σⱼ x_j² / k`
(Mathlib's `HasSubgaussianMGF.sum_of_iIndepFun`). Step 3: the row projection is exactly that
sum (`radMatrix_row_proj_eq_sum`), and `Σⱼ x_j² / k = ‖x‖² / k`. -/
lemma hasSubgaussianMGF_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    HasSubgaussianMGF (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i)
      ⟨‖x‖ ^ 2 / k, by positivity⟩ (radJointMeasure k d) := by
  -- Step 1: each scaled summand is sub-Gaussian with parameter `x_j² / k`.
  have h_scaled : ∀ j : Fin d, HasSubgaussianMGF
      (fun (ω : RadΩ k d) => (x j / Real.sqrt k) * ω i j)
      ⟨(x j) ^ 2 / k, by positivity⟩ (radJointMeasure k d) := fun j =>
    hasSubgaussianMGF_scaled_entry k d hk_pos x i j
  -- Step 2: the summands are independent within the row, so their sum is sub-Gaussian.
  have h_sum := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ)
    (radMatrix_scaled_row_iid k d x i) (fun j _ => h_scaled j)
  -- Step 3: the row projection is that sum; match the parameter `‖x‖²/k = ∑ x_j²/k`.
  rw [radMatrix_row_proj_eq_sum]
  convert h_sum using 1
  apply NNReal.eq
  push_cast
  exact norm_sq_div_eq_sum k x

/-! ## §6. Variance of the row projection -/

/-- The variance of the identity function under the Rademacher distribution is `1`: it is
the second moment `1` minus the square of the mean `0`. -/
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

/-- The variance of an entry `ω ↦ ω i j` under the joint measure is `1` (transport
`variance_id_rademacherReal` along the entry marginal). -/
lemma variance_entry (k d : ℕ) (i : Fin k) (j : Fin d) :
    Var[(fun (ω : RadΩ k d) => ω i j); radJointMeasure k d] = 1 := by
  have hY : AEMeasurable (fun (ω : RadΩ k d) => ω i j) (radJointMeasure k d) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable
  rw [← variance_id_map hY, radJointMeasure_entry_marginal,
      variance_id_rademacherReal]

/-- The mean of an entry `ω ↦ ω i j` under the joint measure is `0` (transport
`integral_id_rademacherReal` along the entry marginal). -/
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

/-- Each scaled entry `ω ↦ (x j / √k) · ω i j` is square-integrable (in `L²`) under the
joint measure, being almost surely bounded in absolute value by `|x j / √k|`.

**Proof sketch.** Write `c = x j / √k`. Step 1: the entry `ω i j` lies in `[-1, 1]`
almost surely, by transporting `rademacherReal_mem_Icc` along the marginal identity
`radJointMeasure_entry_marginal` (the preimage of the complement of `[-1, 1]` is null).
Step 2: hence `c · ω i j` lies in `[-|c|, |c|]` almost surely, since
`|c · ω i j| = |c| · |ω i j| ≤ |c|`. Step 3: an almost-surely bounded measurable function
is in `L²` (`memLp_of_bounded`). -/
private lemma memLp_scaled_entry (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) (j : Fin d) :
    MemLp (fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j) 2 (radJointMeasure k d) := by
  set c := x j / Real.sqrt k
  have hY : Measurable (fun ω : RadΩ k d => ω i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  -- Step 1: the entry `ω i j` lies in `[-1, 1]` almost surely, via the marginal identity.
  have hentry_ae : ∀ᵐ ω ∂radJointMeasure k d, ω i j ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    rw [show {ω : RadΩ k d | ω i j ∉ Set.Icc (-1 : ℝ) 1} =
        (fun ω => ω i j) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ from by ext; simp]
    rw [← Measure.map_apply hY measurableSet_Icc.compl, radJointMeasure_entry_marginal]
    exact ae_iff.mp rademacherReal_mem_Icc
  -- Step 2: hence `c · ω i j` lies in `[-|c|, |c|]` almost surely.
  have hscaled_ae : ∀ᵐ ω ∂radJointMeasure k d, c * ω i j ∈ Set.Icc (-(|c|)) (|c|) := by
    filter_upwards [hentry_ae] with ω hω
    have habs_y : |ω i j| ≤ 1 := abs_le.mpr ⟨hω.1, hω.2⟩
    have habs : |c * ω i j| ≤ |c| :=
      calc |c * ω i j| = |c| * |ω i j| := abs_mul c _
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left habs_y (abs_nonneg c)
        _ = |c| := mul_one _
    exact ⟨by linarith [neg_abs_le (c * ω i j)], (le_abs_self _).trans habs⟩
  -- Step 3: an almost-surely bounded measurable function is in `L²`.
  exact memLp_of_bounded hscaled_ae
    (measurable_const.mul hY).aestronglyMeasurable 2

/-- For `k > 0`, the variance of the scaled entry `ω ↦ (x j / √k) · ω i j` under the joint
measure is `x_j² / k`: `Var[c·X] = c² · Var[X] = c² · 1` with `c = x j / √k`. -/
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

/-- For `k > 0` and any `x ∈ ℝ^d`, the variance of the row projection
`ω ↦ ((radMatrix ω).toEuclideanLin x) i` under the joint measure is exactly `‖x‖² / k`.

**Proof sketch.** Step 1: the row projection is the pointwise sum of the scaled entries
`(x j / √k) · ω i j` (`radMatrix_row_proj_eq_sum`). Step 2: the scaled entries are
square-integrable and pairwise independent within the row (`radMatrix_scaled_row_iid`), so
the variance of the sum is the sum of the variances (Mathlib's `IndepFun.variance_sum`).
Step 3: the per-summand variances `x_j² / k` (`variance_scaled_entry`) sum to `‖x‖² / k`. -/
lemma variance_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    Var[(fun ω : RadΩ k d => (radMatrix k d ω).toEuclideanLin x i);
      radJointMeasure k d] = ‖x‖ ^ 2 / k := by
  -- Step 1: the row projection is the (pointwise) sum of the scaled summands.
  rw [radMatrix_row_proj_eq_sum,
    show (fun ω : RadΩ k d => ∑ j, (x j / Real.sqrt k) * ω i j) =
      (∑ j, fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j) from by
    funext ω; simp [Finset.sum_apply]]
  -- Step 2: pairwise independence within the row makes the variance additive.
  rw [IndepFun.variance_sum
    (fun j _ => memLp_scaled_entry k d hk_pos x i j)
    (fun j _ j' _ hjj' => (radMatrix_scaled_row_iid k d x i).indepFun hjj')]
  -- Step 3: per-summand variances `x_j² / k` sum to `‖x‖² / k`.
  rw [show (∑ j, Var[(fun ω : RadΩ k d => (x j / Real.sqrt k) * ω i j); radJointMeasure k d]) =
      ∑ j, (x j) ^ 2 / k from
        Finset.sum_congr rfl (fun j _ => variance_scaled_entry k d hk_pos x i j)]
  exact (norm_sq_div_eq_sum k x).symm

/-- For `k > 0` and any `x ∈ ℝ^d`, the mean of the row projection
`ω ↦ ((radMatrix ω).toEuclideanLin x) i` under the joint measure is `0`.

**Proof sketch.** Step 1: the row projection is the sum of the scaled entries
`(x j / √k) · ω i j`. Step 2: each summand is integrable, so the integral of the sum is the
sum of the integrals. Step 3: each summand has mean `(x j / √k) · 0 = 0` by
`integral_entry`. -/
lemma integral_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    ∫ ω, (radMatrix k d ω).toEuclideanLin x i ∂(radJointMeasure k d) = 0 := by
  -- Step 1: the row projection is the sum of the scaled summands.
  rw [radMatrix_row_proj_eq_sum]
  -- Step 2: each summand is integrable, so the integral is the sum of the integrals.
  rw [integral_finset_sum _
    (fun j _ => (memLp_scaled_entry k d hk_pos x i j).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  -- Step 3: each summand has mean `(x j / √k) · 0 = 0`.
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_const_mul, integral_entry, mul_zero]

/-- For `k > 0` and any `x ∈ ℝ^d`, the second moment of the row projection
`ω ↦ ((radMatrix ω).toEuclideanLin x) i` under the joint measure is `‖x‖² / k`. This is the
hypothesis `∫ Z² = σ²` (with `σ² = ‖x‖²/k`) consumed by
`subgaussian_centered_sq_bernstein` through `jl_concentration_single_subgaussian`.

**Proof sketch.** Step 1: the row projection is in `L²`, being a finite sum of the `L²`
scaled entries. Step 2: by `variance_eq_sub`, `∫ Y² = Var[Y] + (∫ Y)²`, and
`variance_row_proj` and `integral_row_proj` give `‖x‖²/k + 0²`. -/
lemma integral_sq_row_proj (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    ∫ ω, ((radMatrix k d ω).toEuclideanLin x i) ^ 2 ∂(radJointMeasure k d) =
      ‖x‖ ^ 2 / k := by
  -- Step 1: the row projection is in `L²` (a finite sum of `L²` summands).
  have hMemLp : MemLp
      (fun ω : RadΩ k d => (radMatrix k d ω).toEuclideanLin x i) 2
      (radJointMeasure k d) := by
    rw [radMatrix_row_proj_eq_sum]
    exact memLp_finset_sum Finset.univ
      (fun j _ => memLp_scaled_entry k d hk_pos x i j)
  -- Step 2: `∫ Y² = Var[Y] + (∫ Y)² = ‖x‖²/k + 0²`.
  have h_var := variance_row_proj k d hk_pos x i
  have h_mean := integral_row_proj k d hk_pos x i
  rw [variance_eq_sub hMemLp, h_mean] at h_var
  simp only [Pi.pow_apply] at h_var
  linarith

/-! ## §7. Row-projection independence and the JL concentration bound -/

/-- For fixed `x ∈ ℝ^d`, the row projections `ω ↦ ((radMatrix ω).toEuclideanLin x) i` for
`i : Fin k` are mutually independent under the joint measure: each is a measurable function
of the `i`-th row alone, and the rows are independent (`radJointMeasure_rows_iid`). -/
lemma radMatrix_proj_indep (k d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun (i : Fin k) (ω : RadΩ k d) =>
      (radMatrix k d ω).toEuclideanLin x i) (radJointMeasure k d) := by
  have h_rows := radJointMeasure_rows_iid k d
  let g : Fin k → (Fin d → ℝ) → ℝ := fun _ r => ∑ j, (r j / Real.sqrt k) * x j
  have hg : ∀ i, Measurable (g i) := fun _ =>
    Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).div_const _).mul_const _)
  exact h_rows.comp g hg

/-- For fixed `x ∈ ℝ^d` and `i`, the row projection `ω ↦ ((radMatrix ω).toEuclideanLin x) i`
is a measurable function of the sample (a finite sum of scaled coordinate projections). -/
lemma radMatrix_proj_meas (k d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    Measurable (fun (ω : RadΩ k d) => (radMatrix k d ω).toEuclideanLin x i) := by
  change Measurable (fun ω => ∑ j, (radMatrix k d ω) i j * x j)
  exact Finset.measurable_sum _ (fun j _ =>
    (((measurable_pi_apply j).comp (measurable_pi_apply i)).div_const _).mul_const _)

/-- **JL concentration for the Rademacher matrix** [Ach03, Thm 1.1].

For `k > 0`, any nonzero `x ∈ ℝ^d` and any `0 < ε < 1`, the `±1/√k` Rademacher matrix
`A = radMatrix k d` on the joint sample space satisfies

  ℙ[ ε ‖x‖² < |‖A x‖² − ‖x‖²| ] ≤ 2 · exp(−ε² k / 8),

the same exponent as the Gaussian case. Deviation: Achlioptas proves the bound
`2 · exp(−(ε²/2 − ε³/3) k/2)` (better than `kε²/8` for `ε < 3/4`) for `±1` entries by a
direct moment computation; here the
bound `2 · exp(−kε²/8)` comes from the sub-Gaussian route through the fully proved
`subgaussian_centered_sq_bernstein`; the result is proved with no project-local axioms.

**Proof sketch.** Step 1: apply the distribution-agnostic bound
`jl_concentration_single_subgaussian` to `radMatrix k d`, whose row projections are
measurable (`radMatrix_proj_meas`) and mutually independent (`radMatrix_proj_indep`).
Step 2: each row projection is sub-Gaussian with parameter `‖x‖²/k`
(`hasSubgaussianMGF_row_proj`, via Hoeffding's lemma and independence); unpack
the `HasSubgaussianMGF` structure into the integrability and MGF-bound hypotheses. Step 3:
each row projection has second moment exactly `‖x‖²/k` (`integral_sq_row_proj`). -/
theorem jl_concentration_single_rademacher (k d : ℕ) (hk_pos : 0 < k)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (radJointMeasure k d {ω | ε * ‖x‖ ^ 2 <
      |‖(radMatrix k d ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  -- Step 1: the distribution-agnostic bound, with measurable independent row projections.
  refine jl_concentration_single_subgaussian hk_pos (radJointMeasure k d)
    (radMatrix k d) x hx
    (radMatrix_proj_meas k d x)
    (radMatrix_proj_indep k d x)
    ?_ ?_ ε hε_pos hε_lt
  · -- Step 2: each row projection is sub-Gaussian with parameter `‖x‖²/k`.
    intro i t
    have h_sub := hasSubgaussianMGF_row_proj k d hk_pos x i
    refine ⟨h_sub.integrable_exp_mul t, ?_⟩
    have hmgf := h_sub.mgf_le t
    -- The parameter ⟨‖x‖²/k, _⟩ : ℝ≥0 projects to ‖x‖²/k : ℝ.
    simpa using hmgf
  · -- Step 3: each row projection has second moment `‖x‖²/k`.
    intro i
    exact integral_sq_row_proj k d hk_pos x i

end RademacherMatrix
