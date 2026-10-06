/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Real
import TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein

/-!
# Row Distribution of the Johnson–Lindenstrauss Random Projection

## Main definitions

- `BadSingle`: the "bad event" for a single vector — strict distortion exceeds ε‖x‖²

## Main results

- `concentration_zero`: when x = 0 the bad event is empty and the bound holds trivially
- `map_const_mul_gaussian`: scalar multiple of a centered Gaussian restatement
- `sum_scaled_iid_gaussian_map`: sum of scaled i.i.d. Gaussians is Gaussian with scaled
  variance
- `rows_indep`: rows of Ax are independent given independent matrix rows
- `toEuclideanLin_apply_eq_sum`: coordinate-sum form of (A.toEuclideanLin x) i
- `norm_sq_toEuclideanLin`: ‖A.toEuclideanLin x‖² as a sum of squared row entries

## References

* [DG03] S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and
  Lindenstrauss", *Random Structures & Algorithms* 22(1):60–65, 2003.
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

/-- Matrices as `m → n → α` inherit a Pi measurable space structure. -/
instance : MeasurableSpace (Matrix (Fin k) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin d → ℝ))

/-- The "bad event" for a single vector `x` under the random projection `A`: the squared
norm of `Ax` differs from the squared norm of `x` by strictly more than `ε‖x‖²`, that is,
`ε‖x‖² < |‖Ax‖² − ‖x‖²|`. This is the failure event of [DG03, Lemma 2.2] (the
event `|‖Ax‖² − ‖x‖²| > ε‖x‖²`), stated with strict inequality. -/
def BadSingle (ε : ℝ) (A : Matrix (Fin k) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ε * ‖x‖ ^ 2 < |‖A.toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|

/-! ## Step 1: The `x = 0` case

When `x = 0`, the bad event is empty: `ε · 0 < |0 − 0|` simplifies to
`0 < 0`, which is false. So its measure is `0`, and the bound
`0 ≤ 2 · exp(−kε²/8)` holds trivially. -/

/-- For the zero vector the single-vector concentration bound holds trivially: for any
random matrix `A` and any `ε`, the probability of the bad event `BadSingle ε (A ω) 0` is at
most `2·exp(−kε²/8)`, because that event is empty. -/
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

/-- If a measurable real random variable `X` has law `N(0, σ₀)` (Mathlib's `gaussianReal`
with variance parameter `σ₀`), then for any real `c` the scalar multiple `c·X` has law
`N(0, c²·σ₀)`. This is the scaling step of [DG03, §2] (a linear image of a centered
Gaussian is a centered Gaussian); it is an auxiliary restatement of Mathlib's
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

If `Y j` are mutually independent measurable real random variables each with law
`N(0, σ₀)` and `x j : ℝ` are fixed coefficients, then for every finite set `s` of indices
the weighted sum `∑ j ∈ s, x j · Y j` has law `N(0, (∑ j ∈ s, (x j)²) · σ₀)` under
`μ`. This is the observation of [DG03, §2] that the projection of iid Gaussians is Gaussian with
variance `‖x‖²/k` (DG03 work with a random orthogonal projection; the iid-Gaussian-matrix
form used here is the standard variant, cf. [Ver18, §5.3]).

**Proof sketch.** Step 1: the scaled family `Z j = x j · Y j` is measurable, each `Z j`
has law `N(0, (x j)²·σ₀)` by `map_const_mul_gaussian`, and the `Z j` are mutually
independent as images of the `Y j`. Step 2: induct on the finite set `s`. In the empty
case the sum is identically `0`, whose law is the Dirac mass at `0`, i.e. `N(0, 0)`.
Step 3 (insert case): split the sum as `Z j₀` plus the sum over the remaining indices; the
two are independent (Mathlib's `iIndepFun.indepFun_finset_sum_of_notMem`), the partial
sum is Gaussian by the induction hypothesis, and the sum of two independent centered
Gaussians is centered Gaussian with added variances
(`gaussianReal_add_gaussianReal_of_indepFun`); finally match the variance expression. -/
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
  -- Step 1: the family `Z j := x j * Y j` is independent Gaussian by `iIndepFun.comp`.
  set Z : ι → Ω → ℝ := fun j ω => x j * Y j ω with hZ_def
  have hZ_meas : ∀ j, Measurable (Z j) := fun j => (hY_meas j).const_mul (x j)
  have hZ_law : ∀ j, Measure.map (Z j) μ =
      gaussianReal 0 (⟨(x j) ^ 2, sq_nonneg _⟩ * σ₀) := fun j =>
    map_const_mul_gaussian (hY_meas j) (hY_law j) (x j)
  have hZ_indep : iIndepFun Z μ :=
    hY_indep.comp (fun j r => x j * r) (fun j => measurable_const.mul measurable_id)
  -- Step 2: induction on `s`.
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
    -- Step 3: split the sum and use independence + Gaussian add.
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

/-- **Rows of `Ax` are independent.** Given that the row vectors of the random matrix `A`
are mutually independent as `(Fin d → ℝ)`-valued random variables, the scalar
row-projections `(A ω).toEuclideanLin x i = ∑ⱼ A ω i j · x j` are mutually independent
across `i` for every fixed vector `x` — they are measurable functions of disjoint row
vectors. This is the independence-of-coordinates observation of [DG03, §2] in the
iid-Gaussian-matrix setting (cf. [Ver18, §5.3]). -/
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

/-- The `i`-th coordinate of the image of `x` under the linear map of the matrix `A` is the
row sum `∑ j, A i j * x j`; this holds by definition of `Matrix.toEuclideanLin`. -/
lemma toEuclideanLin_apply_eq_sum
    (A : Matrix (Fin k) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    (A.toEuclideanLin x) i = ∑ j, A i j * x j := rfl

/-- The squared Euclidean norm of the image of `x` under the linear map of the matrix `A`
equals the sum over the rows `i` of the squared coordinates
`((A.toEuclideanLin x) i)²`. -/
lemma norm_sq_toEuclideanLin
    (A : Matrix (Fin k) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖A.toEuclideanLin x‖ ^ 2 = ∑ i, ((A.toEuclideanLin x) i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity)]
  simp [sq_abs]

end JLConcentration
