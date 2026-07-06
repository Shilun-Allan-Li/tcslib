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
import Mathlib.Data.Real.Basic
import TCSlib.LearningTheory.JohnsonLindenstrauss.ConcentrationBound
import TCSlib.LearningTheory.JohnsonLindenstrauss.Rademacher

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Johnson–Lindenstrauss Lemma

## Main results

- `JLDistortion`: The `(1 ± ε)` two-sided distortion predicate for a single pair of points.
- `IsJLEmbedding`: A linear map `f : ℝ^d → ℝ^k` that preserves all pairwise squared distances up to factor `(1 ± ε)`.
- `BadPair`: The bad event that some pair in `V × V` is distorted by more than factor `ε`.
- `jl_concentration_single`: Single-vector concentration bound for iid Gaussian matrices.
- `JLDistortion.of_not_bad`: Converts negation of `BadSingle` to `JLDistortion`.
- `jl_union_bound`: Union bound over all `|V|²` ordered pairs.
- `measurableSet_badSingle`: Measurability of the per-pair bad event.
- `johnson_lindenstrauss_of_gaussian`: Structural JL theorem via the probabilistic method (Gaussian).
- `johnson_lindenstrauss_of_subgaussian`: Structural JL theorem via the probabilistic method (sub-Gaussian).
- `exists_iid_gaussian_matrix`: Existence of an iid Gaussian random matrix on a product probability space.
- `johnson_lindenstrauss`: JL flattening lemma with Gaussian matrix and explicit `k ≥ 32·log n/ε²` bound.
- `johnson_lindenstrauss_subgaussian`: JL flattening lemma with Rademacher matrix.
- `johnson_lindenstrauss_dist`: Distance form of the Gaussian JL lemma.
- `johnson_lindenstrauss_subgaussian_dist`: Distance form of the sub-Gaussian JL lemma.
- `johnson_lindenstrauss_dim_bound`: Logarithmic dimension bound for the Gaussian variant.
- `johnson_lindenstrauss_subgaussian_dim_bound`: Logarithmic dimension bound for the sub-Gaussian variant.

## References

- Original formalization by Ganesh Sankar
-/

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section JohnsonLindenstrauss

/-! ## §1. Notation

Points live in `EuclideanSpace ℝ (Fin d)`, i.e. `ℝ^d` with the standard inner
product. A `k × d` matrix acts linearly as `A.toEuclideanLin`, a bundled
`LinearMap EuclideanSpace ℝ (Fin d) (EuclideanSpace ℝ (Fin k))`.
-/

variable {d k : ℕ}

-- (`MeasurableSpace (Matrix (Fin k) (Fin d) ℝ)` instance is inherited from
-- `concentration_bound.lean`.)

/-- The `(1 ± ε)` two-sided distortion bound for a single pair of points. -/
def JLDistortion (ε : ℝ) (u v : EuclideanSpace ℝ (Fin d))
    (u' v' : EuclideanSpace ℝ (Fin k)) : Prop :=
  (1 - ε) * ‖u - v‖ ^ 2 ≤ ‖u' - v'‖ ^ 2 ∧
  ‖u' - v'‖ ^ 2 ≤ (1 + ε) * ‖u - v‖ ^ 2

/-- A linear map `f : ℝ^d → ℝ^k` is an **ε-JL embedding** of the finite set
`V` if it preserves all pairwise squared distances up to factor `(1 ± ε)`. -/
def IsJLEmbedding (ε : ℝ) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, JLDistortion ε u v (f u) (f v)

-- `BadSingle` is defined in `concentration_bound.lean`; re-exported here.

/-- The "bad event" for the whole set `V`: some pair in `V × V` is distorted
by more than a factor of `ε`. -/
def BadPair (ε : ℝ) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Matrix (Fin k) (Fin d) ℝ) : Prop :=
  ∃ u ∈ V, ∃ v ∈ V, ¬ JLDistortion ε u v
    (A.toEuclideanLin u) (A.toEuclideanLin v)

/-! ## §2. Single-vector concentration (Gaussian wrapper)

The heart of the probabilistic proof. For `x : ℝ^d` fixed, the random
variable `‖A x‖²` (with `A_ij ~ N(0, 1/k)` i.i.d.) is distributed as
`‖x‖² / k · χ²_k`, where `χ²_k` is chi-squared with `k` degrees of freedom.
Standard sub-exponential tail bounds yield the following.
-/

/-- **JL concentration (single vector).**

If `A_ij ~ N(0, 1/k)` are i.i.d. Gaussian (with rows mutually independent
and entries iid within each row), then for any fixed `x : ℝ^d` and any
`0 < ε < 1`,
`ℙ[ |‖Ax‖² − ‖x‖²| > ε · ‖x‖² ] ≤ 2 · exp(−k ε² / 8).`

This is `jl_concentration_single_via_chi_squared` from
`concentration_bound.lean`, fully proved (no axioms) via
`centered_chi_squared_step` + a Bernstein/Chernoff argument. -/
theorem jl_concentration_single (hk_pos : 0 < k)
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
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) :=
  jl_concentration_single_via_chi_squared hk_pos μ A hA_meas hA_law
    hRowEntryIndep hRowsIndep x ε hε_pos hε_lt

/-! ## §3. Union bound

Given concentration per difference vector `u − v`, a finite union bound
over the `|V|²` ordered pairs proves that with probability at least
`1 − |V|² · 2 · exp(−kε²/8)`, *every* pair is preserved. -/

/-- If the squared length of the projection is within a factor `(1±ε)` of
the original, then the pair-distortion predicate `JLDistortion` holds. -/
lemma JLDistortion.of_not_bad (ε : ℝ) (u v : EuclideanSpace ℝ (Fin d))
    (A : Matrix (Fin k) (Fin d) ℝ)
    (h : ¬ BadSingle ε A (u - v)) :
    JLDistortion ε u v (A.toEuclideanLin u) (A.toEuclideanLin v) := by
  -- `BadSingle ε A (u-v)` says `ε ‖u-v‖² < |‖A(u-v)‖² - ‖u-v‖²|`.
  -- Its negation plus `A.toEuclideanLin (u-v) = A.toEuclideanLin u - A.toEuclideanLin v`
  -- gives both sides of `JLDistortion`.
  unfold BadSingle at h
  push_neg at h
  rw [map_sub] at *
  refine ⟨?_, ?_⟩
  · -- (1 - ε) ‖u-v‖² ≤ ‖A(u-v)‖²
    have := abs_le.mp h
    have h1 := sq_nonneg ‖u - v‖
    have h2 := sq_nonneg ‖A.toEuclideanLin u - A.toEuclideanLin v‖
    linarith [this.1, this.2]
  · -- ‖A(u-v)‖² ≤ (1 + ε) ‖u-v‖²
    have := abs_le.mp h
    linarith [this.1, this.2]

/-- **JL union bound.**

Given that each pair's distortion event has probability `≤ 2·exp(−kε²/8)`,
the probability that *some* ordered pair in `V × V` is distorted is at most
`|V|² · 2 · exp(−kε²/8)`. -/
theorem jl_union_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (_hA_meas : Measurable A)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ)
    (_hBadMeasurable : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hpair : ∀ u ∈ V, ∀ v ∈ V,
      (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :
    (μ {ω | BadPair ε V (A ω)}).toReal ≤
        (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
  -- The bad-pair event is contained in the union of per-pair bad-single events.
  have hsub : {ω | BadPair ε V (A ω)} ⊆
      ⋃ u ∈ V, ⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)} := by
    intro ω hω
    obtain ⟨u, hu, v, hv, hbad⟩ := hω
    refine Set.mem_iUnion₂.mpr ⟨u, hu, Set.mem_iUnion₂.mpr ⟨v, hv, ?_⟩⟩
    by_contra hnot
    exact hbad (JLDistortion.of_not_bad ε u v (A ω) hnot)
  -- Measure subadditivity over the finite double union.
  have hmeas_le : μ {ω | BadPair ε V (A ω)} ≤
      ∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)} := by
    calc μ {ω | BadPair ε V (A ω)}
        ≤ μ (⋃ u ∈ V, ⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)}) :=
          measure_mono hsub
      _ ≤ ∑ u ∈ V, μ (⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)}) :=
          measure_biUnion_finset_le V _
      _ ≤ ∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)} := by
          gcongr with u _
          exact measure_biUnion_finset_le V _
  -- All per-pair measures are finite (μ is a probability measure).
  have hne_top : ∀ u ∈ V, ∀ v ∈ V,
      μ {ω | BadSingle ε (A ω) (u - v)} ≠ ⊤ :=
    fun u _ v _ => measure_ne_top _ _
  have hBP_ne_top : μ {ω | BadPair ε V (A ω)} ≠ ⊤ := measure_ne_top _ _
  have hInnerSum_ne_top : ∀ u ∈ V,
      (∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}) ≠ ⊤ := fun u hu => by
    rw [← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun v hv => (hne_top u hu v hv).lt_top
  have hSum_ne_top :
      (∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}) ≠ ⊤ := by
    rw [← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun u hu => (hInnerSum_ne_top u hu).lt_top
  have hsum_toReal :
      (∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}).toReal =
        ∑ u ∈ V, ∑ v ∈ V, (μ {ω | BadSingle ε (A ω) (u - v)}).toReal := by
    rw [ENNReal.toReal_sum (fun u hu => hInnerSum_ne_top u hu)]
    exact Finset.sum_congr rfl
      (fun u hu => ENNReal.toReal_sum (fun v hv => hne_top u hu v hv))
  calc (μ {ω | BadPair ε V (A ω)}).toReal
      ≤ (∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}).toReal :=
        (ENNReal.toReal_le_toReal hBP_ne_top hSum_ne_top).mpr hmeas_le
    _ = ∑ u ∈ V, ∑ v ∈ V, (μ {ω | BadSingle ε (A ω) (u - v)}).toReal :=
        hsum_toReal
    _ ≤ ∑ u ∈ V, ∑ v ∈ V, 2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
        gcongr with u hu v hv
        exact hpair u hu v hv
    _ = (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
        simp [Finset.sum_const, sq]
        ring

/-! ## §4. Probabilistic method (structural extraction)

We state the main theorem in two forms:

1. **Structural form** (`johnson_lindenstrauss_of_gaussian`): given a Gaussian
   matrix on some probability space AND that the union-bound failure
   probability is `< 1`, extract an embedding. Fully proved.
2. **Standard form** (`johnson_lindenstrauss`): the standard statement with
   `k ≥ 32 · log n / ε²`. Proves the numerical bound and invokes the
   probabilistic method; the construction of the product Gaussian measure
   on `Matrix (Fin k) (Fin d) ℝ` via nested `MeasureTheory.Measure.pi`
   (giving both within-row iid and rows iid for free) is fully proved
   below in `exists_iid_gaussian_matrix`. -/

/-- **Structural JL via the probabilistic method.**

Given a Gaussian random matrix on a probability space AND that the
union-bound failure probability `|V|² · 2 · exp(-kε²/8)` is strictly less
than `1`, there exists a realization of the random matrix that is an
`ε`-JL embedding of `V`.

This lemma is purely combinatorial/measure-theoretic: it combines
`jl_concentration_single` + `jl_union_bound` to deduce that the *good* event
has positive measure, then extracts a witness. -/
theorem johnson_lindenstrauss_of_gaussian (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (hA_law : ∀ (i : Fin k) (j : Fin d),
      Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hRowEntryIndep : ∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
        MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hFail : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: Concentration per pair.
  have hPair : ∀ u ∈ V, ∀ v ∈ V,
      (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := fun u _ v _ =>
    jl_concentration_single hk_pos μ A hA_meas hA_law hRowEntryIndep hRowsIndep
      (u - v) ε hε_pos hε_lt
  -- Step 2: Union bound over pairs.
  have hBP : (μ {ω | BadPair ε V (A ω)}).toReal ≤
      (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :=
    jl_union_bound μ A hA_meas V ε hBadMeas hPair
  -- Step 3: Failure prob strictly less than 1.
  have hBadLT1 : (μ {ω | BadPair ε V (A ω)}).toReal < 1 := lt_of_le_of_lt hBP hFail
  -- Step 4: Therefore some ω is *not* bad.
  have hGood : ∃ ω, ¬ BadPair ε V (A ω) := by
    by_contra hNG
    push_neg at hNG
    have hUniv : {ω | BadPair ε V (A ω)} = Set.univ :=
      Set.eq_univ_of_forall hNG
    rw [hUniv, measure_univ] at hBadLT1
    simp at hBadLT1
  -- Step 5: Extract witness, produce embedding.
  obtain ⟨ω, hω⟩ := hGood
  refine ⟨(A ω).toEuclideanLin, ?_⟩
  intro u hu v hv
  by_contra hbd
  exact hω ⟨u, hu, v, hv, hbd⟩

/-- **Structural sub-Gaussian JL via the probabilistic method.**

Sub-Gaussian analog of `johnson_lindenstrauss_of_gaussian`. The Gaussian
hypotheses on entries are replaced by hypotheses on row projections:
each `(Ax)_i` is sub-Gaussian with parameter `‖x‖²/k` and has variance
exactly `‖x‖²/k`. This works for any sub-Gaussian distribution
(Rademacher, bounded, etc.).

Inherits the Hanson-Wright axiom from `jl_concentration_single_subgaussian`. -/
theorem johnson_lindenstrauss_of_subgaussian (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (h_proj_meas : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin k),
        Measurable (fun ω => (A ω).toEuclideanLin x i))
    (h_proj_indep : ∀ x : EuclideanSpace ℝ (Fin d),
        iIndepFun (fun (i : Fin k) ω => (A ω).toEuclideanLin x i) μ)
    (h_proj_subG : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) (t : ℝ),
        Integrable (fun ω => Real.exp (t * (A ω).toEuclideanLin x i)) μ ∧
        mgf (fun ω => (A ω).toEuclideanLin x i) μ t ≤
          Real.exp ((‖x‖ ^ 2 / k) * t ^ 2 / 2))
    (h_proj_var : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin k),
        ∫ ω, ((A ω).toEuclideanLin x i) ^ 2 ∂μ = ‖x‖ ^ 2 / k)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
        MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hFail : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: Concentration per pair (case-split on u = v ↔ u − v = 0).
  have hPair : ∀ u ∈ V, ∀ v ∈ V,
      (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
    intro u _ v _
    by_cases huv : u - v = 0
    · -- When `u − v = 0`, the bad event is empty (`concentration_zero`).
      rw [huv]
      exact concentration_zero μ A ε
    · exact jl_concentration_single_subgaussian hk_pos μ A (u - v) huv
        (h_proj_meas (u - v)) (h_proj_indep (u - v))
        (h_proj_subG (u - v)) (h_proj_var (u - v)) ε hε_pos hε_lt
  -- Step 2: Union bound over pairs (identical to Gaussian path).
  have hBP : (μ {ω | BadPair ε V (A ω)}).toReal ≤
      (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :=
    jl_union_bound μ A hA_meas V ε hBadMeas hPair
  -- Step 3-5: same probabilistic-method extraction as the Gaussian version.
  have hBadLT1 : (μ {ω | BadPair ε V (A ω)}).toReal < 1 := lt_of_le_of_lt hBP hFail
  have hGood : ∃ ω, ¬ BadPair ε V (A ω) := by
    by_contra hNG
    push_neg at hNG
    have hUniv : {ω | BadPair ε V (A ω)} = Set.univ :=
      Set.eq_univ_of_forall hNG
    rw [hUniv, measure_univ] at hBadLT1
    simp at hBadLT1
  obtain ⟨ω, hω⟩ := hGood
  refine ⟨(A ω).toEuclideanLin, ?_⟩
  intro u hu v hv
  by_contra hbd
  exact hω ⟨u, hu, v, hv, hbd⟩

/-! ## §5. Measurability of the bad-single event

For the main theorem we need the per-pair bad events to be measurable. This
follows from the measurability of `A` and the continuity of the maps
`M ↦ ‖M.toEuclideanLin x‖²` and `r ↦ |r - ‖x‖²|`. -/

/-- The map `M ↦ (M.toEuclideanLin x) i` is measurable for each coordinate
`i`, hence so is the composition `M ↦ ‖M.toEuclideanLin x‖²`. -/
lemma measurableSet_badSingle
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ) (hA : Measurable A)
    (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    MeasurableSet {ω | BadSingle ε (A ω) x} := by
  -- `BadSingle ε M x` is `ε * ‖x‖² < |‖M.toEuclideanLin x‖² - ‖x‖²|`.
  -- Each entry (A ω) i j = (A ω).get i j is measurable in ω.
  -- Hence M ↦ (M.toEuclideanLin x) i = ∑ j, M i j * x j is measurable.
  -- Hence ‖M.toEuclideanLin x‖² = ∑ i, ((M.toEuclideanLin x) i)² is measurable.
  -- The full predicate is then `measurable_lt` applied to constant and measurable fns.
  have hentries : ∀ i j, Measurable (fun ω => (A ω) i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  have hmulvec : ∀ i, Measurable (fun ω => (A ω).toEuclideanLin x i) := by
    intro i
    -- (toEuclideanLin M) x i = ∑ j, M i j * x j (via `toLin'` / `mulVec` def)
    have heq : (fun ω => (A ω).toEuclideanLin x i) =
        fun ω => ∑ j, (A ω) i j * x j := by
      funext ω
      change ((A ω).toEuclideanLin x : Fin k → ℝ) i = _
      rfl
    rw [heq]
    exact Finset.measurable_sum _ (fun j _ => (hentries i j).mul_const _)
  have hnorm_sq : Measurable (fun ω => ‖(A ω).toEuclideanLin x‖ ^ 2) := by
    have heq : (fun ω => ‖(A ω).toEuclideanLin x‖ ^ 2) =
        fun ω => ∑ i, ((A ω).toEuclideanLin x i) ^ 2 := by
      funext ω
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (by positivity)]
      simp [sq_abs]
    rw [heq]
    exact Finset.measurable_sum _ (fun i _ => (hmulvec i).pow_const _)
  have hdiff : Measurable (fun ω => |‖(A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|) :=
    (hnorm_sq.sub measurable_const).abs
  exact measurableSet_lt measurable_const hdiff

/-! ## §6. Concrete sample-space construction (Gaussian)

The following lemma packages the existence of a probability space carrying
an iid `N(0, 1/k)` Gaussian random matrix. The construction uses the
**nested** product measure
`MeasureTheory.Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ))`
on `Fin k → Fin d → ℝ`. This shape gives, for free via `iIndepFun_pi`:
* Each entry has marginal law `gaussianReal 0 (1/k)`,
* Within a row, the entries are iid (inner pi),
* The rows (as vector-valued random variables) are iid (outer pi).

The third statement — rows iid — is the hypothesis we need for the
chi-squared concentration argument; the within-row iid is needed for the
row-distribution computation. -/
lemma exists_iid_gaussian_matrix (hk_pos : 0 < k) (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ)
      (A : Ω → Matrix (Fin k) (Fin d) ℝ),
      Measurable A ∧
      (∀ (i : Fin k) (j : Fin d),
        Measure.map (fun ω => A ω i j) μ =
          gaussianReal 0 ⟨1 / k, by positivity⟩) ∧
      (∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ) ∧
      iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ := by
  -- Sample space: `Fin k → Fin d → ℝ` with nested product Gaussian measure.
  set σ : NNReal := ⟨1 / k, by positivity⟩
  refine ⟨Fin k → Fin d → ℝ, inferInstance,
    Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)),
    inferInstance,
    fun ω i j => ω i j,
    ?_, ?_, ?_, ?_⟩
  · -- Measurable A
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)
  · -- Entry marginal: each `(ω i j)` has law `gaussianReal 0 σ`.
    intro i j
    -- Compose the two coordinate projections.
    -- Step 1: Marginal of the i-th row is `Measure.pi (fun _ => gaussianReal 0 σ)`.
    have hrow : Measure.map (fun (ω : Fin k → Fin d → ℝ) => ω i)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = Measure.pi (fun _ : Fin d => gaussianReal 0 σ) :=
      (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin k =>
        Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) i).map_eq
    -- Step 2: Marginal of the j-th coord of the i-th row is `gaussianReal 0 σ`.
    have hcoord : Measure.map (fun (r : Fin d → ℝ) => r j)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) = gaussianReal 0 σ :=
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin d => gaussianReal 0 σ) j).map_eq
    -- Compose: map (ω ↦ ω i j) = (map (ω ↦ ω i)) ∘ (map (r ↦ r j)).
    have : (fun (ω : Fin k → Fin d → ℝ) => ω i j) =
        (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
        hrow, hcoord]
  · -- Within-row entries iid: for each i, `iIndepFun (j ↦ ω i j)` under the outer pi.
    intro i
    -- The i-th row's marginal is the inner pi (i.e., iid Gaussian over Fin d).
    have hrow : Measure.map (fun (ω : Fin k → Fin d → ℝ) => ω i)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = Measure.pi (fun _ : Fin d => gaussianReal 0 σ) :=
      (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin k =>
        Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) i).map_eq
    -- Each entry marginal is `gaussianReal 0 σ`.
    have hentry_marginal : ∀ j : Fin d, Measure.map
        (fun (ω : Fin k → Fin d → ℝ) => ω i j)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = gaussianReal 0 σ := by
      intro j
      have heq : (fun (ω : Fin k → Fin d → ℝ) => ω i j) =
          (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
      rw [heq, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
          hrow]
      exact (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin d => gaussianReal 0 σ) j).map_eq
    -- Use `iIndepFun_iff_map_fun_eq_pi_map`: it suffices to check the joint = product.
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun j => Measurable.aemeasurable (by fun_prop))]
    -- LHS: joint distribution of (j ↦ ω i j) is `Measure.pi (fun _ => σ)` (= the i-th row).
    have hLHS : Measure.map (fun (ω : Fin k → Fin d → ℝ) (j : Fin d) => ω i j)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = Measure.pi (fun _ : Fin d => gaussianReal 0 σ) := by
      have hfn : (fun (ω : Fin k → Fin d → ℝ) (j : Fin d) => ω i j) = fun ω => ω i := rfl
      rw [hfn, hrow]
    rw [hLHS]
    -- RHS: product of marginals is also `Measure.pi (fun _ => σ)`.
    congr 1
    funext j
    exact (hentry_marginal j).symm
  · -- Rows iid: outer pi's `iIndepFun_pi`.
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-! ## §7. Headline theorems

The headline JL flattening lemma in two flavours:

* `johnson_lindenstrauss` — Gaussian random matrix (axiom-free).
* `johnson_lindenstrauss_subgaussian` — Rademacher random matrix
  (inherits the Hanson-Wright axiom from `rademacher.lean`).

Both share the same proof skeleton (numerical bookkeeping →
union-bound failure prob < 1 → probabilistic method) extracted as the
private helper `jl_failure_bound_of_dim`. The only difference is which
random matrix realizes the concentration bound. -/

/-- Numerical bookkeeping common to both headline JL theorems.

Given the JL dimension hypothesis `k ≥ 32·log n / ε²` together with
`V.card ≤ n` and the basic positivity hypotheses on `ε` and `n`, derives:

* `0 < k` (so the random matrix has nonzero rows), and
* `(V.card)² · 2 · exp(−kε²/8) < 1` (the union-bound failure probability
  is strictly less than `1`, which is exactly what
  `johnson_lindenstrauss_of_gaussian` / `_of_subgaussian` consume).

The constant `32` is chosen so that `|V|² · 2 · exp(−kε²/8) ≤ 1/2`,
keeping the calculation clean. Tighter constants (Dasgupta–Gupta 2003
get `4`) work but make the bookkeeping noisier. -/
private lemma jl_failure_bound_of_dim
    (ε : ℝ) (hε_pos : 0 < ε)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    0 < k ∧ (V.card : ℝ) ^ 2 *
        (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_n_pos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hε_sq_pos : 0 < ε ^ 2 := by positivity
  -- Step (a): kε²/8 ≥ 4 log n.
  have hk_lb : 4 * Real.log n ≤ (k : ℝ) * ε ^ 2 / 8 := by
    have := (div_le_iff₀ hε_sq_pos).mp hk
    nlinarith
  -- Step (b): 0 < k.
  have hk_real_pos : 0 < (k : ℝ) := by
    have : 0 < (k : ℝ) * ε ^ 2 / 8 :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * Real.log n) hk_lb
    nlinarith
  have hk_pos : 0 < k := by exact_mod_cast hk_real_pos
  -- Step (c): exp(-kε²/8) ≤ n^{-4}.
  have hexp_bound : Real.exp (-(k : ℝ) * ε ^ 2 / 8) ≤ (n : ℝ) ^ (-(4 : ℤ)) := by
    have h1 : -(k : ℝ) * ε ^ 2 / 8 ≤ -(4 * Real.log n) := by linarith
    calc Real.exp (-(k : ℝ) * ε ^ 2 / 8)
        ≤ Real.exp (-(4 * Real.log n)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (Real.log n * (-(4 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ (-(4 : ℝ)) := by rw [Real.rpow_def_of_pos hn_pos]
      _ = (n : ℝ) ^ (-(4 : ℤ)) := by
          rw [show (-(4 : ℝ)) = ((-(4 : ℤ) : ℤ) : ℝ) from by norm_cast]
          rw [← Real.rpow_intCast]
  -- Step (d): V.card² · 2 · exp(-kε²/8) ≤ 2/n² ≤ 1/2 < 1.
  have hFail : (V.card : ℝ) ^ 2 *
      (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
    have hcard_sq_le : (V.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hcard_nn : (0 : ℝ) ≤ V.card := by positivity
      have hcard_le : (V.card : ℝ) ≤ n := by exact_mod_cast hV
      exact pow_le_pow_left₀ hcard_nn hcard_le 2
    have h1 : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
            ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) := by
      have hrhs_nn : 0 ≤ 2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by positivity
      exact mul_le_mul hcard_sq_le
        (mul_le_mul_of_nonneg_left hexp_bound (by norm_num : (0 : ℝ) ≤ 2))
        hrhs_nn (by positivity)
    have h2 : (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) = 2 / (n : ℝ) ^ 2 := by
      rw [zpow_neg, zpow_ofNat]; field_simp
    have h3 : (2 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
      have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have hn_sq_ge : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hn_sq_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
        ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) := h1
      _ = 2 / (n : ℝ) ^ 2 := h2
      _ ≤ 1 / 2 := h3
      _ < 1 := by norm_num
  exact ⟨hk_pos, hFail⟩

/-- **Johnson–Lindenstrauss flattening lemma (standard form).**

For any `0 < ε < 1`, any `n ≥ 2`, and target dimension `k` with
`k ≥ 32 · log n / ε²`, every finite set `V` of at most `n` points in `ℝ^d`
admits a linear embedding `f : ℝ^d → ℝ^k` preserving pairwise squared
distances up to factor `(1 ± ε)`.

The `32` constant is not tight; the classical bound uses `O(log n / ε²)`
with a smaller leading constant (Dasgupta–Gupta 2003 get `4` using a
slightly different concentration bound). We chose `32` for cleanness of the
numerical bookkeeping: it gives `|V|² · 2 · exp(-kε²/8) ≤ 1/2`. -/
theorem johnson_lindenstrauss
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Numerical bookkeeping: k > 0 and union-bound failure prob < 1.
  obtain ⟨hk_pos, hFail⟩ :=
    jl_failure_bound_of_dim ε hε_pos n hn hk V hV
  -- Obtain a Gaussian probability space and invoke `_of_gaussian`.
  obtain ⟨Ω, _, μ, _, A, hA_meas, hA_law, hRowEntryIndep, hRowsIndep⟩ :=
    exists_iid_gaussian_matrix hk_pos d
  have hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (A ω) (u - v)} :=
    fun u _ v _ => measurableSet_badSingle A hA_meas (u - v) ε
  exact johnson_lindenstrauss_of_gaussian hk_pos μ A hA_meas hA_law
    hRowEntryIndep hRowsIndep ε hε_pos hε_lt V hBadMeas hFail

/-- **Johnson–Lindenstrauss flattening lemma — sub-Gaussian version.**

Same conclusion as `johnson_lindenstrauss`, but instantiated with a
Rademacher (`±1/√k`) random matrix instead of a Gaussian one. The proof
chain is identical at the union-bound + probabilistic-method level; only
the per-distribution input to `johnson_lindenstrauss_of_subgaussian`
changes — Rademacher row projections are sub-Gaussian with parameter
`‖x‖²/k` (Hoeffding + sum) and have variance exactly `‖x‖²/k`
(`IndepFun.variance_sum`).

This recovers Achlioptas's `±1`-entries variant of JL with the same
`32 · log n / ε²` dimension bound. **Inherits** the Hanson-Wright axiom
from `jl_concentration_single_subgaussian` (the only project-local
axiom). -/
theorem johnson_lindenstrauss_subgaussian
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Numerical bookkeeping: k > 0 and union-bound failure prob < 1.
  obtain ⟨hk_pos, hFail⟩ :=
    jl_failure_bound_of_dim ε hε_pos n hn hk V hV
  -- Use the explicit Rademacher matrix on the joint Pi-Rademacher measure.
  have hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (radMatrix k d ω) (u - v)} :=
    fun u _ v _ => measurableSet_badSingle (radMatrix k d)
      (measurable_radMatrix k d) (u - v) ε
  refine johnson_lindenstrauss_of_subgaussian hk_pos (radJointMeasure k d)
    (radMatrix k d) (measurable_radMatrix k d)
    (radMatrix_proj_meas k d) (radMatrix_proj_indep k d) ?_ ?_
    ε hε_pos hε_lt V hBadMeas hFail
  · intro x i t
    have h_sub := hasSubgaussianMGF_row_proj k d hk_pos x i
    refine ⟨h_sub.integrable_exp_mul t, ?_⟩
    simpa using h_sub.mgf_le t
  · intro x i
    exact integral_sq_row_proj k d hk_pos x i

/-! ## §8. Corollaries

Each corollary comes in two parallel flavours: a Gaussian one (axiom-free)
and a sub-Gaussian one (using the Rademacher matrix, inheriting the
Hanson-Wright axiom). They share the same post-processing helper
`jl_dist_of_embedding`. -/

/-- Square-root the squared-distance bound to get the distance form.
This is purely a post-processing step — it doesn't depend on which
distribution produced the embedding. Used by both Gaussian and
sub-Gaussian distance-form corollaries. -/
private lemma jl_dist_of_embedding
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    {V : Finset (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    (hf : IsJLEmbedding ε V f) :
    ∀ u ∈ V, ∀ v ∈ V,
      Real.sqrt (1 - ε) * ‖u - v‖ ≤ ‖f u - f v‖ ∧
      ‖f u - f v‖ ≤ Real.sqrt (1 + ε) * ‖u - v‖ := by
  intro u hu v hv
  have hdist : JLDistortion ε u v (f u) (f v) := hf u hu v hv
  have hε1 : 0 ≤ 1 - ε := by linarith
  have hε2 : 0 ≤ 1 + ε := by linarith
  have hfuv_nonneg : 0 ≤ ‖f u - f v‖ := norm_nonneg _
  have huv_nonneg : 0 ≤ ‖u - v‖ := norm_nonneg _
  refine ⟨?_, ?_⟩
  · have hsq : Real.sqrt ((1 - ε) * ‖u - v‖ ^ 2) ≤ ‖f u - f v‖ := by
      rw [show (‖f u - f v‖ : ℝ) = Real.sqrt (‖f u - f v‖ ^ 2) from
        (Real.sqrt_sq hfuv_nonneg).symm]
      exact Real.sqrt_le_sqrt hdist.1
    calc Real.sqrt (1 - ε) * ‖u - v‖
        = Real.sqrt (1 - ε) * Real.sqrt (‖u - v‖ ^ 2) := by
          rw [Real.sqrt_sq huv_nonneg]
      _ = Real.sqrt ((1 - ε) * ‖u - v‖ ^ 2) := by
          rw [← Real.sqrt_mul hε1]
      _ ≤ ‖f u - f v‖ := hsq
  · have hsq : ‖f u - f v‖ ≤ Real.sqrt ((1 + ε) * ‖u - v‖ ^ 2) := by
      rw [show (‖f u - f v‖ : ℝ) = Real.sqrt (‖f u - f v‖ ^ 2) from
        (Real.sqrt_sq hfuv_nonneg).symm]
      exact Real.sqrt_le_sqrt hdist.2
    calc ‖f u - f v‖ ≤ Real.sqrt ((1 + ε) * ‖u - v‖ ^ 2) := hsq
      _ = Real.sqrt (1 + ε) * Real.sqrt (‖u - v‖ ^ 2) := by
          rw [Real.sqrt_mul hε2]
      _ = Real.sqrt (1 + ε) * ‖u - v‖ := by rw [Real.sqrt_sq huv_nonneg]

/-- **Distance form (Gaussian).** Same conclusion as `johnson_lindenstrauss`,
stated in terms of Euclidean distances rather than squared distances (by
taking square roots). -/
theorem johnson_lindenstrauss_dist
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ u ∈ V, ∀ v ∈ V,
        Real.sqrt (1 - ε) * ‖u - v‖ ≤ ‖f u - f v‖ ∧
        ‖f u - f v‖ ≤ Real.sqrt (1 + ε) * ‖u - v‖ := by
  obtain ⟨f, hf⟩ := johnson_lindenstrauss ε hε_pos hε_lt n hn hk V hV
  exact ⟨f, jl_dist_of_embedding hε_pos hε_lt hf⟩

/-- **Distance form (sub-Gaussian).** Same as `johnson_lindenstrauss_dist`
but using the Rademacher matrix (inherits the Hanson-Wright axiom). -/
theorem johnson_lindenstrauss_subgaussian_dist
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ u ∈ V, ∀ v ∈ V,
        Real.sqrt (1 - ε) * ‖u - v‖ ≤ ‖f u - f v‖ ∧
        ‖f u - f v‖ ≤ Real.sqrt (1 + ε) * ‖u - v‖ := by
  obtain ⟨f, hf⟩ :=
    johnson_lindenstrauss_subgaussian ε hε_pos hε_lt n hn hk V hV
  exact ⟨f, jl_dist_of_embedding hε_pos hε_lt hf⟩

/-- **Dimension bound (Gaussian).** The minimal target dimension is
logarithmic in `n` and inverse-quadratic in `ε`. -/
theorem johnson_lindenstrauss_dim_bound
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∀ (d : ℕ) (V : Finset (EuclideanSpace ℝ (Fin d))), V.card ≤ n →
        ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
          IsJLEmbedding ε V f := by
  refine ⟨⌈(32 : ℝ) * Real.log n / ε ^ 2⌉₊, ?_⟩
  intro k hk d V hV
  have hk' : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
  exact johnson_lindenstrauss ε hε_pos hε_lt n hn hk' V hV

/-- **Dimension bound (sub-Gaussian).** Same as
`johnson_lindenstrauss_dim_bound` but using the Rademacher matrix
(inherits the Hanson-Wright axiom). -/
theorem johnson_lindenstrauss_subgaussian_dim_bound
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∀ (d : ℕ) (V : Finset (EuclideanSpace ℝ (Fin d))), V.card ≤ n →
        ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
          IsJLEmbedding ε V f := by
  refine ⟨⌈(32 : ℝ) * Real.log n / ε ^ 2⌉₊, ?_⟩
  intro k hk d V hV
  have hk' : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
  exact johnson_lindenstrauss_subgaussian ε hε_pos hε_lt n hn hk' V hV

end JohnsonLindenstrauss
