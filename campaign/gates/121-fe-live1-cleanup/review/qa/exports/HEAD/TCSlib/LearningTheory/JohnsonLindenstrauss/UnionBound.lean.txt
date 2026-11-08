/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import TCSlib.LearningTheory.JohnsonLindenstrauss.ConcentrationBound
import TCSlib.LearningTheory.JohnsonLindenstrauss.SubGaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Union Bound for the Johnson–Lindenstrauss Lemma

## Main definitions

- `JLDistortion`: The `(1 ± ε)` two-sided distortion predicate for a single pair of points.
- `IsJLEmbedding`: A linear map `f : ℝ^d → ℝ^k` that preserves all pairwise squared distances
  up to factor `(1 ± ε)`.
- `BadPair`: The bad event that some pair in `V × V` is distorted by more than factor `ε`.

## Main results

- `jl_concentration_single`: Single-vector concentration bound for iid Gaussian matrices.
- `JLDistortion.of_not_bad`: Converts negation of `BadSingle` to `JLDistortion`.
- `jl_union_bound`: Union bound over all `|V|²` ordered pairs.
- `exists_isJLEmbedding_of_pair_bound`: Probabilistic-method extraction of an embedding from
  per-pair concentration and a failure probability below `1`.
- `johnson_lindenstrauss_of_gaussian`: Structural JL theorem via the probabilistic method
  (Gaussian).
- `johnson_lindenstrauss_of_subgaussian`: Structural JL theorem via the probabilistic method
  (sub-Gaussian).

## References

* [DG03] S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and
  Lindenstrauss", *Random Structures & Algorithms* 22(1):60–65, 2003.
* [Ver18] R. Vershynin, *High-Dimensional Probability: An Introduction with Applications in
  Data Science*, Cambridge University Press, 2018.
* [JL84] W. B. Johnson, J. Lindenstrauss, "Extensions of Lipschitz mappings into a Hilbert
  space", *Contemp. Math.* 26:189–206, 1984.

Original formalization by Ganesh Sankar.
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
-- `JohnsonLindenstrauss.RowDistribution`.)

/-- The `(1 ± ε)` two-sided distortion bound for a single pair of points: the squared
distance between the images `u'`, `v'` lies between `(1 − ε)` and `(1 + ε)` times the
squared distance between `u` and `v` [DG03, Thm 2.1]; origin [JL84]. Deviation: stated for
squared distances (the distance form is recovered in `JohnsonLindenstrauss.Main`). -/
def JLDistortion (ε : ℝ) (u v : EuclideanSpace ℝ (Fin d))
    (u' v' : EuclideanSpace ℝ (Fin k)) : Prop :=
  (1 - ε) * ‖u - v‖ ^ 2 ≤ ‖u' - v'‖ ^ 2 ∧
  ‖u' - v'‖ ^ 2 ≤ (1 + ε) * ‖u - v‖ ^ 2

/-- A linear map `f : ℝ^d → ℝ^k` is an **ε-JL embedding** of the finite set
`V` if it preserves all pairwise squared distances up to factor `(1 ± ε)`, i.e.
`JLDistortion ε u v (f u) (f v)` for all `u, v ∈ V` [DG03, Thm 2.1]; origin [JL84].
Deviation: only linear maps are considered, and distances are squared. -/
def IsJLEmbedding (ε : ℝ) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, JLDistortion ε u v (f u) (f v)

-- `BadSingle` is defined in `JohnsonLindenstrauss.RowDistribution`; re-exported here.

/-- The "bad event" for the whole set `V` under the matrix `A`: some ordered pair
`(u, v) ∈ V × V` fails the `(1 ± ε)` distortion bound `JLDistortion` under `A`
[DG03, proof of Thm 2.1]. -/
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

/-- **JL concentration (single vector)** [DG03, Lemma 2.2].

If `A_ij ~ N(0, 1/k)` are i.i.d. Gaussian (with rows mutually independent
and entries iid within each row), then for any fixed `x : ℝ^d` and any
`0 < ε < 1`,
`ℙ[ |‖Ax‖² − ‖x‖²| > ε · ‖x‖² ] ≤ 2 · exp(−k ε² / 8).`
Deviation: the two-sided bound `2 exp(−kε²/8)` replaces the source's
`exp(k/2 (1 − β + ln β))` tails (see `chi_squared_tail`).

This is a wrapper around `jl_concentration_single_via_chi_squared` from
`JohnsonLindenstrauss.ConcentrationBound`, fully proved (no axioms) via
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

/-- If the matrix `A` does not distort the difference vector `u − v` by more than a factor
`ε` (the negation of `BadSingle ε A (u − v)`), then the pair `(u, v)` satisfies the
`(1 ± ε)` distortion bound `JLDistortion` under `A`. -/
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

/-- **JL union bound** [DG03, proof of Thm 2.1].

Given that each pair's distortion event has probability `≤ 2·exp(−kε²/8)`,
the probability that *some* ordered pair in `V × V` is distorted is at most
`|V|² · 2 · exp(−kε²/8)`. Deviation: the union is over all `|V|²` ordered pairs (including
`u = v`) rather than the source's `C(n, 2)` unordered pairs; this only loosens the constant.

**Proof sketch.** Step 1: the bad-pair event is contained in the double union over
`u, v ∈ V` of the per-pair bad events `{ω | BadSingle ε (A ω) (u − v)}`, by
`JLDistortion.of_not_bad`. Step 2: monotonicity and finite subadditivity of the measure
(`measure_biUnion_finset_le`, applied twice) bound the measure of the bad-pair event by
the double sum of the per-pair measures. Step 3: all these measures are finite, so the
double sum passes to real numbers. Step 4: bound each of the `|V|²` real summands by
`2·exp(−kε²/8)` and collect. -/
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
  -- Step 1: the bad-pair event is contained in the union of per-pair bad-single events.
  have hsub : {ω | BadPair ε V (A ω)} ⊆
      ⋃ u ∈ V, ⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)} := by
    intro ω hω
    obtain ⟨u, hu, v, hv, hbad⟩ := hω
    refine Set.mem_iUnion₂.mpr ⟨u, hu, Set.mem_iUnion₂.mpr ⟨v, hv, ?_⟩⟩
    by_contra hnot
    exact hbad (JLDistortion.of_not_bad ε u v (A ω) hnot)
  -- Step 2: measure subadditivity over the finite double union.
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
  -- Step 3: all per-pair measures are finite (μ is a probability measure), so the
  -- double sum passes to `ℝ`.
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
    -- Step 4: bound each of the `|V|²` summands and collect.
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
   in `JohnsonLindenstrauss.Main` (`exists_iid_gaussian_matrix`). -/

/-- **Probabilistic method for JL (shared tail)** [DG03, proof of Thm 2.1];
[Ver18, proof of Thm 5.3.1].

Given a random matrix `A` whose per-pair distortion events
`{ω | BadSingle ε (A ω) (u − v)}` are measurable and each have probability at
most `2·exp(−kε²/8)`, and such that the union-bound failure probability
`|V|² · 2 · exp(−kε²/8)` is strictly less than `1`, some realization `A ω` is
an `ε`-JL embedding of `V`.

This is the common tail of `johnson_lindenstrauss_of_gaussian` and
`johnson_lindenstrauss_of_subgaussian`.

**Proof sketch.** Step 1: the union bound `jl_union_bound` bounds the probability of the
bad-pair event by `|V|² · 2 · exp(−kε²/8)`. Step 2: by hypothesis this is strictly less
than `1`. Step 3: hence some sample `ω` is not bad — otherwise the bad-pair event would be
the whole space, of probability `1`. Step 4: the linear map `(A ω).toEuclideanLin` of that
witness is an `ε`-JL embedding of `V`, since every pair satisfies the distortion bound. -/
theorem exists_isJLEmbedding_of_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (ε : ℝ)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
        MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hPair : ∀ u ∈ V, ∀ v ∈ V,
        (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
          2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
    (hFail : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: Union bound over pairs.
  have hBP : (μ {ω | BadPair ε V (A ω)}).toReal ≤
      (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :=
    jl_union_bound μ A hA_meas V ε hBadMeas hPair
  -- Step 2: Failure probability strictly less than 1.
  have hBadLT1 : (μ {ω | BadPair ε V (A ω)}).toReal < 1 := lt_of_le_of_lt hBP hFail
  -- Step 3: Therefore some ω is *not* bad.
  have hGood : ∃ ω, ¬ BadPair ε V (A ω) := by
    by_contra hNG
    push_neg at hNG
    have hUniv : {ω | BadPair ε V (A ω)} = Set.univ :=
      Set.eq_univ_of_forall hNG
    rw [hUniv, measure_univ] at hBadLT1
    simp at hBadLT1
  -- Step 4: Extract witness, produce embedding.
  obtain ⟨ω, hω⟩ := hGood
  refine ⟨(A ω).toEuclideanLin, ?_⟩
  intro u hu v hv
  by_contra hbd
  exact hω ⟨u, hu, v, hv, hbd⟩

/-- **Structural JL via the probabilistic method (Gaussian)** [DG03, proof of Thm 2.1];
[Ver18, proof of Thm 5.3.1].

Given a random matrix with iid `N(0, 1/k)` entries on a probability space (rows
independent, entries independent within each row) AND that the
union-bound failure probability `|V|² · 2 · exp(-kε²/8)` is strictly less
than `1`, there exists a realization of the random matrix that is an
`ε`-JL embedding of `V`.

**Proof sketch.** Step 1: the single-vector concentration bound
`jl_concentration_single`, applied to each difference `u − v` with `u, v ∈ V`, gives the
per-pair bound `2·exp(−kε²/8)`. Step 2: the shared probabilistic-method lemma
`exists_isJLEmbedding_of_pair_bound` (union bound, failure probability `< 1`, extraction of
a good sample) produces the embedding. -/
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
  -- Step 1: Concentration per pair (Gaussian single-vector bound).
  have hPair : ∀ u ∈ V, ∀ v ∈ V,
      (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := fun u _ v _ =>
    jl_concentration_single hk_pos μ A hA_meas hA_law hRowEntryIndep hRowsIndep
      (u - v) ε hε_pos hε_lt
  -- Step 2: Union bound and probabilistic method.
  exact exists_isJLEmbedding_of_pair_bound μ A hA_meas ε V hBadMeas hPair hFail

/-- **Structural sub-Gaussian JL via the probabilistic method** [DG03, proof of Thm 2.1];
[Ver18, proof of Thm 5.3.1].

Given a random matrix `A` on a probability space whose row projections `(Ax)_i` are, for
every `x`, measurable, mutually independent, sub-Gaussian with parameter `‖x‖²/k` and of
second moment exactly `‖x‖²/k`, AND that the union-bound failure probability
`|V|² · 2 · exp(-kε²/8)` is strictly less than `1`, some realization of `A` is an
`ε`-JL embedding of `V`. This is the sub-Gaussian analogue of
`johnson_lindenstrauss_of_gaussian` and applies to any sub-Gaussian entry distribution
(Rademacher, bounded, etc.). Goes through `jl_concentration_single_subgaussian` and the
fully proved `subgaussian_centered_sq_bernstein`; no project-local axioms.

**Proof sketch.** Step 1: per-pair concentration. For `u = v` the difference is `0` and the
bad event is empty (`concentration_zero`); otherwise `jl_concentration_single_subgaussian`
applied to `u − v` gives the bound `2·exp(−kε²/8)`. Step 2: the shared probabilistic-method
lemma `exists_isJLEmbedding_of_pair_bound` produces the embedding. -/
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
  -- Step 2: Union bound and probabilistic method (shared with the Gaussian path).
  exact exists_isJLEmbedding_of_pair_bound μ A hA_meas ε V hBadMeas hPair hFail

end JohnsonLindenstrauss
