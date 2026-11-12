/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import TCSlib.LearningTheory.JohnsonLindenstrauss.UnionBound
import TCSlib.LearningTheory.JohnsonLindenstrauss.Rademacher

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Johnson–Lindenstrauss Lemma

## Main definitions

- (none; this file contains only theorems and lemmas)

## Main results

- `measurableSet_badSingle`: Measurability of the per-pair bad event.
- `exists_iid_gaussian_matrix`: Existence of an iid Gaussian random matrix on a product
  probability space.
- `johnson_lindenstrauss`: JL flattening lemma with Gaussian matrix and explicit
  `k ≥ 32·log n/ε²` bound.
- `johnson_lindenstrauss_subgaussian`: JL flattening lemma with Rademacher matrix.
- `johnson_lindenstrauss_dist`: Distance form of the Gaussian JL lemma.
- `johnson_lindenstrauss_subgaussian_dist`: Distance form of the sub-Gaussian JL lemma.
- `johnson_lindenstrauss_dim_bound`: Logarithmic dimension bound for the Gaussian variant.
- `johnson_lindenstrauss_subgaussian_dim_bound`: Logarithmic dimension bound for the
  sub-Gaussian variant.

## References

* [JL84] W. B. Johnson, J. Lindenstrauss, "Extensions of Lipschitz mappings into a Hilbert
  space", *Contemp. Math.* 26:189–206, 1984.
* [DG03] S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and
  Lindenstrauss", *Random Structures & Algorithms* 22(1):60–65, 2003.
* [Ach03] D. Achlioptas, "Database-friendly random projections: Johnson–Lindenstrauss with
  binary coins", *J. Comput. Syst. Sci.* 66(4):671–687, 2003.
* [Ver18] R. Vershynin, *High-Dimensional Probability: An Introduction with Applications in
  Data Science*, Cambridge University Press, 2018.

Original formalization by Ganesh Sankar.
-/

open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset

noncomputable section JohnsonLindenstrauss

variable {d k : ℕ}

/-! ## §5. Measurability of the bad-single event

For the main theorem we need the per-pair bad events to be measurable. This
follows from the measurability of `A` and the continuity of the maps
`M ↦ ‖M.toEuclideanLin x‖²` and `r ↦ |r - ‖x‖²|`. -/

/-- For a measurable random matrix `A` and any fixed `x ∈ ℝ^d` and `ε`, the bad event
`{ω | BadSingle ε (A ω) x} = {ω | ε‖x‖² < |‖A ω x‖² − ‖x‖²|}` is a measurable set.

**Proof sketch.** Step 1: each entry `ω ↦ A ω i j` is measurable (a coordinate projection
of the measurable `A`). Step 2: each coordinate of the projection,
`ω ↦ (A ω x) i = Σⱼ A ω i j · x j`, is measurable as a finite sum. Step 3: the squared norm
`‖A ω x‖² = Σᵢ ((A ω x) i)²` is measurable as a finite sum of squares. Step 4: the event is
the strict inequality between the constant `ε‖x‖²` and the measurable function
`|‖A ω x‖² − ‖x‖²|`, hence measurable (`measurableSet_lt`). -/
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
  -- Step 1: each entry is measurable.
  have hentries : ∀ i j, Measurable (fun ω => (A ω) i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  -- Step 2: each coordinate of the projection is a finite sum of entries times constants.
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
  -- Step 3: the squared norm is a finite sum of squares of the coordinates.
  have hnorm_sq : Measurable (fun ω => ‖(A ω).toEuclideanLin x‖ ^ 2) := by
    have heq : (fun ω => ‖(A ω).toEuclideanLin x‖ ^ 2) =
        fun ω => ∑ i, ((A ω).toEuclideanLin x i) ^ 2 := by
      funext ω
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (by positivity)]
      simp [sq_abs]
    rw [heq]
    exact Finset.measurable_sum _ (fun i _ => (hmulvec i).pow_const _)
  -- Step 4: the event is a strict inequality between a constant and a measurable function.
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

/-- For `k > 0` and any `d`, there exist a probability space `(Ω, μ)` and a measurable
random `k × d` matrix `A` on it whose entries `A ω i j` each have law `N(0, 1/k)`, are
mutually independent within each row, and whose rows (as `ℝ^d`-valued random variables) are
mutually independent — the iid-Gaussian variant of the random projections of [DG03] and
[Ver18, §5.3], realized on a concrete sample space.

**Proof sketch.** Step 1: on the nested product space `Fin k → Fin d → ℝ` with measure
`⊗ᵢ ⊗ⱼ N(0, 1/k)`, the law of the `i`-th row `ω ↦ ω i` is the inner product measure
`⊗ⱼ N(0, 1/k)` (`measurePreserving_eval`). Step 2: take this space, this measure, and
`A ω i j = ω i j`. Step 3: `A` is measurable, being built from coordinate projections.
Step 4: the entry `ω ↦ ω i j` is the `j`-th coordinate of the `i`-th row, so its law is the
`j`-th marginal of the inner product measure, namely `N(0, 1/k)`. Step 5: within row `i`,
the entries are independent because the joint law of `(ω i j)ⱼ` is the inner product
measure (Step 1), which is also the product of the entry marginals (Step 4)
(`iIndepFun_iff_map_fun_eq_pi_map`). Step 6: the rows are independent as coordinates of the
outer product measure (`iIndepFun_pi`). -/
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
  -- Step 1: marginal of the i-th row is the inner product measure
  -- `Measure.pi (fun _ => gaussianReal 0 σ)` (used by the entry-marginal and
  -- within-row-iid bullets below).
  have hrow : ∀ i : Fin k, Measure.map (fun (ω : Fin k → Fin d → ℝ) => ω i)
      (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
      = Measure.pi (fun _ : Fin d => gaussianReal 0 σ) := fun i =>
    (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin k =>
      Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) i).map_eq
  -- Step 2: the sample space, the nested product measure, and `A ω i j = ω i j`.
  refine ⟨Fin k → Fin d → ℝ, inferInstance,
    Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)),
    inferInstance,
    fun ω i j => ω i j,
    ?_, ?_, ?_, ?_⟩
  · -- Step 3: `A` is measurable.
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)
  · -- Step 4: entry marginal: each `(ω i j)` has law `gaussianReal 0 σ`.
    intro i j
    -- Compose the two coordinate projections.
    -- Marginal of the j-th coord of the i-th row is `gaussianReal 0 σ`.
    have hcoord : Measure.map (fun (r : Fin d → ℝ) => r j)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) = gaussianReal 0 σ :=
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin d => gaussianReal 0 σ) j).map_eq
    -- Compose: map (ω ↦ ω i j) = (map (ω ↦ ω i)) ∘ (map (r ↦ r j)).
    have : (fun (ω : Fin k → Fin d → ℝ) => ω i j) =
        (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
        hrow i, hcoord]
  · -- Step 5: within-row entries iid: for each i, `iIndepFun (j ↦ ω i j)` under the
    -- outer pi.
    intro i
    -- Each entry marginal is `gaussianReal 0 σ` (via the hoisted row marginal `hrow i`).
    have hentry_marginal : ∀ j : Fin d, Measure.map
        (fun (ω : Fin k → Fin d → ℝ) => ω i j)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = gaussianReal 0 σ := by
      intro j
      have heq : (fun (ω : Fin k → Fin d → ℝ) => ω i j) =
          (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
      rw [heq, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
          hrow i]
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
      rw [hfn, hrow i]
    rw [hLHS]
    -- RHS: product of marginals is also `Measure.pi (fun _ => σ)`.
    congr 1
    funext j
    exact (hentry_marginal j).symm
  · -- Step 6: rows iid: outer pi's `iIndepFun_pi`.
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-! ## §7. Headline theorems

The headline JL flattening lemma in two flavours:

* `johnson_lindenstrauss` — Gaussian random matrix.
* `johnson_lindenstrauss_subgaussian` — Rademacher random matrix
  (via the fully proved `subgaussian_centered_sq_bernstein` from
  `JohnsonLindenstrauss.SubGaussian`).

Both are proved with no project-local axioms.

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
keeping the calculation clean. Tighter constants ([DG03, Thm 2.1] gets
`4 (ε²/2 − ε³/3)⁻¹`) work but make the bookkeeping noisier.

**Proof sketch.** Step (a): from `k ≥ 32 ln n/ε²` deduce `kε²/8 ≥ 4 ln n`. Step (b): since
`ln n > 0` this forces `k > 0`. Step (c): `exp(−kε²/8) ≤ exp(−4 ln n) = n⁻⁴`. Step (d):
`|V|² · 2 · exp(−kε²/8) ≤ n² · 2 · n⁻⁴ = 2/n² ≤ 1/2 < 1` using `|V| ≤ n` and `n ≥ 2`. -/
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

/-- **Johnson–Lindenstrauss flattening lemma (standard form)** [DG03, Thm 2.1];
[Ver18, Thm 5.3.1]; origin [JL84, Lemma 1].

For any `0 < ε < 1`, any `n ≥ 2`, and target dimension `k` with
`k ≥ 32 · log n / ε²`, every finite set `V` of at most `n` points in `ℝ^d`
admits a linear embedding `f : ℝ^d → ℝ^k` preserving pairwise squared
distances up to factor `(1 ± ε)`. The embedding is a realization of a matrix with iid
`N(0, 1/k)` entries; the proof is axiom-free.

Deviation: the dimension bound is `k ≥ 32 · log n / ε²`, whereas [DG03] obtains
`k ≥ 4 (ε²/2 − ε³/3)⁻¹ log n` and [Ver18] states `k ≥ C ε⁻² log n` for an unspecified
constant; the conclusion is stated for squared distances (see
`johnson_lindenstrauss_dist` for the distance form). The `32` is not tight: it is chosen
for cleanness of the numerical bookkeeping, giving `|V|² · 2 · exp(-kε²/8) ≤ 1/2`.

**Proof sketch.** Step 1: numerical bookkeeping (`jl_failure_bound_of_dim`): the dimension
hypothesis gives `k > 0` and the union-bound failure probability `|V|² · 2 · exp(−kε²/8)`
is strictly less than `1`. Step 2: realize an iid `N(0, 1/k)` matrix `A` on a probability
space (`exists_iid_gaussian_matrix`) and check that its per-pair bad events are measurable
(`measurableSet_badSingle`). Step 3: the structural theorem
`johnson_lindenstrauss_of_gaussian` (single-vector concentration, union bound, probabilistic
method) extracts a good realization. -/
theorem johnson_lindenstrauss
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: numerical bookkeeping: k > 0 and union-bound failure prob < 1.
  obtain ⟨hk_pos, hFail⟩ :=
    jl_failure_bound_of_dim ε hε_pos n hn hk V hV
  -- Step 2: obtain a Gaussian probability space; the per-pair bad events are measurable.
  obtain ⟨Ω, _, μ, _, A, hA_meas, hA_law, hRowEntryIndep, hRowsIndep⟩ :=
    exists_iid_gaussian_matrix hk_pos d
  have hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (A ω) (u - v)} :=
    fun u _ v _ => measurableSet_badSingle A hA_meas (u - v) ε
  -- Step 3: invoke the structural theorem `_of_gaussian`.
  exact johnson_lindenstrauss_of_gaussian hk_pos μ A hA_meas hA_law
    hRowEntryIndep hRowsIndep ε hε_pos hε_lt V hBadMeas hFail

/-- **Johnson–Lindenstrauss flattening lemma — sub-Gaussian version** [Ach03, Thm 1.1].

For any `0 < ε < 1`, any `n ≥ 2`, and target dimension `k` with `k ≥ 32 · log n / ε²`,
every finite set `V` of at most `n` points in `ℝ^d` admits a linear embedding
`f : ℝ^d → ℝ^k` preserving pairwise squared distances up to factor `(1 ± ε)`; the embedding
is a realization of the Rademacher (`±1/√k`) random matrix `radMatrix k d` rather than a
Gaussian one.

Deviation: the dimension bound is the same `32 · log n / ε²` as in `johnson_lindenstrauss`
(Achlioptas obtains `k ≥ 4 (ε²/2 − ε³/3)⁻¹ log n` for `±1` entries by a direct moment
computation); the proof goes through the sub-Gaussian route, i.e. through
`jl_concentration_single_subgaussian` and the fully proved
`subgaussian_centered_sq_bernstein`, and uses no project-local axioms.

**Proof sketch.** Step 1: numerical bookkeeping (`jl_failure_bound_of_dim`) gives `k > 0`
and the union-bound failure probability `< 1`. Step 2: the per-pair bad events of the
measurable Rademacher matrix are measurable (`measurableSet_badSingle`). Step 3: apply the
structural theorem `johnson_lindenstrauss_of_subgaussian` to `radMatrix k d`: its row
projections are measurable and independent (`radMatrix_proj_meas`, `radMatrix_proj_indep`),
sub-Gaussian with parameter `‖x‖²/k` (`hasSubgaussianMGF_row_proj`, Hoeffding + sum of
independent sub-Gaussians), and have second moment exactly `‖x‖²/k`
(`integral_sq_row_proj`). -/
theorem johnson_lindenstrauss_subgaussian
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: numerical bookkeeping: k > 0 and union-bound failure prob < 1.
  obtain ⟨hk_pos, hFail⟩ :=
    jl_failure_bound_of_dim ε hε_pos n hn hk V hV
  -- Step 2: the explicit Rademacher matrix on the joint Pi-Rademacher measure has
  -- measurable per-pair bad events.
  have hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (radMatrix k d ω) (u - v)} :=
    fun u _ v _ => measurableSet_badSingle (radMatrix k d)
      (measurable_radMatrix k d) (u - v) ε
  -- Step 3: the structural theorem `_of_subgaussian`, fed the Rademacher row facts.
  refine johnson_lindenstrauss_of_subgaussian hk_pos (radJointMeasure k d)
    (radMatrix k d) (measurable_radMatrix k d)
    (radMatrix_proj_meas k d) (radMatrix_proj_indep k d) ?_ ?_
    ε hε_pos hε_lt V hBadMeas hFail
  · -- Row projections are sub-Gaussian with parameter `‖x‖²/k`.
    intro x i t
    have h_sub := hasSubgaussianMGF_row_proj k d hk_pos x i
    refine ⟨h_sub.integrable_exp_mul t, ?_⟩
    simpa using h_sub.mgf_le t
  · -- Row projections have second moment `‖x‖²/k`.
    intro x i
    exact integral_sq_row_proj k d hk_pos x i

/-! ## §8. Corollaries

Each corollary comes in two parallel flavours: a Gaussian one and a
sub-Gaussian one (using the Rademacher matrix and the proved Hanson–Wright-type
bound `subgaussian_centered_sq_bernstein`). They share the same post-processing helper
`jl_dist_of_embedding`. -/

/-- If `f` is an `ε`-JL embedding of `V` with `0 < ε < 1`, then for all `u, v ∈ V`,
`√(1 − ε) · ‖u − v‖ ≤ ‖f u − f v‖ ≤ √(1 + ε) · ‖u − v‖`: the distance form obtained by
taking square roots of the squared-distance bound. This is purely a post-processing step,
independent of which distribution produced the embedding, shared by the Gaussian and
sub-Gaussian distance-form corollaries.

**Proof sketch.** Step 1: unpack the squared-distance bound `JLDistortion` for the pair and
record that `1 − ε`, `1 + ε` and both norms are nonnegative. Step 2 (lower bound): write
`‖f u − f v‖ = √(‖f u − f v‖²)`, apply monotonicity of `√` to the lower distortion
inequality, and split `√((1 − ε)‖u − v‖²) = √(1 − ε) · ‖u − v‖`. Step 3 (upper bound): the
same with the upper distortion inequality and `√(1 + ε)`. -/
private lemma jl_dist_of_embedding
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    {V : Finset (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    (hf : IsJLEmbedding ε V f) :
    ∀ u ∈ V, ∀ v ∈ V,
      Real.sqrt (1 - ε) * ‖u - v‖ ≤ ‖f u - f v‖ ∧
      ‖f u - f v‖ ≤ Real.sqrt (1 + ε) * ‖u - v‖ := by
  intro u hu v hv
  -- Step 1: the squared-distance bound for the pair, and the nonnegativity facts.
  have hdist : JLDistortion ε u v (f u) (f v) := hf u hu v hv
  have hε1 : 0 ≤ 1 - ε := by linarith
  have hε2 : 0 ≤ 1 + ε := by linarith
  have hfuv_nonneg : 0 ≤ ‖f u - f v‖ := norm_nonneg _
  have huv_nonneg : 0 ≤ ‖u - v‖ := norm_nonneg _
  refine ⟨?_, ?_⟩
  · -- Step 2: lower bound, by taking square roots of the lower distortion inequality.
    have hsq : Real.sqrt ((1 - ε) * ‖u - v‖ ^ 2) ≤ ‖f u - f v‖ := by
      rw [show (‖f u - f v‖ : ℝ) = Real.sqrt (‖f u - f v‖ ^ 2) from
        (Real.sqrt_sq hfuv_nonneg).symm]
      exact Real.sqrt_le_sqrt hdist.1
    calc Real.sqrt (1 - ε) * ‖u - v‖
        = Real.sqrt (1 - ε) * Real.sqrt (‖u - v‖ ^ 2) := by
          rw [Real.sqrt_sq huv_nonneg]
      _ = Real.sqrt ((1 - ε) * ‖u - v‖ ^ 2) := by
          rw [← Real.sqrt_mul hε1]
      _ ≤ ‖f u - f v‖ := hsq
  · -- Step 3: upper bound, by taking square roots of the upper distortion inequality.
    have hsq : ‖f u - f v‖ ≤ Real.sqrt ((1 + ε) * ‖u - v‖ ^ 2) := by
      rw [show (‖f u - f v‖ : ℝ) = Real.sqrt (‖f u - f v‖ ^ 2) from
        (Real.sqrt_sq hfuv_nonneg).symm]
      exact Real.sqrt_le_sqrt hdist.2
    calc ‖f u - f v‖ ≤ Real.sqrt ((1 + ε) * ‖u - v‖ ^ 2) := hsq
      _ = Real.sqrt (1 + ε) * Real.sqrt (‖u - v‖ ^ 2) := by
          rw [Real.sqrt_mul hε2]
      _ = Real.sqrt (1 + ε) * ‖u - v‖ := by rw [Real.sqrt_sq huv_nonneg]

/-- **Distance form (Gaussian)** — the [JL84, Lemma 1] form, via [DG03, Thm 2.1].

For any `0 < ε < 1`, any `n ≥ 2`, and `k ≥ 32 · log n / ε²`, every finite set `V` of at
most `n` points in `ℝ^d` admits a linear map `f : ℝ^d → ℝ^k` with
`√(1 − ε) · ‖u − v‖ ≤ ‖f u − f v‖ ≤ √(1 + ε) · ‖u − v‖` for all `u, v ∈ V`. This is
`johnson_lindenstrauss` restated for Euclidean distances rather than squared distances (by
taking square roots, `jl_dist_of_embedding`); axiom-free. -/
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

/-- **Distance form (sub-Gaussian)** — the [JL84, Lemma 1] form, via [Ach03, Thm 1.1].

For any `0 < ε < 1`, any `n ≥ 2`, and `k ≥ 32 · log n / ε²`, every finite set `V` of at
most `n` points in `ℝ^d` admits a linear map `f : ℝ^d → ℝ^k` with
`√(1 − ε) · ‖u − v‖ ≤ ‖f u − f v‖ ≤ √(1 + ε) · ‖u − v‖` for all `u, v ∈ V`, the map being
a realization of the Rademacher matrix. This is `johnson_lindenstrauss_subgaussian`
restated for distances (`jl_dist_of_embedding`); fully proved, no project-local
axioms. -/
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

/-- **Dimension bound (Gaussian)** [DG03, Thm 2.1].

For any `0 < ε < 1` and `n ≥ 2` there is a threshold `k₀` (namely `⌈32 · log n / ε²⌉`)
such that for every `k ≥ k₀`, every ambient dimension `d`, and every set `V` of at most
`n` points in `ℝ^d`, there is a linear `ε`-JL embedding `ℝ^d → ℝ^k` of `V`: the target
dimension needed is logarithmic in `n` and inverse-quadratic in `ε`. Axiom-free. -/
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

/-- **Dimension bound (sub-Gaussian)** [DG03, Thm 2.1] with the matrix of [Ach03, Thm 1.1].

For any `0 < ε < 1` and `n ≥ 2` there is a threshold `k₀` (namely `⌈32 · log n / ε²⌉`)
such that for every `k ≥ k₀`, every ambient dimension `d`, and every set `V` of at most
`n` points in `ℝ^d`, there is a linear `ε`-JL embedding `ℝ^d → ℝ^k` of `V` realized by
the Rademacher matrix. Fully proved, no project-local axioms. -/
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
