/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/

import TCSlib.LearningTheory.JohnsonLindenstrauss.RowDistribution
import TCSlib.LearningTheory.JohnsonLindenstrauss.ChiSquaredMGF

/-!
# Concentration Bound for the Johnson–Lindenstrauss Random Projection

## Main definitions

- (none; this file contains only theorems)

## Main results

- `jl_concentration_single_via_chi_squared`: main JL single-vector bound via chi-squared
  reduction
- `jl_concentration_single_via_bernstein`: distribution-agnostic JL concentration via
  Bernstein tails

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

/-- **Single-vector JL concentration for iid Gaussian matrices.** Let `A` be a random
`k × d` matrix (`k > 0`) whose entries are iid `N(0, 1/k)` — formally: `A` is measurable,
each entry has law `N(0, 1/k)`, the entries within each row are mutually independent, and
the rows are mutually independent. Then for every fixed vector `x` and every `0 < ε < 1`,

  `ℙ[ ε‖x‖² < |‖Ax‖² − ‖x‖²| ] ≤ 2·exp(−kε²/8)`.

This is [DG03, Lemma 2.2] (with the two-sided bound noted at `chi_squared_tail`) and the
analogue of [Ver18, Lemma 5.3.2]. Deviation: the sources treat a random orthogonal
projection (and [Ver18] an unspecified constant `c`); here the iid-Gaussian-matrix variant
with the explicit two-sided constant `2·exp(−kε²/8)`, cf. [Ver18, §5.3].

**Proof sketch.** If `x = 0` the bad event is empty (`concentration_zero`). Otherwise
`‖x‖ > 0` and: Step 1: set `Y i = (Ax)_i = ∑ j, A i j · x j`; by
`sum_scaled_iid_gaussian_map` applied to the `i`-th row, each `Y i` has law
`N(0, ‖x‖²/k)`. Step 2: by `rows_indep` the `Y i` are mutually independent. Step 3: set
`Z i = Y i / ‖x‖`; by `map_const_mul_gaussian` each `Z i` has law `N(0, 1/k)`, and
independence is preserved. Step 4: `‖Ax‖² = ∑ i, (Y i)² = ‖x‖² · ∑ i, (Z i)²`
(`norm_sq_toEuclideanLin`). Step 5: hence the bad event
`ε‖x‖² < |‖Ax‖² − ‖x‖²|` is the event `ε < |∑ i, (Z i)² − 1|`, dividing by `‖x‖² > 0`.
Step 6: apply the chi-squared tail bound `chi_squared_tail` to `Z`. -/
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
  -- Otherwise ‖x‖ > 0; the numbered steps below follow the proof sketch in the
  -- docstring.
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_norm_sq_pos : 0 < ‖x‖ ^ 2 := by positivity
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  -- Helper: ‖x‖² = ∑ j, (x j)²
  have hxnorm_sq : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [sq_abs]
  -- Step 1: define `Y i := (A·).toEuclideanLin x i` and establish its
  -- distribution.
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
  -- Step 2: rows are independent as scalar projections.
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
  -- Step 4: `∑ i, (Y i)² = ‖x‖² · ∑ i, (Z i)²`.
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
  -- Step 5: the bad event matches `{ω | ε < |∑ i, (Z i ω)² - 1|}`.
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

Let `A` be a random `k × d` matrix (`k > 0`) and `x` a fixed vector such that the
row-projections `(Ax)_i` are measurable and mutually independent, and each centered
squared projection `((Ax)_i)² − ‖x‖²/k` has a Bernstein-type MGF with parameters
`(c, tmax)`, `c > 0`. Then for every `s` with `0 ≤ s ≤ 2k·c·tmax`,

  `ℙ[ s < |‖Ax‖² − ‖x‖²| ] ≤ 2·exp(−s²/(4kc))`.

This is Bernstein's inequality [Ver18, Thm 2.8.1] in abstract form, applied to the
centered row-squares. Deviation from the source: the statement is parametric in a
`HasBernsteinMGF` hypothesis on the centered row-squares rather than in a
sub-exponential norm, and no distribution on the matrix entries is assumed. The Gaussian
case recovers `2 · exp(−k ε² / 8)` with `s = ε‖x‖²`, `c = 2 ‖x‖⁴ / k²`,
`tmax = k / (4 ‖x‖²)`, `ε ≤ 1`.

**Proof sketch.** Step 1: apply the abstract centered-squared tail bound
`centered_squared_iid_tail` to the row projections with `σ² = ‖x‖²/k`. Step 2: the bad
event matches, since `‖Ax‖² − ‖x‖² = ∑ i, ((Ax)_i)² − k · (‖x‖²/k)` by
`norm_sq_toEuclideanLin`. -/
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
  -- Step 1: apply the abstract centered-squared tail with σ² := ‖x‖²/k.
  have h_concentration := centered_squared_iid_tail h_proj_meas h_proj_indep hc h_bern
    s hs_pos (by simp only [Fintype.card_fin]; exact hs_le)
  -- Step 2: the bad event matches.
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
