/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples.Cubes
import TCSlib.BooleanAnalysis.GaussianSpace.Profile

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharpness of the Gaussian halfspace-count bound

## Main definitions

Uses upper coordinate cubes and the existing standard Gaussian quantile.

## Main results

* `exists_halfspace_count_surfaceArea_ge`: the `sqrt(log m)` lower bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50.
* [Naz03] F. Nazarov, On the maximal perimeter of a convex set in Rn with respect
  to a Gaussian measure, Geometric Aspects of Functional Analysis (2003), 169–187.
* [KOS08] A. Klivans, R. O'Donnell and R. Servedio, Learning geometric concepts
  via Gaussian surface area, FOCS (2008), 541–550.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions

/-- Keeping each coordinate with probability `1 - 1/(2m)` leaves the other
`m-1` coordinates inside with probability at least one half.

**Proof sketch.** Bernoulli's inequality gives the stronger bound
`1 - (m-1)/(2m) = 1/2 + 1/(2m)`. -/
private lemma cube_power_lower (m : ℕ) (hm : 2 ≤ m) :
    (1/2:ℝ) ≤ (1-1/(2*(m:ℝ)))^(m-1) := by
  let α : ℝ := 1/(2*(m:ℝ))
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hma : (m:ℝ)*α = 1/2 := by dsimp [α]; field_simp
  have hαle : α ≤ 1/2 := by nlinarith
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hbern : (1 / 2 : ℝ) ≤ (1 - α) ^ (m - 1) := by
    have hb := one_add_mul_le_pow (a := -α) (by linarith : (-2 : ℝ) ≤ -α) (m - 1)
    rw [hcast] at hb
    have heq : 1 + ((m : ℝ) - 1) * -α = 1 / 2 + α := by nlinarith [hma]
    rw [heq] at hb
    simpa only [sub_eq_add_neg] using
      (show (1 / 2 : ℝ) ≤ (1 + -α) ^ (m - 1) by linarith)
  exact hbern

/-- Gaussian cubes with marginal exclusion probability `1/(2m)` have the
candidate perimeter at least `sqrt(log m)/8` for all sufficiently large `m`.
[OD14, Example 11.50; KOS08]

**Proof sketch.** The existing Gaussian tail equivalence gives
`U(α) ≥ α sqrt(2 log(1/α))/2` near zero. Set `α = 1/(2m)` and compare the
logarithms. Bernoulli's inequality bounds the remaining product factor below
by one half. -/
private lemma cube_profile_eventually :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      (1 / 8 : ℝ) * Real.sqrt (Real.log (m : ℝ)) ≤
        (m : ℝ) * gaussianIsoperimetric (1 / (2 * (m : ℝ))) *
          (1 - 1 / (2 * (m : ℝ))) ^ (m - 1) := by
  have hev := gaussianIsoperimetric_equiv_at_zero.isLittleO.bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2 : ℝ) (1 / ε))
  have hMtwo : 2 ≤ M := by
    have := (le_max_left (2 : ℝ) (1 / ε)).trans_lt hM
    exact_mod_cast this.le
  refine ⟨M, hMtwo, fun m hmm => ?_⟩
  have hm : 2 ≤ m := hMtwo.trans hmm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  let α : ℝ := 1 / (2 * (m : ℝ))
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hma : (m : ℝ) * α = 1 / 2 := by dsimp [α]; field_simp
  have hmε : 1 / ε < (m : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hM).trans_le (by exact_mod_cast hmm)
  have hεm : 1 < ε * (m : ℝ) := by
    have := (div_lt_iff₀ hε).mp hmε
    nlinarith
  have hαε : α < ε := by
    dsimp [α]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (m : ℝ))).mpr
    nlinarith
  have hb := he (show dist α 0 < ε by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hαpos] using hαε) hαpos
  have hinv : α⁻¹ = 2 * (m : ℝ) := by dsimp [α]; simp
  have hlognonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (m : ℝ) ≤ Real.log α⁻¹ := by
    rw [hinv]
    exact Real.log_le_log hmpos (by nlinarith)
  have hgpos : 0 ≤ α * Real.sqrt (2 * Real.log α⁻¹) :=
    mul_nonneg hαpos.le (Real.sqrt_nonneg _)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hgpos] at hb
  have hU : α * Real.sqrt (2 * Real.log α⁻¹) / 2 ≤ gaussianIsoperimetric α := by
    have := (neg_le_abs (gaussianIsoperimetric α -
      α * Real.sqrt (2 * Real.log α⁻¹))).trans hb
    linarith
  have hroot : Real.sqrt (Real.log (m : ℝ)) ≤
      Real.sqrt (2 * Real.log α⁻¹) := Real.sqrt_le_sqrt (by linarith)
  have hmain : (1 / 4 : ℝ) * Real.sqrt (Real.log (m : ℝ)) ≤
      (m : ℝ) * gaussianIsoperimetric α := by
    calc
      _ ≤ ((m : ℝ) * α) / 2 * Real.sqrt (2 * Real.log α⁻¹) := by rw [hma]; nlinarith
      _ = (m : ℝ) * (α * Real.sqrt (2 * Real.log α⁻¹) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hU hmpos.le
  have hbern := cube_power_lower m hm
  have hUpos : 0 ≤ (m : ℝ) * gaussianIsoperimetric α :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.sqrt_nonneg _)).trans hmain
  change (1 / 8 : ℝ) * Real.sqrt (Real.log (m : ℝ)) ≤
    (m : ℝ) * gaussianIsoperimetric α * (1 - α) ^ (m - 1)
  calc
    _ = ((1 / 4 : ℝ) * Real.sqrt (Real.log (m : ℝ))) * (1 / 2) := by ring
    _ ≤ ((m : ℝ) * gaussianIsoperimetric α) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hmain (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hbern hUpos
/-- Intersections of `m ≥ 2` halfspaces attain Gaussian surface area at least
a universal positive constant times `sqrt(log m)`.
[OD14, Example 11.50; Naz03; KOS08]

**Proof sketch.** For large `m`, use a coordinate cube whose marginal Gaussian
exclusion probability is `1/(2m)`. Its explicit perimeter and the Gaussian
tail equivalence give the lower bound. For the finitely many smaller counts,
duplicate a fixed coordinate halfspace, shrinking the universal constant to
cover both cases. -/
theorem exists_halfspace_count_surfaceArea_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
      ∃ (n : ℕ) (a : Fin m → Fin n → ℝ) (t : Fin m → ℝ),
        ENNReal.ofReal (c * Real.sqrt (Real.log (m : ℝ))) ≤
          gaussianSurfaceArea {x : Fin n → ℝ | ∀ j, ∑ i, a j i * x i ≤ t j} := (by
  classical
  obtain ⟨M, hM, hlarge⟩ := cube_profile_eventually
  have hMR : (1:ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hrootM : 0 < Real.sqrt (Real.log (M:ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos hMR)
  let c : ℝ := min (1/8) (standardGaussianPDF 0 / Real.sqrt (Real.log (M:ℝ)))
  refine ⟨c, lt_min (by norm_num) (div_pos (standardGaussianPDF_pos 0) hrootM), ?_⟩
  intro m hm
  by_cases hbig : M ≤ m
  · let α : ℝ := 1/(2*(m:ℝ))
    have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hα : α ∈ Set.Ioo (0:ℝ) 1 := by
      constructor
      · dsimp [α]; positivity
      · dsimp [α]; apply (div_lt_one (by positivity)).2; linarith
    let t := standardGaussianQuantile (1-α)
    have ht : standardGaussianCDF t = 1-α :=
      standardGaussianCDF_quantile (by linarith [hα.2]) (by linarith [hα.1])
    have hpdf : standardGaussianPDF t = gaussianIsoperimetric α := by
      rw [← gaussianIsoperimetric_eq, gaussianIsoperimetric_one_sub hα]
    refine ⟨m, fun j => Pi.single j 1, fun _ => t, ?_⟩
    have hset : {x : Fin m → ℝ | ∀ j, ∑ i, (Pi.single j (1:ℝ) : Fin m → ℝ) i * x i ≤ t} =
        {x : Fin m → ℝ | ∀ j, x j ≤ t} := by
      simp [Pi.single_apply]
    rw [hset, surfaceArea_coordinate_cube, ht, hpdf]
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)).trans
      (hlarge m hbig)
  · refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
    have hset : {x : Fin 1 → ℝ | ∀ j : Fin m, ∑ i : Fin 1, (1:ℝ)*x i ≤ 0} =
        {x : Fin 1 → ℝ | x 0 ≤ 0} := by
      ext x
      simp only [Fin.sum_univ_one, one_mul, Set.mem_setOf_eq]
      constructor
      · intro h; exact h ⟨0, by omega⟩
      · intro h j; exact h
    have hhalf : gaussianSurfaceArea {x : Fin 1 → ℝ | x 0 ≤ 0} =
        ENNReal.ofReal (standardGaussianPDF 0) := by
      simpa using surfaceArea_halfspace (fun _ : Fin 1 => (1:ℝ)) (by simp) 0
    rw [hset, hhalf]
    apply ENNReal.ofReal_le_ofReal
    have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hle : Real.sqrt (Real.log (m:ℝ)) ≤ Real.sqrt (Real.log (M:ℝ)) :=
      Real.sqrt_le_sqrt (Real.log_le_log hmpos (by exact_mod_cast (by omega : m ≤ M)))
    calc
      c * Real.sqrt (Real.log (m:ℝ)) ≤
          (standardGaussianPDF 0 / Real.sqrt (Real.log (M:ℝ))) *
            Real.sqrt (Real.log (m:ℝ)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
      _ ≤ (standardGaussianPDF 0 / Real.sqrt (Real.log (M:ℝ))) *
          Real.sqrt (Real.log (M:ℝ)) :=
        mul_le_mul_of_nonneg_left hle (div_pos (standardGaussianPDF_pos 0) hrootM).le
      _ = standardGaussianPDF 0 := div_mul_cancel₀ _ (ne_of_gt hrootM)
)

end BooleanAnalysis.GaussianSpace
