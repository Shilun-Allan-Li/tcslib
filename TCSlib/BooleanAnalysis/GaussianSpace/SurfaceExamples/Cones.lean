/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples.Crossings
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Tauto

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian surface area of convex cones

## Main definitions

The existing Gaussian rotation sensitivity and surface area are used directly.

## Main results

* `surfaceArea_convex_cone_bound`: a measurable convex cone has surface area at most one.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50.
* [KOS08] A. Klivans, R. O'Donnell and R. Servedio, Learning geometric concepts
  via Gaussian surface area, FOCS (2008), 541–550.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- An order-convex Boolean sequence changes value at most twice.

**Proof sketch.** Distinct transition indices have distinct starting truth values:
otherwise order convexity fails between them. Inject the transition set into `Bool`. -/
private lemma count_changes (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hc : ∀ i j k, k ≤ N → i ≤ j → j ≤ k → P i → P k → P j) :
    (∑ i ∈ Finset.range N, if ¬(P i ↔ P (i+1)) then (1:ℝ) else 0) ≤ 2 := by
  classical
  let s := (Finset.range N).filter (fun i => ¬(P i ↔ P (i+1)))
  have hstrict : ∀ i ∈ s, ∀ j ∈ s, i < j → decide (P i) ≠ decide (P j) := by
    intro i hi j hj hij he
    obtain ⟨hiN, hiC⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjN, hjC⟩ := Finset.mem_filter.mp hj
    have hiN := Finset.mem_range.mp hiN
    have hjN := Finset.mem_range.mp hjN
    have heP : P i ↔ P j := by
      by_cases hiP : P i <;> by_cases hjP : P j <;> simp_all
    by_cases hiP : P i
    · have hjP := heP.mp hiP
      have hiNext : P (i+1) := hc i (i+1) j (by omega) (by omega) (by omega) hiP hjP
      exact hiC (by simp [hiP, hiNext])
    · have hjP : ¬P j := fun h => hiP (heP.mpr h)
      have hiNext : P (i+1) := by tauto
      have hjNext : P (j+1) := by tauto
      exact hjP (hc (i+1) j (j+1) (by omega) (by omega) (by omega) hiNext hjNext)
  have hcard : s.card ≤ 2 := by
    calc
      s.card ≤ (Finset.univ : Finset Bool).card :=
        Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool)) (fun i => decide (P i)) (by intro i hi; change decide (P i) ∈ (Finset.univ : Finset Bool); exact Finset.mem_univ (decide (P i)))
          (by
            intro i hi j hj he
            by_contra hne
            rcases lt_or_gt_of_ne hne with hij | hji
            · exact hstrict i hi j hj hij he
            · exact hstrict j hj i hi hji he.symm)
      _ = 2 := by decide
  rw [Finset.sum_boole]
  exact_mod_cast hcard

open MeasureTheory
open scoped BigOperators
/-- Sine interpolation expresses a rotation inside an arc of length less than π as
 a nonnegative combination of its endpoints. **Proof sketch.** expand sine differences and
cancel the nonzero sine denominator. -/
private lemma cone_arc_mem {n : ℕ} {A : Set (Fin n → ℝ)}
    (hconvex : Convex ℝ A)
    (hcone : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → t • x ∈ A)
    (x y : Fin n → ℝ) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hac : c - a < Real.pi)
    (ha : (fun i => Real.cos a * x i + Real.sin a * y i) ∈ A)
    (hc : (fun i => Real.cos c * x i + Real.sin c * y i) ∈ A) :
    (fun i => Real.cos b * x i + Real.sin b * y i) ∈ A := by
  have hs : 0 < Real.sin (c-a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) hac
  have h₁ : 0 ≤ Real.sin (c-b) / Real.sin (c-a) :=
    div_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))) hs.le
  have h₂ : 0 ≤ Real.sin (b-a) / Real.sin (c-a) :=
    div_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))) hs.le
  have hadd {u v : Fin n → ℝ} (hu : u ∈ A) (hv : v ∈ A) : u + v ∈ A := by
    have hh := hconvex hu hv (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2+1/2=1 by norm_num)
    have ht := hcone _ hh 2 (by norm_num)
    convert ht using 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ht := hadd (hcone _ ha _ h₁) (hcone _ hc _ h₂)
  convert ht using 1
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hs]
  rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
  ring

/-- Cone membership along equally spaced angles is order convex up to N.
**Proof sketch.** the final sample is strictly before π; intermediate samples lie on
short arcs, and hence are nonnegative combinations of their endpoints. -/
private lemma cone_samples_between {n N : ℕ} {A : Set (Fin n → ℝ)}
    (hconvex : Convex ℝ A)
    (hcone : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → t • x ∈ A)
    (x y : Fin n → ℝ) (i j k : ℕ) (hk : k ≤ N) (hij : i ≤ j) (hjk : j ≤ k)
    (hi : (fun l => Real.cos ((i:ℝ) * (Real.pi / (N+1))) * x l +
      Real.sin ((i:ℝ) * (Real.pi / (N+1))) * y l) ∈ A)
    (hkmem : (fun l => Real.cos ((k:ℝ) * (Real.pi / (N+1))) * x l +
      Real.sin ((k:ℝ) * (Real.pi / (N+1))) * y l) ∈ A) :
    (fun l => Real.cos ((j:ℝ) * (Real.pi / (N+1))) * x l +
      Real.sin ((j:ℝ) * (Real.pi / (N+1))) * y l) ∈ A := by
  obtain rfl | hij := hij.eq_or_lt
  · exact hi
  obtain rfl | hjk := hjk.eq_or_lt
  · exact hkmem
  have hd : (0:ℝ) < N+1 := by positivity
  have hscale : (0:ℝ) < Real.pi / (N+1) := div_pos Real.pi_pos hd
  have hij' : (i:ℝ) < j := by exact_mod_cast hij
  have hjk' : (j:ℝ) < k := by exact_mod_cast hjk
  have hk' : (k:ℝ) ≤ N := by exact_mod_cast hk
  have hi' : (0:ℝ) ≤ i := by positivity
  apply cone_arc_mem hconvex hcone x y
    (mul_lt_mul_of_pos_right hij' hscale)
    (mul_lt_mul_of_pos_right hjk' hscale) _ hi hkmem
  calc
    (k:ℝ)*(Real.pi/(N+1)) - (i:ℝ)*(Real.pi/(N+1)) =
        ((k:ℝ)-i)*Real.pi/(N+1) := by ring
    _ < (N+1)*Real.pi/(N+1) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by linarith) Real.pi_pos) hd
    _ = Real.pi := by field_simp

/-- A convex cone has at most two expected changes over `N` equal rotation steps
strictly before a half turn. [OD14, Example 11.50; KOS08]

**Proof sketch.** Cone membership is order convex on this short arc. Thus each
sample path changes membership at most twice. Integrate the count and use rotation
invariance to identify every step probability with the same sensitivity. -/
private lemma cone_sampling_le {n : ℕ} (A : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hconvex : Convex ℝ A)
    (hcone : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → t • x ∈ A) (N : ℕ) :
    (N:ℝ) * rotationSensitivity A (Real.pi / (N+1)) ≤ 2 := by
  classical
  apply rotationSensitivity_mul_nat_le_of_crossings A hA N _ 2
  intro x y
  apply count_changes
  intro i j k hk hij hjk hi hkA
  exact cone_samples_between hconvex hcone x y i j k hk hij hjk hi hkA

/-- The Gaussian rotation normalization is at most `5π/11`.
This coarse bound follows from `π > 3` by squaring both nonnegative sides. -/
private lemma cone_normalization_le : Real.sqrt (Real.pi/2) ≤ 5*Real.pi/11 := by
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ Real.pi/2 by positivity)
  have hs0 := Real.sqrt_nonneg (Real.pi/2)
  have hp := Real.pi_gt_three
  nlinarith [sq_nonneg (Real.sqrt (Real.pi/2) - 5*Real.pi/11)]

/-- A uniform two-crossing bound along increasingly fine semicircle samples
bounds Gaussian surface area by one. **Proof sketch.** follow the rotation quotient along
these positive angles tending to zero. For counts at least ten, the crossing
bound gives `(N+1)` times the sensitivity at most `11/5`. Combining this
with the normalization estimate `sqrt(π/2) ≤ 5π/11` bounds the rotation
quotient by one. Pass to the surface-area rotation limit. -/
private lemma cone_limit_bound {n : ℕ} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)
    (h : ∀ N : ℕ, (N:ℝ) * rotationSensitivity A (Real.pi / ((N:ℝ)+1)) ≤ 2) :
    gaussianSurfaceArea A ≤ 1 := by
  have hzero : Tendsto (fun N : ℕ => Real.pi / ((N:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Real.pi
  have hpos : Tendsto (fun N : ℕ => Real.pi / ((N:ℝ)+1)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall (fun N => by
      change 0 < Real.pi / ((N:ℝ)+1)
      positivity)⟩
  apply le_of_tendsto ((surfaceArea_rotation_limit hA).comp hpos)
  filter_upwards [eventually_ge_atTop 10] with N hN
  have hN' : (10:ℝ) ≤ N := by exact_mod_cast hN
  have hd : (0:ℝ) < N+1 := by positivity
  have hr : 0 ≤ rotationSensitivity A (Real.pi / ((N:ℝ)+1)) := by
    rw [rotationSensitivity_eq]
    positivity
  have hc := h N
  -- For N ≥ 10, sensitivity is at most 1/5, so the extra endpoint
  -- contributes at most 1/5 beyond the two-crossing bound.
  have hsmall : rotationSensitivity A (Real.pi / ((N:ℝ)+1)) ≤ 1/5 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ N-10 by linarith) hr]
  have htotal : ((N:ℝ)+1) * rotationSensitivity A (Real.pi / ((N:ℝ)+1)) ≤ 11/5 := by
    nlinarith
  -- The factors 11/5 and 5π/11 cancel, bounding the quotient by one.
  have hs := cone_normalization_le
  apply (ENNReal.ofReal_le_one).2
  rw [div_le_iff₀ (div_pos Real.pi_pos hd)]
  rw [one_mul]
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 5*Real.pi/11 - Real.sqrt (Real.pi/2) by linarith)
    (mul_nonneg (show (0:ℝ) ≤ N+1 by positivity) hr),
    mul_nonneg (show (0:ℝ) ≤ 11/5 - ((N:ℝ)+1)*rotationSensitivity A (Real.pi/((N:ℝ)+1)) by linarith)
      Real.pi_pos.le]

/-- Every measurable convex cone with apex at the origin has Gaussian surface
area at most one. [OD14, Example 11.50; KOS08]

**Proof sketch.** Convexity and conic scaling make membership order convex along
any Gaussian rotation arc shorter than a half turn. The sampled membership has at
most two transitions. Rotation invariance bounds the sensitivity at each step;
taking the surface-area rotation limit proves the claim. -/
theorem surfaceArea_convex_cone_bound {n : ℕ} (A : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hconvex : Convex ℝ A)
    (hcone : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → t • x ∈ A) :
    gaussianSurfaceArea A ≤ 1 := (by
  exact cone_limit_bound hA (cone_sampling_le A hA hconvex hcone)
)

end BooleanAnalysis.GaussianSpace
