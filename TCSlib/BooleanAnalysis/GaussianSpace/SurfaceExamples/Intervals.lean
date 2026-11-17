/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian surface area of finite interval unions

## Main definitions

No new surface-area or Gaussian-law definition is introduced.

## Main results

* `surfaceArea_coordinate_disjoint_intervals`: the Gaussian surface area of finitely
  many disjoint nondegenerate closed intervals is the sum of endpoint densities.
* `rotationSensitivity_coordinate_set_eq_scalar`: reduction of coordinate sets
  to scalar Gaussian rotation disagreement.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014; May 2021 arXiv edition, §11.4, Example 11.50 and Exercise 11.16.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

private lemma symmDiff_iUnion_subset {ι α : Type*} (A B : ι → Set α) :
    symmDiff (⋃ i, A i) (⋃ i, B i) ⊆ ⋃ i, symmDiff (A i) (B i) := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨⟨i, hi⟩, hn⟩ | ⟨⟨i, hi⟩, hn⟩
  · exact ⟨i, Or.inl ⟨hi, fun h => hn ⟨i, h⟩⟩⟩
  · exact ⟨i, Or.inr ⟨hi, fun h => hn ⟨i, h⟩⟩⟩
/-- If distinct indexed components never overlap across the two families, symmetric difference commutes with their union.

**Proof sketch.** Expand union membership and symmetric difference. A witness in one family cannot belong to a different indexed component of the other family, by cross-disjointness. -/
private lemma symmDiff_iUnion_eq {ι α : Type*} (A B : ι → Set α)
    (hc : ∀ i j, i ≠ j → Disjoint (A i) (B j)) :
    symmDiff (⋃ i, A i) (⋃ i, B i) = ⋃ i, symmDiff (A i) (B i) := by
  apply Set.Subset.antisymm (symmDiff_iUnion_subset A B)
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨i, (⟨hi, hn⟩ | ⟨hi, hn⟩)⟩
  · refine Or.inl ⟨⟨i, hi⟩, ?_⟩
    rintro ⟨j, hj⟩
    by_cases hij : i = j
    · exact hn (hij ▸ hj)
    · exact Set.disjoint_left.mp (hc i j hij) hi hj
  · refine Or.inr ⟨⟨i, hi⟩, ?_⟩
    rintro ⟨j, hj⟩
    by_cases hij : j = i
    · exact hn (hij ▸ hj)
    · exact Set.disjoint_left.mp (hc j i hij) hj hi
private lemma interval_symmDiff_eq {a b a' b' : ℝ}
    (hab : a ≤ b) (hab' : a ≤ b') (ha'b : a' ≤ b) :
    symmDiff (Set.Ioc a b) (Set.Ioc a' b') =
      symmDiff (Set.Iic a) (Set.Iic a') ∪ symmDiff (Set.Iic b) (Set.Iic b') := by
  ext x
  simp only [Set.mem_symmDiff, Set.mem_Ioc, Set.mem_Iic, Set.mem_union]
  by_cases ha : x ≤ a <;> by_cases hb : x ≤ b <;>
    by_cases ha' : x ≤ a' <;> by_cases hb' : x ≤ b' <;> simp_all <;> linarith
private lemma interval_crossings_disjoint {a b a' b' : ℝ}
    (hab : a ≤ b) (hab' : a ≤ b') (ha'b : a' ≤ b) (ha'b' : a' ≤ b') :
    Disjoint (symmDiff (Set.Iic a) (Set.Iic a')) (symmDiff (Set.Iic b) (Set.Iic b')) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [Set.mem_symmDiff, Set.mem_Iic] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hx with ⟨h₁,h₂⟩ <;>
    rcases hy with ⟨h₃,h₄⟩ <;> simp only [not_le] at * <;> linarith
private lemma measureReal_interval_symmDiff {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a ≤ b')
    (ha'b : a' ≤ b) (ha'b' : a' ≤ b') :
    μ.real (symmDiff (Set.Ioc a b) (Set.Ioc a' b')) =
      μ.real (symmDiff (Set.Iic a) (Set.Iic a')) +
      μ.real (symmDiff (Set.Iic b) (Set.Iic b')) := by
  rw [interval_symmDiff_eq hab hab' ha'b,
    measureReal_union (interval_crossings_disjoint hab hab' ha'b ha'b')
      (measurableSet_Iic.symmDiff measurableSet_Iic)]

private lemma interval_symmDiff_subset {a b a' b' : ℝ} :
    symmDiff (Set.Ioc a b) (Set.Ioc a' b') ⊆
      symmDiff (Set.Iic a) (Set.Iic a') ∪ symmDiff (Set.Iic b) (Set.Iic b') := by
  intro x
  simp only [Set.mem_symmDiff, Set.mem_Ioc, Set.mem_Iic, Set.mem_union, ← not_le]
  tauto
private lemma measureReal_interval_symmDiff_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (a b a' b' : ℝ) :
    μ.real (symmDiff (Set.Ioc a b) (Set.Ioc a' b')) ≤
      μ.real (symmDiff (Set.Iic a) (Set.Iic a')) +
      μ.real (symmDiff (Set.Iic b) (Set.Iic b')) :=
  (measureReal_mono interval_symmDiff_subset).trans (measureReal_union_le _ _)
private lemma measureReal_intervals_symmDiff_le {ι : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (a b a' b' : ι → ℝ) :
    μ.real (symmDiff (⋃ i, Set.Ioc (a i) (b i)) (⋃ i, Set.Ioc (a' i) (b' i))) ≤
      ∑ i, (μ.real (symmDiff (Set.Iic (a i)) (Set.Iic (a' i))) +
        μ.real (symmDiff (Set.Iic (b i)) (Set.Iic (b' i)))) := by
  calc
    _ ≤ μ.real (⋃ i, symmDiff (Set.Ioc (a i) (b i)) (Set.Ioc (a' i) (b' i))) :=
      measureReal_mono (symmDiff_iUnion_subset _ _)
    _ ≤ ∑ i, μ.real (symmDiff (Set.Ioc (a i) (b i)) (Set.Ioc (a' i) (b' i))) :=
      measureReal_iUnion_fintype_le _
    _ ≤ _ := Finset.sum_le_sum fun i _ => measureReal_interval_symmDiff_le _ _ _ _
/-- For finite interval families whose corresponding components overlap and whose envelopes are pairwise disjoint, the union symmetric-difference measure is the sum of endpoint crossing measures.

**Proof sketch.** Cross-disjointness identifies the union symmetric difference componentwise. Pairwise disjoint envelopes make these component crossings disjoint, so finite additivity and the two-endpoint interval formula give the result. -/
private lemma measureReal_intervals_symmDiff {ι : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (a b a' b' : ι → ℝ)
    (hab : ∀ i, a i ≤ b i) (hab' : ∀ i, a i ≤ b' i)
    (ha'b : ∀ i, a' i ≤ b i) (ha'b' : ∀ i, a' i ≤ b' i)
    (hd : Pairwise fun i j =>
      Disjoint (Set.Ioc (a i) (b i) ∪ Set.Ioc (a' i) (b' i))
        (Set.Ioc (a j) (b j) ∪ Set.Ioc (a' j) (b' j))) :
    μ.real (symmDiff (⋃ i, Set.Ioc (a i) (b i)) (⋃ i, Set.Ioc (a' i) (b' i))) =
      ∑ i, (μ.real (symmDiff (Set.Iic (a i)) (Set.Iic (a' i))) +
        μ.real (symmDiff (Set.Iic (b i)) (Set.Iic (b' i)))) := by
  rw [symmDiff_iUnion_eq _ _ (fun i j hij =>
    (hd hij).mono Set.subset_union_left Set.subset_union_right)]
  rw [measureReal_iUnion_fintype
    (fun i j hij => (hd hij).mono Set.symmDiff_subset_union Set.symmDiff_subset_union)
    (fun i => measurableSet_Ioc.symmDiff measurableSet_Ioc)]
  exact Finset.sum_congr rfl fun i _ =>
    measureReal_interval_symmDiff (hab i) (hab' i) (ha'b i) (ha'b' i)


private lemma disjoint_Icc_order {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hd : Disjoint (Set.Icc a b) (Set.Icc c d)) : b < c ∨ d < a := by
  by_contra hn
  push_neg at hn
  exact Set.disjoint_left.mp hd
    (show max a c ∈ Set.Icc a b from ⟨le_max_left _ _, max_le hab hn.1⟩)
    (show max a c ∈ Set.Icc c d from ⟨le_max_right _ _, max_le hn.2 hcd⟩)
private lemma interval_envelopes_disjoint {a b a' b' c d c' d' : ℝ}
    (hbc : b < c) (hbc' : b < c') (hb'c : b' < c) (hb'c' : b' < c') :
    Disjoint (Set.Ioc a b ∪ Set.Ioc a' b') (Set.Ioc c d ∪ Set.Ioc c' d') := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp only [Set.mem_Ioc] at hx hy <;> linarith [hx.2, hy.1]
/-- Finitely many disjoint nondegenerate closed intervals retain disjoint envelopes under endpoint perturbations tending to zero.

**Proof sketch.** Each pair of original intervals has a strict order gap. Convergence preserves the four inequalities between their original and perturbed endpoints. Intersect the finitely many eventual pairwise conditions. -/
private lemma eventually_interval_envelopes_disjoint {ι β : Type*} [Finite ι]
    {l : Filter β} (a b : ι → ℝ) (a' b' : β → ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))
    (ha : ∀ i, Filter.Tendsto (fun t => a' t i) l (nhds (a i)))
    (hb : ∀ i, Filter.Tendsto (fun t => b' t i) l (nhds (b i))) :
    ∀ᶠ t in l, Pairwise fun i j =>
      Disjoint (Set.Ioc (a i) (b i) ∪ Set.Ioc (a' t i) (b' t i))
        (Set.Ioc (a j) (b j) ∪ Set.Ioc (a' t j) (b' t j)) := by
  have hsep (i j : ι) (hij : i ≠ j) :
      ∀ᶠ t in l, Disjoint (Set.Ioc (a i) (b i) ∪ Set.Ioc (a' t i) (b' t i))
        (Set.Ioc (a j) (b j) ∪ Set.Ioc (a' t j) (b' t j)) := by
    rcases disjoint_Icc_order (hab i).le (hab j).le (hd hij) with h | h
    · filter_upwards [Filter.Tendsto.eventually_lt tendsto_const_nhds (ha j) h,
        Filter.Tendsto.eventually_lt (hb i) tendsto_const_nhds h,
        Filter.Tendsto.eventually_lt (hb i) (ha j) h] with t h₁ h₂ h₃
      exact interval_envelopes_disjoint h h₁ h₂ h₃
    · filter_upwards [Filter.Tendsto.eventually_lt tendsto_const_nhds (ha i) h,
        Filter.Tendsto.eventually_lt (hb j) tendsto_const_nhds h,
        Filter.Tendsto.eventually_lt (hb j) (ha i) h] with t h₁ h₂ h₃
      exact (interval_envelopes_disjoint h h₁ h₂ h₃).symm
  exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
    Filter.eventually_all.mpr fun hij => hsep i j hij


/-- The symmetric difference of finitely many separated intervals and their vanishing endpoint perturbations eventually has measure equal to the sum of endpoint crossing measures.

**Proof sketch.** Eventually each original interval overlaps its own perturbation, while the envelopes of distinct components remain disjoint. The component symmetric differences therefore add, and each component splits into its two disjoint endpoint crossings. -/
private lemma eventually_measureReal_intervals_symmDiff {ι β : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] {l : Filter β}
    (a b : ι → ℝ) (a' b' : β → ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))
    (ha : ∀ i, Filter.Tendsto (fun t => a' t i) l (nhds (a i)))
    (hb : ∀ i, Filter.Tendsto (fun t => b' t i) l (nhds (b i))) :
    ∀ᶠ t in l,
      μ.real (symmDiff (⋃ i, Set.Ioc (a i) (b i)) (⋃ i, Set.Ioc (a' t i) (b' t i))) =
        ∑ i, (μ.real (symmDiff (Set.Iic (a i)) (Set.Iic (a' t i))) +
          μ.real (symmDiff (Set.Iic (b i)) (Set.Iic (b' t i)))) := by
  filter_upwards [Filter.eventually_all.mpr (fun i =>
      Filter.Tendsto.eventually_lt tendsto_const_nhds (hb i) (hab i)),
    Filter.eventually_all.mpr (fun i =>
      Filter.Tendsto.eventually_lt (ha i) tendsto_const_nhds (hab i)),
    Filter.eventually_all.mpr (fun i =>
      Filter.Tendsto.eventually_lt (ha i) (hb i) (hab i)),
    eventually_interval_envelopes_disjoint a b a' b' hab hd ha hb] with t h₁ h₂ h₃ ht
  exact measureReal_intervals_symmDiff a b (a' t) (b' t) (fun i => (hab i).le)
    (fun i => (h₁ i).le) (fun i => (h₂ i).le) (fun i => (h₃ i).le) ht


private lemma measureReal_closed_intervals_symmDiff_eq_halfopen {ι : Type*} [Finite ι]
    {μ : Measure ℝ} [NoAtoms μ] (a b a' b' : ι → ℝ) :
    μ.real (symmDiff (⋃ i, Set.Icc (a i) (b i)) (⋃ i, Set.Icc (a' i) (b' i))) =
      μ.real (symmDiff (⋃ i, Set.Ioc (a i) (b i)) (⋃ i, Set.Ioc (a' i) (b' i))) := by
  apply congrArg ENNReal.toReal
  exact (measure_congr ((Filter.EventuallyEq.iUnion fun i =>
    (Ioc_ae_eq_Icc : Set.Ioc (a i) (b i) =ᵐ[μ] Set.Icc (a i) (b i))).symmDiff
      (Filter.EventuallyEq.iUnion fun i =>
        (Ioc_ae_eq_Icc : Set.Ioc (a' i) (b' i) =ᵐ[μ] Set.Icc (a' i) (b' i))))).symm
private lemma measureReal_closed_intervals_symmDiff_le {ι : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NoAtoms μ] (a b a' b' : ι → ℝ) :
    μ.real (symmDiff (⋃ i, Set.Icc (a i) (b i)) (⋃ i, Set.Icc (a' i) (b' i))) ≤
      ∑ i, (μ.real (symmDiff (Set.Iic (a i)) (Set.Iic (a' i))) +
        μ.real (symmDiff (Set.Iic (b i)) (Set.Iic (b' i)))) := by
  rw [measureReal_closed_intervals_symmDiff_eq_halfopen]
  exact measureReal_intervals_symmDiff_le a b a' b'
/-- For an atomless finite measure, separated closed intervals and convergent endpoint perturbations eventually have symmetric-difference measure equal to the sum of their endpoint crossing measures.

**Proof sketch.** Closed and half-open intervals differ only at finitely many endpoints, which are null for an atomless measure. Transfer the eventual half-open interval decomposition through these null changes. -/
private lemma eventually_measureReal_closed_intervals_symmDiff {ι β : Type*} [Fintype ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NoAtoms μ] {l : Filter β}
    (a b : ι → ℝ) (a' b' : β → ι → ℝ)
    (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))
    (ha : ∀ i, Filter.Tendsto (fun t => a' t i) l (nhds (a i)))
    (hb : ∀ i, Filter.Tendsto (fun t => b' t i) l (nhds (b i))) :
    ∀ᶠ t in l,
      μ.real (symmDiff (⋃ i, Set.Icc (a i) (b i)) (⋃ i, Set.Icc (a' t i) (b' t i))) =
        ∑ i, (μ.real (symmDiff (Set.Iic (a i)) (Set.Iic (a' t i))) +
          μ.real (symmDiff (Set.Iic (b i)) (Set.Iic (b' t i)))) := by
  simpa only [measureReal_closed_intervals_symmDiff_eq_halfopen] using
    eventually_measureReal_intervals_symmDiff (μ := μ) a b a' b' hab hd ha hb


private lemma preimage_iUnion_Icc_affine {ι : Type*} (a b : ι → ℝ) {c d : ℝ} (hc : 0 < c) :
    (fun x : ℝ => c * x + d) ⁻¹' (⋃ i, Set.Icc (a i) (b i)) =
      ⋃ i, Set.Icc ((a i - d) / c) ((b i - d) / c) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_Icc]
  apply exists_congr
  intro i
  rw [div_le_iff₀ hc, le_div_iff₀ hc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith


open Filter
open scoped Topology
private lemma endpoint_rotation_tendsto (t y : ℝ) :
    Tendsto (fun θ : ℝ => (t - Real.sin θ * y) / Real.cos θ)
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
  have h : ContinuousAt (fun θ : ℝ => (t - Real.sin θ * y) / Real.cos θ) 0 :=
    (continuousAt_const.sub (Real.continuous_sin.continuousAt.mul_const y)).div
      Real.continuous_cos.continuousAt (by simp)
  simpa only [Real.sin_zero, zero_mul, sub_zero, Real.cos_zero, div_one] using
    h.tendsto.mono_left nhdsWithin_le_nhds
/-- A conditional Gaussian rotation crossing quotient for separated intervals eventually equals its sum of endpoint CDF quotients.

**Proof sketch.** The affine preimage has the explicitly shifted endpoints, which tend to the originals. Apply the stable separated-interval decomposition and convert each endpoint crossing measure to its CDF increment. -/
private lemma interval_rotation_slice_quotient_eventually {m : ℕ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NoAtoms μ] (C : ℝ → ℝ)
    (hC : ∀ u v, μ.real (symmDiff (Set.Iic u) (Set.Iic v)) = |C v - C u|)
    (a b : Fin m → ℝ) (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))
    (y : ℝ) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      μ.real (symmDiff (⋃ i, Set.Icc (a i) (b i))
        ((fun x : ℝ => Real.cos θ * x + Real.sin θ * y) ⁻¹'
          (⋃ i, Set.Icc (a i) (b i)))) / θ =
        ∑ i, (|C ((a i - Real.sin θ * y) / Real.cos θ) - C (a i)| / θ +
          |C ((b i - Real.sin θ * y) / Real.cos θ) - C (b i)| / θ) := by
  filter_upwards [eventually_measureReal_closed_intervals_symmDiff (μ := μ) a b
      (fun θ i => (a i - Real.sin θ * y) / Real.cos θ)
      (fun θ i => (b i - Real.sin θ * y) / Real.cos θ) hab hd
      (fun i => endpoint_rotation_tendsto (a i) y)
      (fun i => endpoint_rotation_tendsto (b i) y),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ hsmall
  have hcos : 0 < Real.cos θ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ), sq_nonneg (1 - θ),
      hsmall.1, hsmall.2]
  rw [preimage_iUnion_Icc_affine a b hcos, hθ]
  simp only [hC, Finset.sum_div, add_div]
/-- At angles between zero and one, the conditional interval crossing quotient is bounded by the sum of all endpoint CDF quotients.

**Proof sketch.** The affine preimage is a union of intervals with shifted endpoints. The symmetric difference of unions is contained in the union of component symmetric differences; each component crossing is contained in its two endpoint crossings. -/
private lemma interval_rotation_slice_quotient_bound {m : ℕ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NoAtoms μ] (C : ℝ → ℝ)
    (hC : ∀ u v, μ.real (symmDiff (Set.Iic u) (Set.Iic v)) = |C v - C u|)
    (a b : Fin m → ℝ) (θ y : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ‖μ.real (symmDiff (⋃ i, Set.Icc (a i) (b i))
        ((fun x : ℝ => Real.cos θ * x + Real.sin θ * y) ⁻¹'
          (⋃ i, Set.Icc (a i) (b i)))) / θ‖ ≤
        ∑ i, (|C ((a i - Real.sin θ * y) / Real.cos θ) - C (a i)| / θ +
          |C ((b i - Real.sin θ * y) / Real.cos θ) - C (b i)| / θ) := by
  have hcos : 0 < Real.cos θ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ), sq_nonneg (1 - θ)]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg measureReal_nonneg hθ.le),
    preimage_iUnion_Icc_affine a b hcos]
  have h := div_le_div_of_nonneg_right
    (measureReal_closed_intervals_symmDiff_le (μ := μ) a b
      (fun i => (a i - Real.sin θ * y) / Real.cos θ)
      (fun i => (b i - Real.sin θ * y) / Real.cos θ)) hθ.le
  simpa only [hC, Finset.sum_div, add_div] using h

open ThresholdFunctions

/-- Scalar rotation disagreement of a measurable set is measurable. -/
private lemma measurableSet_scalar_set_rotation_disagreement (S : Set ℝ)
    (hS : MeasurableSet S) (θ : ℝ) :
    MeasurableSet {z : ℝ × ℝ |
      ¬ (z.1 ∈ S ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)} := by
  have h₁ : MeasurableSet {z : ℝ × ℝ | z.1 ∈ S} :=
    hS.preimage measurable_fst
  have h₂ : MeasurableSet {z : ℝ × ℝ |
      Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S} :=
    hS.preimage (by fun_prop)
  convert h₁.symmDiff h₂ using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_symmDiff]
  tauto

/-- Scalar Gaussian rotation disagreement is the average conditional symmetric
difference measure.

**Proof sketch.** Apply the product measure formula conditioning on the second
coordinate. Each section is the symmetric difference of the original set and
its affine preimage. Finite Gaussian mass permits moving the real conversion
inside the integral. -/
private lemma scalar_set_rotation_disagreement_eq_integral (S : Set ℝ)
    (hS : MeasurableSet S) (θ : ℝ) :
    (((standardGaussianMeasure.prod standardGaussianMeasure)
      {z : ℝ × ℝ | ¬ (z.1 ∈ S ↔
        Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)}).toReal) =
      ∫ y, standardGaussianMeasure.real
        (symmDiff S ((fun x : ℝ => Real.cos θ * x + Real.sin θ * y) ⁻¹' S))
        ∂standardGaussianMeasure := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  let γ := standardGaussianMeasure
  let E : Set (ℝ × ℝ) := {z | ¬ (z.1 ∈ S ↔
    Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)}
  have hE : MeasurableSet E := measurableSet_scalar_set_rotation_disagreement S hS θ
  change ((γ.prod γ) E).toReal = _
  rw [Measure.prod_apply_symm hE,
    ← integral_toReal (measurable_measure_prodMk_right (μ := γ) hE).aemeasurable
      (Eventually.of_forall fun y => measure_lt_top γ _)]
  apply integral_congr_ae
  filter_upwards [] with y
  congr 2
  ext x
  simp only [Set.mem_preimage, E, Set.mem_setOf_eq, Set.mem_symmDiff]
  tauto

/-- The conditional scalar rotation disagreement quotient is almost everywhere
strongly measurable as a function of the conditioning coordinate. -/
private lemma aestronglyMeasurable_scalar_set_rotation_slice (S : Set ℝ)
    (hS : MeasurableSet S) (θ : ℝ) :
    AEStronglyMeasurable (fun y => standardGaussianMeasure.real
      (symmDiff S ((fun x : ℝ => Real.cos θ * x + Real.sin θ * y) ⁻¹' S)) / θ)
      standardGaussianMeasure := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  let E : Set (ℝ × ℝ) := {z | ¬ (z.1 ∈ S ↔
    Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)}
  have hE : MeasurableSet E := measurableSet_scalar_set_rotation_disagreement S hS θ
  have h := ((measurable_measure_prodMk_right (μ := standardGaussianMeasure) hE).ennreal_toReal.div_const θ).aestronglyMeasurable (μ := standardGaussianMeasure)
  convert h using 1
  funext y
  congr 2
  ext x
  simp only [Set.mem_preimage, E, Set.mem_setOf_eq, Set.mem_symmDiff]
  tauto

/-- Conditional crossing quotients with finitely many separated interval endpoints
converge after integration to the endpoint densities times the first absolute
Gaussian moment. The hypotheses isolate the measurable interval decomposition.

**Proof sketch.** Sum the individual endpoint limits. The uniform CDF increment
estimate bounds the conditional quotients by a finite sum of affine functions of
the absolute Gaussian coordinate. Its finite first moment permits dominated
convergence. -/
private lemma integral_finite_endpoint_quotient_tendsto {m : ℕ} (a b : Fin m → ℝ)
    (F : ℝ → ℝ → ℝ)
    (hFmeas : ∀ θ, AEStronglyMeasurable (F θ) standardGaussianMeasure)
    (hFeq : ∀ y, ∀ᶠ θ in 𝓝[>] (0 : ℝ), F θ y =
      ∑ j, (|standardGaussianCDF ((a j - Real.sin θ * y) / Real.cos θ) -
        standardGaussianCDF (a j)| / θ +
        |standardGaussianCDF ((b j - Real.sin θ * y) / Real.cos θ) -
        standardGaussianCDF (b j)| / θ))
    (hFbound : ∀ θ, 0 < θ → θ < 1 → ∀ y,
      ‖F θ y‖ ≤ ∑ j, (|standardGaussianCDF ((a j - Real.sin θ * y) / Real.cos θ) -
        standardGaussianCDF (a j)| / θ +
        |standardGaussianCDF ((b j - Real.sin θ * y) / Real.cos θ) -
        standardGaussianCDF (b j)| / θ)) :
    Tendsto (fun θ : ℝ => ∫ y, F θ y ∂standardGaussianMeasure)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) *
        ∫ y : ℝ, |y| ∂standardGaussianMeasure)) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  have hid : Integrable (fun y : ℝ => y) standardGaussianMeasure := by
    simpa only [standardGaussianMeasure_eq] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  let bound : ℝ → ℝ := fun y => ∑ j,
    (2 * standardGaussianPDF 0 * (|a j| + |y|) +
      2 * standardGaussianPDF 0 * (|b j| + |y|))
  have hbound : Integrable bound standardGaussianMeasure := by
    apply integrable_finset_sum
    intro j hj
    exact (((integrable_const |a j|).add hid.abs).const_mul _).add
      (((integrable_const |b j|).add hid.abs).const_mul _)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMeasure) bound
    (Eventually.of_forall hFmeas)
    (show ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂standardGaussianMeasure,
      ‖F θ y‖ ≤ bound y from by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact Eventually.of_forall fun y => (hFbound θ hθ.1 hθ.2 y).trans
        (Finset.sum_le_sum fun j hj => add_le_add
          (gaussianCDF_rotation_quotient_le (a j) y θ hθ.1 hθ.2)
          (gaussianCDF_rotation_quotient_le (b j) y θ hθ.1 hθ.2)))
    hbound
    (Eventually.of_forall fun y => by
      have h := tendsto_finset_sum Finset.univ fun j hj =>
        (gaussianCDF_rotation_quotient_tendsto (a j) y).add
          (gaussianCDF_rotation_quotient_tendsto (b j) y)
      simp_rw [← add_mul, ← Finset.sum_mul] at h
      apply h.congr'
      filter_upwards [hFeq y] with θ hθ
      exact hθ.symm)
  simpa only [integral_const_mul] using hlim

open ThresholdFunctions

/-- Rotation sensitivity of a set depending only on one coordinate is its scalar
Gaussian disagreement probability. [OD14, §11.1 and §11.4]

**Proof sketch.** Evaluation at the chosen coordinate preserves the standard
Gaussian law. Apply this map to both independent vectors and pull the scalar
disagreement event back through the resulting measure-preserving product map. -/
lemma rotationSensitivity_coordinate_set_eq_scalar {n : ℕ} (i : Fin n)
    (S : Set ℝ) (hS : MeasurableSet S) (θ : ℝ) :
    rotationSensitivity {x : Fin n → ℝ | x i ∈ S} θ =
      (((standardGaussianMeasure.prod standardGaussianMeasure)
        {z : ℝ × ℝ | ¬ (z.1 ∈ S ↔
          Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)}).toReal) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  let E : Set (ℝ × ℝ) := {z | ¬ (z.1 ∈ S ↔
    Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)}
  have hE : MeasurableSet E := measurableSet_scalar_set_rotation_disagreement S hS θ
  have hp := (measurePreserving_eval (fun _ : Fin n => standardGaussianMeasure) i).prod
    (measurePreserving_eval (fun _ : Fin n => standardGaussianMeasure) i)
  rw [rotationSensitivity_eq]
  change (((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
      (Measure.pi fun _ : Fin n => standardGaussianMeasure))
    {z : (Fin n → ℝ) × (Fin n → ℝ) |
      ¬ (z.1 i ∈ S ↔ Real.cos θ * z.1 i + Real.sin θ * z.2 i ∈ S)}).toReal = _
  apply congrArg ENNReal.toReal
  rw [← hp.measure_preimage hE.nullMeasurableSet]
  rfl

/-- An infinitesimal scalar rotation crossing limit evaluates the surface area
of the corresponding coordinate set. -/
private lemma surfaceArea_coordinate_set_of_quotient_tendsto {n : ℕ} (i : Fin n)
    (S : Set ℝ) (hS : MeasurableSet S) (L : ℝ)
    (hlim : Tendsto (fun θ : ℝ => Real.sqrt (Real.pi / 2) *
      (((standardGaussianMeasure.prod standardGaussianMeasure)
        {z : ℝ × ℝ | ¬ (z.1 ∈ S ↔
          Real.cos θ * z.1 + Real.sin θ * z.2 ∈ S)}).toReal) / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    gaussianSurfaceArea {x : Fin n → ℝ | x i ∈ S} = ENNReal.ofReal L := by
  apply tendsto_nhds_unique
    (surfaceArea_rotation_limit (hS.preimage (measurable_pi_apply i)))
  simpa only [← rotationSensitivity_coordinate_set_eq_scalar i S hS] using
    (ENNReal.continuous_ofReal.tendsto _).comp hlim


/-- A cylindrical set specified by finitely many disjoint nondegenerate closed
intervals in one coordinate has Gaussian surface area equal to the sum of their
endpoint densities. [OD14, Example 11.50; Exercise 11.16]
This states the interval formula in any ambient dimension, using the standard
Gaussian law of a coordinate projection.

**Proof sketch.** Condition on the second scalar Gaussian. At each fixed
conditioning value, small rotations preserve separation of the interval
components, so their crossing probabilities sum exactly over all endpoints.
Gaussian CDF differentiation gives each endpoint limit. A finite sum of affine
functions of the absolute conditioning coordinate dominates the quotients,
permitting dominated convergence. The first absolute Gaussian moment cancels
the surface-area normalization. -/
theorem surfaceArea_coordinate_disjoint_intervals {n m : ℕ} (i : Fin n)
    (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j)
    (hd : Pairwise fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))) :
    gaussianSurfaceArea {x : Fin n → ℝ | ∃ j, a j ≤ x i ∧ x i ≤ b j} =
      ENNReal.ofReal (∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) := (by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  letI : NoAtoms standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    exact ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  let S : Set ℝ := ⋃ j, Set.Icc (a j) (b j)
  have hS : MeasurableSet S := MeasurableSet.iUnion fun _ => measurableSet_Icc
  have hlim := integral_finite_endpoint_quotient_tendsto a b
    (fun θ y => standardGaussianMeasure.real
      (symmDiff S ((fun x : ℝ => Real.cos θ * x + Real.sin θ * y) ⁻¹' S)) / θ)
    (fun θ => aestronglyMeasurable_scalar_set_rotation_slice S hS θ)
    (fun y => interval_rotation_slice_quotient_eventually standardGaussianCDF
      gaussianMeasure_symmDiff_Iic a b hab hd y)
    (fun θ hθ hθ1 y => interval_rotation_slice_quotient_bound standardGaussianCDF
      gaussianMeasure_symmDiff_Iic a b θ y hθ hθ1)
  have hnorm := hlim.const_mul (Real.sqrt (Real.pi / 2))
  rw [integral_abs_standardGaussian] at hnorm
  have hn : Real.sqrt (Real.pi / 2) *
      ((∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) *
        (2 * standardGaussianPDF 0)) =
      ∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j)) := by
    calc
      _ = (∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) *
          (Real.sqrt (Real.pi / 2) * (2 * standardGaussianPDF 0)) := by ring
      _ = _ := by rw [gaussian_surface_normalization, mul_one]
  rw [hn] at hnorm
  have hscalar := surfaceArea_coordinate_set_of_quotient_tendsto i S hS
    (∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) (by
      apply hnorm.congr'
      filter_upwards [] with θ
      rw [scalar_set_rotation_disagreement_eq_integral S hS θ, integral_div]
      ring)
  simpa only [S, Set.mem_iUnion, Set.mem_Icc] using hscalar
)

end BooleanAnalysis.GaussianSpace
