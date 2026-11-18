/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.TimeDifferentiation
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
/-!
# Compact tests for the strong Gaussian generator

## Main definitions

The Gaussian noise operator and its time difference quotients are reused.

## Main results

* `gaussianNoise_quotient_compact_test`: compactly supported C² functions have
  the expected pointwise generator quotient limit and a uniform linear-growth bound.
* `integral_mul_gaussian_differential_of_strong_limit`: a strong Gaussian L²
  generator limit satisfies the differential generator identity against compact tests.

Pairing convergence and bounded Mehler differentiation provide the supporting
analytic estimates. The generator assumptions are stated directly to avoid
an import cycle with the parent generator module.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.24 and Propositions 11.26–11.27.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Strong L² convergence implies convergence of pairing with a fixed L² function.
**Proof sketch.** Hölder's inequality bounds the L¹ product error by the fixed
L² norm times the vanishing L² error; continuity of integration concludes. -/
lemma tendsto_integral_mul_of_eLpNorm_sub_tendsto
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {F : ι → α → ℝ} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hF : ∀ᶠ i in l, MemLp (F i) 2 μ)
    (hlim : Tendsto (fun i => eLpNorm (fun x => F i x - g x) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f x * F i x ∂μ) l (𝓝 (∫ x, f x * g x ∂μ)) := by
  apply tendsto_integral_of_L1' (fun x => f x * g x) (hf.integrable_mul hg)
  · filter_upwards [hF] with i hi using hf.integrable_mul hi
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hf.eLpNorm_lt_top.ne))
      (Eventually.of_forall fun _ => zero_le _)
    filter_upwards [hF] with i hi
    have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (hi.sub hg).aestronglyMeasurable hf.aestronglyMeasurable
    convert h using 1
    congr 1
    ext x
    change f x * F i x - f x * g x = f x * (F i x - g x)
    ring
/-- Pointwise convergence dominated by an L² function implies convergence of
pairing with a fixed L² function.
**Proof sketch.** Cauchy–Schwarz makes the product of the fixed function's
absolute value and the L² majorant integrable; apply dominated convergence. -/
lemma tendsto_integral_mul_of_dominated_L2
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ} {f g B : α → ℝ}
    (hf : MemLp f 2 μ) (hB : MemLp B 2 μ)
    (hF : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (g x))) :
    Tendsto (fun i => ∫ x, f x * F i x ∂μ) l (𝓝 (∫ x, f x * g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ * B x)
  · exact hF.mono fun i hi => hf.aestronglyMeasurable.mul hi
  · filter_upwards [hb] with i hi
    filter_upwards [hi] with x hx
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (f x))
  · exact hf.norm.integrable_mul hB
  · exact hlim.mono fun x hx => tendsto_const_nhds.mul hx
/-- Every affine function of the Gaussian input norm belongs to Gaussian L².
[OD14, §11.1, Gaussian moments] -/
lemma memLp_gaussian_linear_growth {n : ℕ} (C M : ℝ) :
    MemLp (fun x : Fin n → ℝ => C + M * ‖x‖) 2
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  have hn : MemLp (fun x : Fin n → ℝ => ‖x‖) 2
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    (memLp_two_iff_integrable_sq continuous_norm.aestronglyMeasurable).mpr
      (integrable_gaussianPi_norm_pow 2)
  exact (memLp_const C).add (hn.const_mul M)

/-- For a bounded continuous input, Gaussian noise at a fixed starting point
depends continuously on its correlation parameter. [OD14, §11.1]
**Proof sketch.** The Mehler endpoint varies continuously, and the global input
bound permits dominated convergence under the Gaussian probability law. -/
lemma continuous_gaussianNoise_correlation_of_bounded
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) {B : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ B) (x : Fin n → ℝ) :
    Continuous (fun r : ℝ => gaussianNoise r f x) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  simp only [gaussianNoise_eq]
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun q =>
      (hf.comp (by fun_prop)).aestronglyMeasurable
  · exact ⟨B, Eventually.of_forall fun q =>
      Eventually.of_forall fun y => hb _⟩
  · exact Eventually.of_forall fun y =>
      (hf.comp (by fun_prop : Continuous (fun q : ℝ =>
        fun i => q * x i + Real.sqrt (1 - q ^ 2) * y i))).tendsto r

/-- At correlation one, Gaussian noise of a bounded C² function with bounded
first and second derivatives has left derivative equal to its positive
differential generator. [OD14, §11.1, Props. 11.26–11.27]
**Proof sketch.** The interior Mehler derivative converges to the drift minus
the Hessian trace by bounded dominated convergence. Continuity at the endpoint
extends this derivative to a derivative within the left half-line. -/
lemma hasDerivWithinAt_gaussianNoise_one_of_bounded
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun r : ℝ => gaussianNoise r f x)
      (fderiv ℝ f x x - ∑ i, fderiv ℝ (fderiv ℝ f) x
        (Pi.single i 1) (Pi.single i 1)) (Set.Iic 1) 1 := by
  let A := fun z => fderiv ℝ f z x
  let H := fun (i : Fin n) z => fderiv ℝ (fderiv ℝ f) z
    (Pi.single i 1) (Pi.single i 1)
  have hAc : Continuous A := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hAb (z) : ‖A z‖ ≤ M * ‖x‖ :=
    ((fderiv ℝ f z).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hm z) (norm_nonneg _))
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hHc (i : Fin n) : Continuous (H i) :=
    ((hdf.continuous_fderiv le_rfl).clm_apply
      continuous_const).clm_apply continuous_const
  have hHb (i : Fin n) (z) : ‖H i z‖ ≤ K := by
    apply le_trans ?_ (hk z)
    simpa only [Pi.norm_single, norm_one, mul_one] using
      (fderiv ℝ (fderiv ℝ f) z).le_opNorm₂ (Pi.single i 1) (Pi.single i 1)
  let D := fun r => gaussianNoise r A x - r * ∑ i, gaussianNoise r (H i) x
  have hDc : Continuous D :=
    (continuous_gaussianNoise_correlation_of_bounded hAc hAb x).sub
      (continuous_id.mul (continuous_finset_sum _ fun i _ =>
        continuous_gaussianNoise_correlation_of_bounded (hHc i) (hHb i) x))
  have hd (r : ℝ) (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun q => gaussianNoise q f x) (D r) r := by
    exact hasDerivAt_gaussianNoise_correlation_generator hf hb hm hk x hr
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Set.Ioo (-1 : ℝ) 1)
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (continuous_gaussianNoise_correlation_of_bounded hf.continuous
      (fun z => by simpa only [Real.norm_eq_abs] using hb z) x).continuousAt.continuousWithinAt
    (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1))
  have hlim : Tendsto D (𝓝[<] (1 : ℝ)) (𝓝 (D 1)) :=
    (hDc.tendsto 1).mono_left nhdsWithin_le_nhds
  have heq : (fun r => deriv (fun q => gaussianNoise q f x) r) =ᶠ[𝓝[<] (1 : ℝ)] D := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
    exact (hd r hr).deriv
  simpa only [D, gaussianNoise_one, one_mul, A, H] using hlim.congr' heq.symm

/-- For a bounded C² function with bounded first and second derivatives,
the positive-time Gaussian generator quotients converge pointwise to drift
minus the Hessian trace. [OD14, Prop. 11.26]
**Proof sketch.** Compose the endpoint correlation derivative with the
exponential time parametrization and rewrite its right-hand difference quotient. -/
lemma tendsto_gaussianNoise_quotient_of_bounded
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K) (x : Fin n → ℝ) :
    Tendsto (fun t : ℝ => (f x - gaussianNoise (Real.exp (-t)) f x) / t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (fderiv ℝ f x x - ∑ i, fderiv ℝ (fderiv ℝ f) x
        (Pi.single i 1) (Pi.single i 1))) := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    simpa only [Pi.neg_apply, id_eq, neg_zero, Real.exp_zero, one_mul] using
      (hasDerivAt_id (0 : ℝ)).neg.exp
  have hd := (hasDerivWithinAt_gaussianNoise_one_of_bounded hf hb hm hk x).comp_of_eq
    0 he.hasDerivWithinAt
    (show Set.MapsTo (fun t : ℝ => Real.exp (-t)) (Set.Ici 0) (Set.Iic 1) from
      fun t ht => Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) (by norm_num)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have hsets : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by ext t; simp
  rw [hsets] at hd
  have hn := hd.neg
  simpa only [Function.comp_def, slope_def_field, sub_zero, neg_zero, Real.exp_zero,
    gaussianNoise_one, mul_neg_one, neg_neg, ← neg_div, neg_sub] using hn

/-- For a bounded C² function, bounded first and second derivatives give a uniform
linear-growth bound on positive-time Gaussian generator quotients. [OD14, §11.1]
**Proof sketch.** Derivative commutation bounds the time derivative of the
noise orbit by the Hessian bound plus the gradient bound times the input norm.
Apply the mean-value estimate between zero and the requested positive time. -/
lemma norm_gaussianNoise_quotient_le_of_bounded
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(f x - gaussianNoise (Real.exp (-t)) f x) / t‖ ≤ (n : ℝ) * K + M * ‖x‖ := by
  let U := fun r : ℝ => gaussianNoise (Real.exp (-r)) f
  let D := fun r => (∑ i, fderiv ℝ (fderiv ℝ (U r)) x
    (Pi.single i 1) (Pi.single i 1)) - fderiv ℝ (U r) x x
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ f 0)).trans (hm 0)
  have hK : 0 ≤ K := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hk 0)
  have hderiv (r : ℝ) (hr : r ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt (fun q => U q x) (D r) (Set.Ici 0) r := by
    by_cases hz : r = 0
    · subst r
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
        simpa only [Pi.neg_apply, id_eq, neg_zero, Real.exp_zero, one_mul] using
          (hasDerivAt_id (0 : ℝ)).neg.exp
      have hh := (hasDerivWithinAt_gaussianNoise_one_of_bounded hf hb hm hk x).comp_of_eq
        0 he.hasDerivWithinAt
        (show Set.MapsTo (fun t : ℝ => Real.exp (-t)) (Set.Ici 0) (Set.Iic 1) from
          fun t ht => Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) (by norm_num)
      convert hh using 1
      simp only [D, U, neg_zero, Real.exp_zero, gaussianNoise_one, mul_neg_one]
      ring
    · exact (hasDerivAt_gaussianNoise_exp_neg_generator hf hb hm hk x
        (lt_of_le_of_ne hr (Ne.symm hz))).hasDerivWithinAt
  have hbound (r : ℝ) (hr : r ∈ Set.Ici (0 : ℝ)) :
      ‖D r‖ ≤ (n : ℝ) * K + M * ‖x‖ := by
    have hexp : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
    have habs : |Real.exp (-r)| ≤ 1 := by rw [abs_of_pos (Real.exp_pos _)]; exact hexp
    apply norm_gaussianGenerator_le
    · intro z
      exact (norm_fderiv_gaussianNoise_commutation_le (hf.of_le (by norm_num)) hb hm _ z).trans
        (mul_le_of_le_one_left hM habs)
    · intro z
      exact (norm_fderiv_fderiv_gaussianNoise_commutation_le hf hb hm hk _ z).trans
        (mul_le_of_le_one_left hK (by nlinarith [Real.exp_pos (-r)]))
  have hv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ici (0 : ℝ))
    (show (0 : ℝ) ∈ Set.Ici 0 by simp) (show t ∈ Set.Ici 0 from ht.le)
  rw [norm_div, show ‖t‖ = t from (Real.norm_eq_abs t).trans (abs_of_pos ht), div_le_iff₀ ht]
  simpa only [U, neg_zero, Real.exp_zero, gaussianNoise_one, sub_zero,
    Real.norm_eq_abs, abs_of_pos ht, norm_sub_rev] using hv

/-- Differentiating a Fréchet derivative evaluated on a fixed vector agrees
with evaluating its second Fréchet derivative on that vector. -/
lemma fderiv_fderiv_apply_const_of_contDiff
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : Fin n → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fderiv ℝ f) x w v := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  rw [fderiv_clm_apply (hdf.differentiable le_rfl x)
    (differentiableAt_const v)]
  simp

/-- For a compactly supported C² function, Gaussian generator quotients converge
pointwise to the positive differential generator and admit a uniform bound
of the form C + M ‖x‖ with nonnegative constants. [OD14, Prop. 11.26]
**Proof sketch.** Compact support bounds the function and its first two
derivatives. Apply the bounded-input quotient limit and linear-growth estimate,
then identify the scalar coordinate second derivatives. -/
lemma gaussianNoise_quotient_compact_test
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∀ x, Tendsto (fun t : ℝ => (f x - gaussianNoise (Real.exp (-t)) f x) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (fderiv ℝ f x x - ∑ i,
        fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)))) ∧
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ (x : Fin n → ℝ) (t : ℝ), 0 < t →
      ‖(f x - gaussianNoise (Real.exp (-t)) f x) / t‖ ≤ C + M * ‖x‖ := by
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨M, hM⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by norm_num))
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨K, hK⟩ := ((hfc.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous
    (hdf.continuous_fderiv le_rfl)
  have hb (z) : |f z| ≤ B := by simpa only [Real.norm_eq_abs] using hB z
  constructor
  · intro x
    simpa only [fderiv_fderiv_apply_const_of_contDiff hf] using
      tendsto_gaussianNoise_quotient_of_bounded hf hb hM hK x
  · refine ⟨(n : ℝ) * K, M, ?_, ?_, ?_⟩
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hK 0))
    · exact (norm_nonneg _).trans (hM 0)
    · intro x t ht
      exact norm_gaussianNoise_quotient_le_of_bounded hf hb hM hK x ht

/-- A strong Gaussian L² generator limit agrees with the differential generator
after pairing against a compactly supported C² test function.
[OD14, Prop. 11.26, weak formulation]
**Proof sketch.** Noise symmetry pairs the two finite generator quotients.
The assumed strong limit determines one pairing limit. The compact test's
pointwise quotient limit and uniform linear-growth bound determine the other
by dominated convergence and Gaussian square integrability. Uniqueness of
limits gives the identity. -/
lemma integral_mul_gaussian_differential_of_strong_limit
    {f g φ : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hlim : Tendsto (fun t : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x, φ x * g x ∂γ) = ∫ x, f x * (fderiv ℝ φ x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single i 1)) x (Pi.single i 1)) ∂γ := (by
    obtain ⟨hpt, C, M, _, _, hbound⟩ := gaussianNoise_quotient_compact_test hφ hφc
    have hφLp : MemLp φ 2 γ := hφ.continuous.memLp_of_hasCompactSupport hφc
    let q (w : (Fin n → ℝ) → ℝ) (t : ℝ) :=
      fun x => (w x - gaussianNoise (Real.exp (-t)) w x) / t
    have hρ {t : ℝ} (ht : 0 < t) : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans (by norm_num) (Real.exp_pos _).le,
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
    have hq {w : (Fin n → ℝ) → ℝ} (hw : MemLp w 2 γ) {t : ℝ} (ht : 0 < t) :
        MemLp (q w t) 2 γ := by
      convert (hw.sub (gaussianNoise_memLp (hρ ht) 2 (by norm_num) hw)).const_smul t⁻¹ using 1
      ext x
      change (w x - gaussianNoise (Real.exp (-t)) w x) / t =
        t⁻¹ * (w x - gaussianNoise (Real.exp (-t)) w x)
      ring
    have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have hleft : Tendsto (fun t => ∫ x, φ x * q f t x ∂γ)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, φ x * g x ∂γ)) :=
      tendsto_integral_mul_of_eLpNorm_sub_tendsto hφLp hg
        (htpos.mono fun t ht => hq hf ht) hlim
    have hright : Tendsto (fun t => ∫ x, f x * q φ t x ∂γ)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x * (fderiv ℝ φ x x -
          ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single i 1)) x (Pi.single i 1)) ∂γ)) := by
      apply tendsto_integral_mul_of_dominated_L2 hf (memLp_gaussian_linear_growth C M)
      · exact htpos.mono fun t ht => (hq hφLp ht).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Eventually.of_forall fun x => hbound x t ht
      · exact Eventually.of_forall fun x => hpt x
    have heq : (fun t => ∫ x, φ x * q f t x ∂γ) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => ∫ x, f x * q φ t x ∂γ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      simp only [q, ← mul_div_assoc, mul_sub]
      rw [integral_div, integral_div,
        integral_sub (show Integrable (fun x => φ x * f x) γ from hφLp.integrable_mul hf)
          (show Integrable (fun x => φ x * gaussianNoise (Real.exp (-t)) f x) γ from
            hφLp.integrable_mul (gaussianNoise_memLp (hρ ht) 2 (by norm_num) hf)),
        integral_sub (show Integrable (fun x => f x * φ x) γ from hf.integrable_mul hφLp)
          (show Integrable (fun x => f x * gaussianNoise (Real.exp (-t)) φ x) γ from
            hf.integrable_mul (gaussianNoise_memLp (hρ ht) 2 (by norm_num) hφLp)),
        gaussianNoise_selfAdjoint (hρ ht) hφLp hf]
      congr 2
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
    exact tendsto_nhds_unique hleft (hright.congr' heq.symm)
)

end BooleanAnalysis.GaussianSpace
