/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Interpolation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# L1 continuity of the Gaussian profile functional

## Main definitions

The bivariate probability profile and correlated Gaussian law are reused.

## Main results

The profile functional is continuous under L1 approximation of its input.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- The L1 change of the two-endpoint profile is at most twice the L1 change
of its unit-interval input. [MN15, §2, endpoint approximation]

**Proof sketch.** The profile is Lipschitz in its two volumes with the sum
metric. Integrate this pointwise bound; both Gaussian marginals equal the
original Gaussian measure. -/
lemma eLpNorm_gaussianBivariateStability_sub_le {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hgrange : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    eLpNorm (fun z => gaussianBivariateStability ρ (f z.1) (f z.2) -
      gaussianBivariateStability ρ (g z.1) (g z.2)) 1 (correlatedGaussianMeasure ρ) ≤
        eLpNorm (fun x => f x - g x) 1
          (Measure.pi fun _ => standardGaussianMeasure) +
        eLpNorm (fun x => f x - g x) 1
          (Measure.pi fun _ => standardGaussianMeasure) := by
  let μ := correlatedGaussianMeasure (n := n) ρ
  have hm₁ : MeasurePreserving Prod.fst μ
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩
  have hm₂ : MeasurePreserving Prod.snd μ
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    ⟨measurable_snd, correlatedGaussianMeasure_snd hρ⟩
  have hm : Measurable (fun x => |f x - g x|) := (hf.sub hg).abs
  calc
    _ ≤ eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f z.1 - g z.1| + |f z.2 - g z.2|) 1 μ := by
      apply eLpNorm_mono_ae_real
      exact Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using abs_gaussianBivariateStability_sub_le hρ
          (hfrange z.1) (hfrange z.2) (hgrange z.1) (hgrange z.2)
    _ ≤ eLpNorm (fun z => |f z.1 - g z.1|) 1 μ +
        eLpNorm (fun z => |f z.2 - g z.2|) 1 μ :=
      eLpNorm_add_le (hm.comp measurable_fst).aestronglyMeasurable
        (hm.comp measurable_snd).aestronglyMeasurable le_rfl
    _ = _ := by
      have h₁ := eLpNorm_comp_measurePreserving (p := 1) hm.aestronglyMeasurable hm₁
      have h₂ := eLpNorm_comp_measurePreserving (p := 1) hm.aestronglyMeasurable hm₂
      simpa only [Function.comp_def, ← Real.norm_eq_abs, eLpNorm_norm] using
        congrArg₂ (· + ·) h₁ h₂

/-- L1 approximation of measurable unit-interval functions implies convergence
of their bivariate Gaussian profile integrals.
[MN15, §2, passage to nonsmooth functions]

**Proof sketch.** The profile L1 bound is twice the input L1 error. This tends
to zero, and all profile integrands are bounded and integrable. Continuity of
the integral in L1 gives the conclusion. -/
lemma tendsto_integral_gaussianBivariateStability_of_L1 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {ι : Type*} {l : Filter ι}
    {F : ι → (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hF : ∀ᶠ i in l, Measurable (F i) ∧ ∀ x, F i x ∈ Set.Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun i => eLpNorm (fun x => F i x - f x) 1
      (Measure.pi fun _ => standardGaussianMeasure)) l (𝓝 0)) :
    Tendsto (fun i => ∫ z, gaussianBivariateStability ρ (F i z.1) (F i z.2)
      ∂correlatedGaussianMeasure ρ) l
      (𝓝 (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
        ∂correlatedGaussianMeasure ρ)) := by
  haveI : IsProbabilityMeasure (correlatedGaussianMeasure (n := n) ρ) := by
    rw [correlatedGaussianMeasure_eq]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  apply tendsto_integral_of_L1' (μ := correlatedGaussianMeasure ρ)
    (F := fun i (z : (Fin n → ℝ) × (Fin n → ℝ)) =>
      gaussianBivariateStability ρ (F i z.1) (F i z.2))
    (fun z : (Fin n → ℝ) × (Fin n → ℝ) => gaussianBivariateStability ρ (f z.1) (f z.2))
    (integrable_gaussianBivariateStability_comp _ hρ
      (hf.comp measurable_fst) (hf.comp measurable_snd)
      (fun z => hfrange z.1) (fun z => hfrange z.2))
  · filter_upwards [hF] with i hi
    exact integrable_gaussianBivariateStability_comp _ hρ
      (hi.1.comp measurable_fst) (hi.1.comp measurable_snd)
      (fun z => hi.2 z.1) (fun z => hi.2 z.2)
  · have hupper : Tendsto (fun i => eLpNorm (fun x => F i x - f x) 1
        (Measure.pi fun _ => standardGaussianMeasure) +
        eLpNorm (fun x => F i x - f x) 1
        (Measure.pi fun _ => standardGaussianMeasure)) l (𝓝 0) := by
      simpa only [add_zero] using hlim.add hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => zero_le _)
    filter_upwards [hF] with i hi
    exact eLpNorm_gaussianBivariateStability_sub_le hρ hi.1 hf hi.2 hfrange

/-- A measurable function valued in the unit interval has its Gaussian mean
in the unit interval. -/
lemma gaussianMean_mem_unitInterval {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ∈
      Set.Icc (0 : ℝ) 1 := by
  have hi : Integrable f (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfrange x).1]
        exact (hfrange x).2)
  refine ⟨integral_nonneg (fun x => (hfrange x).1), ?_⟩
  calc
    _ ≤ ∫ _x : Fin n → ℝ, (1 : ℝ)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
      integral_mono hi (integrable_const _) (fun x => (hfrange x).2)
    _ = 1 := by simp

/-- Gaussian Jensen inequalities for an L1 approximating family imply the
same inequality for its measurable unit-interval limit.
[MN15, §2, approximation step]

**Proof sketch.** The profile functional converges by its L1 bound. The input
means converge by continuity of the integral in L1, and their profiles converge
by continuity on the closed probability square. Pass the approximating
inequalities to these limits. -/
lemma gaussianBivariateStability_jensen_of_L1 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {ι : Type*} {l : Filter ι} [NeBot l]
    {F : ι → (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hF : ∀ᶠ i in l, Measurable (F i) ∧ ∀ x, F i x ∈ Set.Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun i => eLpNorm (fun x => F i x - f x) 1
      (Measure.pi fun _ => standardGaussianMeasure)) l (𝓝 0))
    (hle : ∀ᶠ i in l,
      (∫ z, gaussianBivariateStability ρ (F i z.1) (F i z.2)
        ∂correlatedGaussianMeasure ρ) ≤
      gaussianBivariateStability ρ
        (∫ x, F i x ∂(Measure.pi fun _ => standardGaussianMeasure))
        (∫ x, F i x ∂(Measure.pi fun _ => standardGaussianMeasure))) :
    (∫ z, gaussianBivariateStability ρ (f z.1) (f z.2)
      ∂correlatedGaussianMeasure ρ) ≤
    gaussianBivariateStability ρ
      (∫ x, f x ∂(Measure.pi fun _ => standardGaussianMeasure))
      (∫ x, f x ∂(Measure.pi fun _ => standardGaussianMeasure)) := by
  let γ := Measure.pi fun _ : Fin n => standardGaussianMeasure
  have hi {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
      (hgrange : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) : Integrable g γ :=
    Integrable.of_bound hg.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgrange x).1]
        exact (hgrange x).2)
  have hmean : Tendsto (fun i => ∫ x, F i x ∂γ) l (𝓝 (∫ x, f x ∂γ)) := by
    apply tendsto_integral_of_L1' f (hi hf hfrange) _ hlim
    filter_upwards [hF] with i h
    exact hi h.1 h.2
  have hmem := gaussianMean_mem_unitInterval hf hfrange
  have hpair : Tendsto (fun i => (∫ x, F i x ∂γ, ∫ x, F i x ∂γ)) l
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (∫ x, f x ∂γ, ∫ x, f x ∂γ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmean.prodMk_nhds hmean, ?_⟩
    filter_upwards [hF] with i h
    exact ⟨gaussianMean_mem_unitInterval h.1 h.2,
      gaussianMean_mem_unitInterval h.1 h.2⟩
  have hright := ((continuousOn_gaussianBivariateStability hρ) _
    (show (∫ x, f x ∂γ, ∫ x, f x ∂γ) ∈
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 from ⟨hmem, hmem⟩)).tendsto.comp hpair
  exact le_of_tendsto_of_tendsto
    (tendsto_integral_gaussianBivariateStability_of_L1 hρ hf hfrange hF hlim)
    hright hle

end BooleanAnalysis.GaussianSpace
