/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Kernel
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Density
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Continuity of Gaussian endpoint pullbacks

## Main definitions

The existing Gaussian rotations and Lp pullback operation are reused.

## Main results

* `tendsto_eLpNorm_gaussianEndpoint_at`: L1 continuity at every rotation parameter.
* `tendsto_eLpNorm_gaussianEndpoint`: the specialization at correlation one.
* `gaussianNoise_tendsto_zero_L1`: noise converges to the Gaussian mean at zero correlation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Proposition 11.17.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Pulling a Gaussian integrable function back through the rotated endpoint
is continuous in L1 at every parameter.
[OD14, Prop. 11.17, arbitrary-center extension of its rotation argument]

**Proof sketch.** The endpoints form a continuous family of continuous
measure-preserving maps. Mathlib's continuity theorem for Lp pullbacks applies
to the fixed L1 class; translate its metric convergence into the L1 seminorm. -/
lemma tendsto_eLpNorm_gaussianEndpoint_at
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) (c : ℝ) :
    Tendsto (fun ρ : ℝ => eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (fun i => Real.cos (Real.arccos ρ) * z.1 i +
        Real.sin (Real.arccos ρ) * z.2 i) -
      f (fun i => Real.cos (Real.arccos c) * z.1 i +
        Real.sin (Real.arccos c) * z.2 i)) 1 ((γ).prod γ)) (𝓝 c) (𝓝 0) := by
  let g := fun ρ : ℝ => (⟨fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    fun i => Real.cos (Real.arccos ρ) * z.1 i + Real.sin (Real.arccos ρ) * z.2 i,
      by fun_prop⟩ : C((Fin n → ℝ) × (Fin n → ℝ), Fin n → ℝ))
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      fun i => Real.cos (Real.arccos p.1) * p.2.1 i +
        Real.sin (Real.arccos p.1) * p.2.2 i)
    fun_prop
  have hm (ρ : ℝ) : MeasurePreserving (g ρ) ((γ).prod γ) γ :=
    measurePreserving_fst.comp (measurePreserving_gaussianRotation (Real.arccos ρ))
  have hf1 : MemLp f 1 γ := memLp_one_iff_integrable.mpr hf
  let F := fun ρ => Lp.compMeasurePreserving (g ρ) (hm ρ) (hf1.toLp f)
  have hF : Continuous F :=
    continuous_const.compMeasurePreservingLp hg hm ENNReal.one_ne_top
  have hlim : Tendsto (fun ρ => edist (F ρ) (F c)) (𝓝 c) (𝓝 0) := by
    simpa only [edist_self] using
      (hF.edist (continuous_const : Continuous (fun _ : ℝ => F c))).tendsto c
  simpa [F, g, Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp] using hlim

/-- Pulling a Gaussian integrable function back through the rotated endpoint
converges in L1 to its pullback through the first projection.
[OD14, Prop. 11.17] -/
lemma tendsto_eLpNorm_gaussianEndpoint {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Tendsto (fun ρ : ℝ => eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (fun i => Real.cos (Real.arccos ρ) * z.1 i +
        Real.sin (Real.arccos ρ) * z.2 i) - f z.1) 1 ((γ).prod γ)) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_eLpNorm_gaussianEndpoint_at hf 1

/-- The L1 error of Gaussian averaging is bounded by the joint L1 change of
the underlying Gaussian endpoint. [OD14, Prop. 11.17]

**Proof sketch.** Subtract the original value inside the conditional integral,
then use contraction of averaging over the second probability coordinate. -/
lemma eLpNorm_gaussianNoise_sub_le {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    eLpNorm (fun x => gaussianNoise ρ f x - f x) 1 γ ≤
      eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i) - f z.1)
        1 ((γ).prod γ) := by
  have heq : (fun x : Fin n → ℝ => ∫ y,
      (f (fun i => ρ * x i + Real.sqrt (1 - ρ ^ 2) * y i) - f x) ∂γ) =
      fun x => gaussianNoise ρ f x - f x := by
    funext x
    rw [integral_sub (integrable_gaussianNoise_integrand hρ hf x) (integrable_const _)]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, gaussianNoise]
  have hdiff : AEStronglyMeasurable
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i) - f z.1)
      ((γ).prod γ) :=
    ((measurePreserving_gaussianEndpoint hρ).integrable_comp_of_integrable hf).aestronglyMeasurable.sub
      hf.aestronglyMeasurable.comp_fst
  have havg := eLpNorm_integral_prod_le (μ := γ) (ν := γ) 1 le_rfl hdiff
  exact (congrArg (fun h : (Fin n → ℝ) → ℝ => eLpNorm h 1 γ) heq.symm).le.trans havg

/-- The L1 error from the Gaussian mean is bounded by the joint L1 change
from the independent second endpoint. [OD14, §11.1, conditional-averaging argument]

**Proof sketch.** Subtract the mean inside the conditional integral. Averaging
over the second probability coordinate contracts L1, giving the stated bound. -/
lemma eLpNorm_gaussianNoise_sub_mean_le {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    eLpNorm (fun x => gaussianNoise ρ f x - ∫ y, f y ∂γ) 1 γ ≤
      eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i) - f z.2)
        1 ((γ).prod γ) := by
  have heq : (fun x : Fin n → ℝ => ∫ y,
      (f (fun i => ρ * x i + Real.sqrt (1 - ρ ^ 2) * y i) - f y) ∂γ) =
      fun x => gaussianNoise ρ f x - ∫ y, f y ∂γ := by
    funext x
    rw [integral_sub (integrable_gaussianNoise_integrand hρ hf x) hf]
    rfl
  have hdiff : AEStronglyMeasurable
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i) - f z.2)
      ((γ).prod γ) :=
    ((measurePreserving_gaussianEndpoint hρ).integrable_comp_of_integrable hf).aestronglyMeasurable.sub
      hf.aestronglyMeasurable.comp_snd
  have havg := eLpNorm_integral_prod_le (μ := γ) (ν := γ) 1 le_rfl hdiff
  exact (congrArg (fun h : (Fin n → ℝ) → ℝ => eLpNorm h 1 γ) heq.symm).le.trans havg

/-- Gaussian noise converges to the Gaussian mean in L1 as its correlation
tends to zero. [OD14, §11.1, mixing of the Ornstein–Uhlenbeck semigroup]

**Proof sketch.** Endpoint pullbacks are continuous in L1, and at zero
correlation the endpoint is the independent second coordinate. Conditional
averaging bounds the noise error by this vanishing joint endpoint error. -/
theorem gaussianNoise_tendsto_zero_L1 {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Tendsto (fun ρ : ℝ => eLpNorm (fun x => gaussianNoise ρ f x - ∫ y, f y ∂γ) 1 γ)
      (𝓝 0) (𝓝 0) := by
  have hvalid : ∀ᶠ ρ : ℝ in 𝓝 0, ρ ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0),
      eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with ρ hl hr
    exact ⟨hl.le, hr.le⟩
  have hbound : ∀ᶠ ρ : ℝ in 𝓝 0,
      eLpNorm (fun x => gaussianNoise ρ f x - ∫ y, f y ∂γ) 1 γ ≤
        eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (fun i => Real.cos (Real.arccos ρ) * z.1 i +
            Real.sin (Real.arccos ρ) * z.2 i) - f z.2) 1 ((γ).prod γ) := by
    filter_upwards [hvalid] with ρ hv
    simpa only [Real.cos_arccos hv.1 hv.2, Real.sin_arccos] using
      eLpNorm_gaussianNoise_sub_mean_le hv hf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using tendsto_eLpNorm_gaussianEndpoint_at hf 0)
    (Eventually.of_forall fun _ => zero_le _) hbound

/-- In the usual positive-time parametrization, Gaussian noise converges in
L1 to the Gaussian mean as time tends to infinity.
[OD14, §11.1, mixing of the Ornstein–Uhlenbeck semigroup] -/
theorem gaussianNoise_exp_neg_tendsto_mean_L1
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Tendsto (fun t : ℝ => eLpNorm
      (fun x => gaussianNoise (Real.exp (-t)) f x - ∫ y, f y ∂γ) 1 γ)
      atTop (𝓝 0) :=
  (gaussianNoise_tendsto_zero_L1 hf).comp
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)

end BooleanAnalysis.GaussianSpace
