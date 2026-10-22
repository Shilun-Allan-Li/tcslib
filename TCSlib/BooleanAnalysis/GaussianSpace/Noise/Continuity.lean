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
# Continuity of Gaussian noise at correlation one

## Main definitions

The existing Gaussian rotations and Lp pullback operation are reused.

## Main results

* `tendsto_eLpNorm_gaussianEndpoint`: continuous Gaussian endpoint pullbacks in L1.

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
converges in L1 to its pullback through the first projection.
[OD14, Prop. 11.17]

**Proof sketch.** The endpoints form a continuous family of continuous
measure-preserving maps. Mathlib's continuity theorem for Lp pullbacks applies
to the fixed L1 class; translate its metric convergence into the L1 seminorm. -/
lemma tendsto_eLpNorm_gaussianEndpoint {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Tendsto (fun ρ : ℝ => eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (fun i => Real.cos (Real.arccos ρ) * z.1 i +
        Real.sin (Real.arccos ρ) * z.2 i) - f z.1) 1 ((γ).prod γ)) (𝓝 1) (𝓝 0) := by
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
  have hlim : Tendsto (fun ρ => edist (F ρ) (F 1)) (𝓝 1) (𝓝 0) := by
    simpa only [edist_self] using
      (hF.edist (continuous_const : Continuous (fun _ : ℝ => F 1))).tendsto 1
  simpa [F, g, Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp] using hlim

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

end BooleanAnalysis.GaussianSpace
