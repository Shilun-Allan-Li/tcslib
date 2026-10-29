/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Torus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Continuous torus approximation in finite Lp

## Main definitions

The existing two-frequency torus map and Lp pullback are reused.

## Main results

* `memLp_gaussianTorusPullback`: continuous torus pullbacks belong to every Lp
  space for a finite measure on real vectors.
* `exists_gaussianTorus_approximation`: real continuous torus functions approximate
  any finite Lp input both in its seminorm and almost everywhere.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Theorem 11.22 and Gaussian
  Hypercontractivity. The torus is an auxiliary approximation device.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

/-- A continuous real function on the compact torus has an Lp pullback for every
exponent and every finite measure on real vectors. -/
lemma memLp_gaussianTorusPullback {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) (F : C(UnitAddTorus (Fin n × Bool), ℝ)) :
    MemLp (fun x => F (gaussianTorusMap x)) p μ := by
  exact MemLp.of_bound
    (F.continuous.comp continuous_gaussianTorusMap).aestronglyMeasurable ‖F‖
    (Eventually.of_forall fun x => F.norm_coe_le_norm (gaussianTorusMap x))

/-- Every real finite-Lp function has continuous torus approximants whose
pullbacks converge in Lp and almost everywhere, for any finite measure on
real vectors.

**Proof sketch.** Lift the Lp class to the image measure on the compact torus.
Approximate it by continuous functions there and pull the approximations back
through the measure-preserving torus map. Lp convergence implies convergence
in measure, so a subsequence also converges almost everywhere. -/
lemma exists_gaussianTorus_approximation {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p μ) :
    ∃ F : ℕ → C(UnitAddTorus (Fin n × Bool), ℝ),
      Tendsto (fun m => eLpNorm (fun x => F m (gaussianTorusMap x) - f x) p μ)
        atTop (𝓝 0) ∧
      ∀ᵐ x ∂μ, Tendsto (fun m => F m (gaussianTorusMap x)) atTop (𝓝 (f x)) := by
  let ν := μ.map (gaussianTorusMap (n := n))
  let L : Lp ℝ p ν →ₗᵢ[ℝ] Lp ℝ p μ :=
    Lp.compMeasurePreservingₗᵢ ℝ gaussianTorusMap
      ⟨continuous_gaussianTorusMap.measurable, rfl⟩
  obtain ⟨g, hg⟩ := surjective_gaussianTorus_pullback (𝕜 := ℝ) μ p (hf.toLp f)
  change L g = hf.toLp f at hg
  let C : C(UnitAddTorus (Fin n × Bool), ℝ) →L[ℝ] Lp ℝ p ν :=
    ContinuousMap.toLp p ν ℝ
  have hd : DenseRange C := ContinuousMap.toLp_denseRange ℝ ν ℝ hp
  obtain ⟨u, hu, hulim⟩ := mem_closure_iff_seq_limit.mp (hd g)
  choose F hF using hu
  have hFconv : Tendsto (fun m => C (F m)) atTop (𝓝 g) := by
    simpa only [hF] using hulim
  have hLp : Tendsto (fun m => L (C (F m))) atTop (𝓝 (hf.toLp f)) := by
    rw [← hg]
    exact (L.continuous.tendsto g).comp hFconv
  have hco (m : ℕ) : (L (C (F m)) : (Fin n → ℝ) → ℝ) =ᵐ[μ]
      fun x => F m (gaussianTorusMap x) := by
    apply (Lp.coeFn_compMeasurePreserving _ _).trans
    exact ae_of_ae_map continuous_gaussianTorusMap.measurable.aemeasurable
      (ContinuousMap.coeFn_toLp ν (F m))
  have hnorm : Tendsto
      (fun m => eLpNorm (fun x => F m (gaussianTorusMap x) - f x) p μ)
      atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun m => L (C (F m))) f hf).mp hLp
    apply h.congr
    intro m
    exact eLpNorm_congr_ae ((hco m).sub Filter.EventuallyEq.rfl)
  have hm : TendstoInMeasure μ (fun m x => F m (gaussianTorusMap x)) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le Fact.out).ne'
      (fun m => ((F m).continuous.comp continuous_gaussianTorusMap).aestronglyMeasurable)
      hf.aestronglyMeasurable hnorm
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  exact ⟨fun m => F (ns m), hnorm.comp hns.tendsto_atTop, hae⟩

end BooleanAnalysis.GaussianSpace
