/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.ContinuousBounds
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.TorusApproximation
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.FatouBound

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian pairing bounds in Lp

## Main definitions

Gaussian measures, the correlated coupling and continuous torus approximants are reused.

## Main results

* `tendsto_toReal_eLpNorm_of_sub`: Lp convergence implies convergence of real norms.
* `gaussian_two_function_positiveOffsets`: the Gaussian absolute-product estimate
  with positive exponent offsets, including joint integrability.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian Hypercontractivity.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}

local notation "γ" => Measure.pi (fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))

local instance (ρ : ℝ) : IsFiniteMeasure (correlatedGaussianMeasure (n := n) ρ) := by
  unfold correlatedGaussianMeasure
  infer_instance

/-- Lp convergence of functions implies convergence of their finite real norms.

**Proof sketch.** Pass to Lp equivalence classes and use continuity of the norm. -/
lemma tendsto_toReal_eLpNorm_of_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)] {F : ℕ → X → ℝ} {f : X → ℝ}
    (hF : ∀ m, MemLp (F m) p μ) (hf : MemLp f p μ)
    (hlim : Tendsto (fun m => eLpNorm (F m - f) p μ) atTop (𝓝 0)) :
    Tendsto (fun m => (eLpNorm (F m) p μ).toReal) atTop (𝓝 (eLpNorm f p μ).toReal) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).mpr hlim
  simpa only [Lp.norm_toLp] using hLp.norm

/-- The positive-offset Gaussian pairing estimate extends from continuous torus
pullbacks to all functions in the prescribed finite Lp spaces.
[OD14, §11.1, Gaussian Hypercontractivity]

**Proof sketch.** Choose continuous approximants converging in each Lp space
and almost everywhere. The marginal laws transfer both pointwise limits to the
coupling. Fatou's lemma bounds the absolute-product integral by the limit of the
continuous estimates, while continuity of Lp norms identifies that limit. -/
lemma gaussian_two_function_positiveOffsets (r s ρ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r * s ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ r * s)
    (hfst : MeasurePreserving Prod.fst (correlatedGaussianMeasure ρ) γ)
    (hsnd : MeasurePreserving Prod.snd (correlatedGaussianMeasure ρ) γ)
    {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal (1 + r)) γ)
    (hg : MemLp g (ENNReal.ofReal (1 + s)) γ) :
    Integrable (fun z => f z.1 * g z.2) (correlatedGaussianMeasure ρ) ∧
      (∫ z : (Fin n → ℝ) × (Fin n → ℝ), |f z.1| * |g z.2|
        ∂correlatedGaussianMeasure ρ) ≤
        (eLpNorm f (ENNReal.ofReal (1 + r)) γ).toReal *
          (eLpNorm g (ENNReal.ofReal (1 + s)) γ).toReal := by
  letI : Fact (1 ≤ ENNReal.ofReal (1 + r)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)⟩
  letI : Fact (1 ≤ ENNReal.ofReal (1 + s)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)⟩
  obtain ⟨F, hFnorm, hFae⟩ := exists_gaussianTorus_approximation γ _ ENNReal.ofReal_ne_top hf
  obtain ⟨G, hGnorm, hGae⟩ := exists_gaussianTorus_approximation γ _ ENNReal.ofReal_ne_top hg
  have hFm (m : ℕ) : MemLp (fun x => F m (gaussianTorusMap x))
      (ENNReal.ofReal (1 + r)) γ :=
    memLp_gaussianTorusPullback γ _ (F m)
  have hGm (m : ℕ) : MemLp (fun x => G m (gaussianTorusMap x))
      (ENNReal.ofReal (1 + s)) γ :=
    memLp_gaussianTorusPullback γ _ (G m)
  let P (m : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :=
    |F m (gaussianTorusMap z.1)| * |G m (gaussianTorusMap z.2)|
  have hP (m : ℕ) : Integrable (P m) (correlatedGaussianMeasure ρ) := by
    apply (MemLp.of_bound
      (by fun_prop : Continuous (P m)).aestronglyMeasurable (‖F m‖ * ‖G m‖) _ :
        MemLp (P m) 1 (correlatedGaussianMeasure ρ)).integrable le_rfl
    filter_upwards [] with z
    simpa only [P, Real.norm_eq_abs, abs_mul, abs_abs] using
      mul_le_mul ((F m).norm_coe_le_norm (gaussianTorusMap z.1))
        ((G m).norm_coe_le_norm (gaussianTorusMap z.2))
        (norm_nonneg _) (norm_nonneg _)
  have hPa : ∀ᵐ z ∂correlatedGaussianMeasure ρ,
      Tendsto (fun m => P m z) atTop (𝓝 (|f z.1| * |g z.2|)) := by
    filter_upwards [hfst.quasiMeasurePreserving.ae hFae,
      hsnd.quasiMeasurePreserving.ae hGae] with z hzF hzG
    exact hzF.abs.mul hzG.abs
  have hbound (m : ℕ) : (∫ z, P m z ∂correlatedGaussianMeasure ρ) ≤
      (eLpNorm (fun x => F m (gaussianTorusMap x)) (ENNReal.ofReal (1 + r)) γ).toReal *
        (eLpNorm (fun x => G m (gaussianTorusMap x)) (ENNReal.ofReal (1 + s)) γ).toReal := by
    rw [toReal_eLpNorm_ofReal_eq_integral _ (by linarith) (hFm m),
      toReal_eLpNorm_ofReal_eq_integral _ (by linarith) (hGm m)]
    exact gaussian_two_function_continuous r s ρ hr hs hrs hρ0 hρ1 hρsq hfst hsnd (F m) (G m)
  have hprod := (hf.aestronglyMeasurable.comp_measurePreserving hfst).mul
    (hg.aestronglyMeasurable.comp_measurePreserving hsnd)
  have habsmeas : AEStronglyMeasurable (fun z => |f z.1| * |g z.2|)
      (correlatedGaussianMeasure ρ) := by
    simpa only [Function.comp_def, Pi.mul_apply, Real.norm_eq_abs, abs_mul] using hprod.norm
  obtain ⟨habs, hle⟩ := integrable_and_integral_le_of_nonneg_tendsto
    (correlatedGaussianMeasure ρ) hP
    (fun m => Filter.Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    hPa habsmeas hbound
    ((tendsto_toReal_eLpNorm_of_sub hFm hf hFnorm).mul
      (tendsto_toReal_eLpNorm_of_sub hGm hg hGnorm))
  refine ⟨habs.mono' hprod ?_, hle⟩
  filter_upwards [] with z
  simp only [Real.norm_eq_abs, abs_mul, le_refl]

end BooleanAnalysis.GaussianSpace
