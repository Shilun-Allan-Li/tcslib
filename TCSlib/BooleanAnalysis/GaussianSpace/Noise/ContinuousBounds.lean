/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.UniformTransfer
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.BooleanBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian pairing bounds for continuous compact approximants

## Main definitions

The two-frequency torus map and the existing Boolean noise coupling are reused.

## Main results

* `gaussian_two_function_continuous`: transfer the Boolean bound to continuous
  torus pullbacks, with explicit Gaussian marginal laws.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, BitsToGaussians and Gaussian Hypercontractivity.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity ThresholdFunctions

variable {n : ℕ}

local notation "γ" => Measure.pi (fun _ : Fin n => standardGaussianMeasure)

/-- For a positive finite real exponent, the real Lp norm is the corresponding
power moment raised to the reciprocal exponent. -/
lemma toReal_eLpNorm_ofReal_eq_integral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (p : ℝ) (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal =
      (∫ x, |f x| ^ p ∂μ) ^ (1 / p) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, ← one_div]
  exact ENNReal.toReal_ofReal (by positivity)

/-- Continuous torus pullbacks satisfy the Gaussian absolute-product estimate.
[OD14, §11.1, Gaussian Hypercontractivity]

**Proof sketch.** Apply the Boolean two-function inequality to absolute values of
the pullbacks on normalized blocks. Joint compact transfer gives convergence of
the product and both power moments. The marginal laws identify the limiting
moments with the corresponding Gaussian norms. -/
lemma gaussian_two_function_continuous (r s ρ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r * s ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ r * s)
    (hfst : MeasurePreserving Prod.fst (correlatedGaussianMeasure ρ) γ)
    (hsnd : MeasurePreserving Prod.snd (correlatedGaussianMeasure ρ) γ)
    (F G : C(UnitAddTorus (Fin n × Bool), ℝ)) :
    (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
      |F (gaussianTorusMap z.1)| * |G (gaussianTorusMap z.2)| ∂correlatedGaussianMeasure ρ) ≤
      (∫ x : Fin n → ℝ, |F (gaussianTorusMap x)| ^ (1 + r) ∂γ) ^ (1 / (1 + r)) *
        (∫ x : Fin n → ℝ, |G (gaussianTorusMap x)| ^ (1 + s) ∂γ) ^ (1 / (1 + s)) := by
  let H : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℝ) :=
    ⟨fun z => |F (fun j => z (.inl j))| * |G (fun j => z (.inr j))|, by fun_prop⟩
  let A : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℝ) :=
    ⟨fun z => |F (fun j => z (.inl j))| ^ (1 + r),
      (by fun_prop : Continuous (fun z : UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)) =>
        |F (fun j => z (.inl j))|)).rpow_const
        (fun _ => Or.inr (by linarith))⟩
  let B : C(UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)), ℝ) :=
    ⟨fun z => |G (fun j => z (.inr j))| ^ (1 + s),
      (by fun_prop : Continuous (fun z : UnitAddTorus ((Fin n × Bool) ⊕ (Fin n × Bool)) =>
        |G (fun j => z (.inr j))|)).rpow_const
        (fun _ => Or.inr (by linarith))⟩
  have hH := tendsto_booleanBlockExpectation_real hρ0 hρ1 H
  have hA : Tendsto (fun m : ℕ => expect (fun x : BoolCube (n * m) =>
      |F (gaussianTorusMap (normalizedCubeBlocks n m x))| ^ (1 + r))) atTop
      (𝓝 (∫ x : Fin n → ℝ, |F (gaussianTorusMap x)| ^ (1 + r) ∂γ)) := by
    have hi : (∫ z, A (gaussianPairTorusMap z) ∂correlatedGaussianMeasure ρ) =
        ∫ x : Fin n → ℝ, |F (gaussianTorusMap x)| ^ (1 + r) ∂γ := by
      change (∫ z, |F (gaussianTorusMap z.1)| ^ (1 + r) ∂correlatedGaussianMeasure ρ) = _
      rw [← hfst.map_eq]
      symm
      apply integral_map hfst.measurable.aemeasurable
      exact ((by fun_prop : Continuous (fun x => |F (gaussianTorusMap x)|)).rpow_const
        (fun _ => Or.inr (by linarith))).aestronglyMeasurable
    have ht := tendsto_booleanBlockExpectation_real hρ0 hρ1 A
    rw [hi] at ht
    simpa only [A, ContinuousMap.coe_mk, gaussianPairTorusMap, Sum.elim_inl,
      ← Finset.sum_mul, noiseKernel_sum_right hρ0 hρ1, one_mul, expect] using ht
  have hB : Tendsto (fun m : ℕ => expect (fun y : BoolCube (n * m) =>
      |G (gaussianTorusMap (normalizedCubeBlocks n m y))| ^ (1 + s))) atTop
      (𝓝 (∫ x : Fin n → ℝ, |G (gaussianTorusMap x)| ^ (1 + s) ∂γ)) := by
    have hi : (∫ z, B (gaussianPairTorusMap z) ∂correlatedGaussianMeasure ρ) =
        ∫ x : Fin n → ℝ, |G (gaussianTorusMap x)| ^ (1 + s) ∂γ := by
      change (∫ z, |G (gaussianTorusMap z.2)| ^ (1 + s) ∂correlatedGaussianMeasure ρ) = _
      rw [← hsnd.map_eq]
      symm
      apply integral_map hsnd.measurable.aemeasurable
      exact ((by fun_prop : Continuous (fun x => |G (gaussianTorusMap x)|)).rpow_const
        (fun _ => Or.inr (by linarith))).aestronglyMeasurable
    have ht := tendsto_booleanBlockExpectation_real hρ0 hρ1 B
    rw [hi] at ht
    simp only [B, ContinuousMap.coe_mk, gaussianPairTorusMap, Sum.elim_inr] at ht
    have he (m : ℕ) :
        (∑ x : BoolCube (n * m), ∑ y : BoolCube (n * m), noiseKernel ρ x y *
          |G (gaussianTorusMap (normalizedCubeBlocks n m y))| ^ (1 + s)) =
        ∑ y : BoolCube (n * m), |G (gaussianTorusMap (normalizedCubeBlocks n m y))| ^ (1 + s) := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, noiseKernel_sum_left hρ0 hρ1, one_mul]
    simpa only [he, expect] using ht
  apply le_of_tendsto_of_tendsto hH
    ((hA.rpow_const (Or.inr (by positivity))).mul
      (hB.rpow_const (Or.inr (by positivity))))
  filter_upwards [] with m
  simpa only [H, ContinuousMap.coe_mk, gaussianPairTorusMap, Sum.elim_inl, Sum.elim_inr,
    abs_abs, innerProduct_noiseOp_eq_weighted_sum, mul_assoc] using
      boolean_two_function_positiveOffsets r s ρ hr hs hrs hρ0 hρ1 hρsq
        (fun x => |F (gaussianTorusMap (normalizedCubeBlocks n m x))|)
        (fun y => |G (gaussianTorusMap (normalizedCubeBlocks n m y))|)

end BooleanAnalysis.GaussianSpace
