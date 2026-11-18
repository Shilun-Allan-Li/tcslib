/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Integration
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Const
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
/-!
# Compact-test Gaussian integration by parts

## Main definitions

The Gaussian product measure and coordinate derivatives are reused.

## Main results

* `integral_mul_gaussian_coordinate_adjoint`: transfer a coordinate derivative
  from a compactly supported test function.
* `integral_mul_gaussian_coordinate_generator`: transfer a coordinate
  drift-minus-second-derivative expression.
* `integral_mul_gaussian_differential`: transfer the Gaussian
  drift-minus-Laplacian across a compact-test integral.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian integration by parts and
  Proposition 11.28.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Gaussian integration by parts transfers a coordinate derivative off a
compactly supported C¹ test function. [OD14, §11.1, Gaussian integration by parts]
**Proof sketch.** Apply coordinate Gaussian integration by parts to the product;
compact support supplies integrability of every term, and rearrange. -/
lemma integral_mul_gaussian_coordinate_adjoint
    {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (i : Fin n) :
    (∫ x, u x * (x i * v x - fderiv ℝ v x (Pi.single i 1)) ∂γ) =
      ∫ x, fderiv ℝ u x (Pi.single i 1) * v x ∂γ := by
  have hduc : Continuous (fun x => fderiv ℝ u x (Pi.single i 1)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdvc : Continuous (fun x => fderiv ℝ v x (Pi.single i 1)) :=
    (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hiv : Integrable (fun x => u x * v x) γ :=
    (hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hidu : Integrable (fun x => fderiv ℝ u x (Pi.single i 1) * v x) γ :=
    (hduc.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hidv : Integrable (fun x => u x * fderiv ℝ v x (Pi.single i 1)) γ :=
    (hu.continuous.mul hdvc).integrable_of_hasCompactSupport
      (hvc.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have hix : Integrable (fun x => x i * (u x * v x)) γ :=
    ((continuous_apply i).mul (hu.continuous.mul hv.continuous)).integrable_of_hasCompactSupport
      hvc.mul_left.mul_left
  have h := integral_coordinate_derivative_gaussianPi i (fun x => u x * v x)
    (fun x => fderiv ℝ u x (Pi.single i 1) * v x +
      u x * fderiv ℝ v x (Pi.single i 1)) (fun x => by
        have hup : HasDerivAt (fun t : ℝ => Function.update x i t)
            (Pi.single i (1 : ℝ)) (x i) := hasDerivAt_update x i (x i)
        have hud : HasDerivAt (fun t : ℝ => u (Function.update x i t))
            (fderiv ℝ u x (Pi.single i 1)) (x i) := by
          simpa only [Function.update_eq_self] using
            ((hu.differentiable le_rfl (Function.update x i (x i))).hasFDerivAt.comp_hasDerivAt
              (x i) hup)
        have hvd : HasDerivAt (fun t : ℝ => v (Function.update x i t))
            (fderiv ℝ v x (Pi.single i 1)) (x i) := by
          simpa only [Function.update_eq_self] using
            ((hv.differentiable le_rfl (Function.update x i (x i))).hasFDerivAt.comp_hasDerivAt
              (x i) hup)
        simpa only [Function.update_eq_self] using hud.mul hvd)
      hiv (hidu.add hidv) hix
  rw [integral_add hidu hidv] at h
  calc
    _ = (∫ x, x i * (u x * v x) ∂γ) -
        ∫ x, u x * fderiv ℝ v x (Pi.single i 1) ∂γ := by
      rw [← integral_sub hix hidv]
      congr 1
      funext x
      ring
    _ = _ := by linarith

/-- The Gaussian coordinate generator transfers across an integral against a
compactly supported C² test function. [OD14, §11.1, Gaussian integration by parts]
**Proof sketch.** Apply first-order Gaussian integration by parts twice; the
intermediate integral is the product of the coordinate derivatives. -/
lemma integral_mul_gaussian_coordinate_generator
    {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (i : Fin n) :
    (∫ x, u x * (x i * fderiv ℝ v x (Pi.single i 1) -
      fderiv ℝ (fun y => fderiv ℝ v y (Pi.single i 1)) x (Pi.single i 1)) ∂γ) =
    ∫ x, (x i * fderiv ℝ u x (Pi.single i 1) -
      fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single i 1)) * v x ∂γ := by
  let du := fun x => fderiv ℝ u x (Pi.single i 1)
  let dv := fun x => fderiv ℝ v x (Pi.single i 1)
  have hdu : ContDiff ℝ 1 du :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdv : ContDiff ℝ 1 dv :=
    (hv.fderiv_right (by norm_num)).clm_apply contDiff_const
  have h1 := integral_mul_gaussian_coordinate_adjoint
    (hu.of_le (by norm_num) : ContDiff ℝ 1 u) hdv
    (hvc.fderiv_apply ℝ (Pi.single i 1)) i
  have h2 := integral_mul_gaussian_coordinate_adjoint hdu
    (hv.of_le (by norm_num) : ContDiff ℝ 1 v) hvc i
  have hA : Integrable (fun x => x i * du x * v x) γ :=
    (((continuous_apply i).mul hdu.continuous).mul hv.continuous).integrable_of_hasCompactSupport
      hvc.mul_left
  have hB : Integrable (fun x => du x * dv x) γ :=
    (hdu.continuous.mul hdv.continuous).integrable_of_hasCompactSupport
      (hvc.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have hddu : Continuous (fun x => fderiv ℝ du x (Pi.single i 1)) :=
    (hdu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hC : Integrable (fun x => fderiv ℝ du x (Pi.single i 1) * v x) γ :=
    (hddu.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have h2' : (∫ x, x i * du x * v x ∂γ) - (∫ x, du x * dv x ∂γ) =
      ∫ x, fderiv ℝ du x (Pi.single i 1) * v x ∂γ := by
    rw [← integral_sub hA hB]
    convert h2 using 1
    congr 1
    funext x
    ring
  calc
    _ = ∫ x, du x * dv x ∂γ := h1
    _ = (∫ x, x i * du x * v x ∂γ) -
        ∫ x, fderiv ℝ du x (Pi.single i 1) * v x ∂γ := by linarith
    _ = _ := by
      rw [← integral_sub hA hC]
      congr 1
      funext x
      ring

/-- The Gaussian drift-minus-Laplacian transfers across an integral against a
compactly supported C² test function. [OD14, §11.1, Gaussian integration by parts]
**Proof sketch.** Expand the drift in the coordinate basis and sum the
coordinate integration-by-parts identities. All products are compactly supported. -/
lemma integral_mul_gaussian_differential
    {u v : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (∫ x, u x * (fderiv ℝ v x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ v y (Pi.single i 1)) x (Pi.single i 1)) ∂γ) =
    ∫ x, (fderiv ℝ u x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1)) x (Pi.single i 1)) * v x ∂γ := (by
    let A (w : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) :=
      x i * fderiv ℝ w x (Pi.single i 1) -
        fderiv ℝ (fun y => fderiv ℝ w y (Pi.single i 1)) x (Pi.single i 1)
    have hAc {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ 2 w) (i : Fin n) :
        Continuous (A w i) := by
      have hwd : ContDiff ℝ 1 (fun x => fderiv ℝ w x (Pi.single i 1)) :=
        (hw.fderiv_right (by norm_num)).clm_apply contDiff_const
      exact ((continuous_apply i).mul hwd.continuous).sub
        ((hwd.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have hAsc (i : Fin n) : HasCompactSupport (A v i) := by
      have hd := hvc.fderiv_apply ℝ (Pi.single i 1)
      exact (show HasCompactSupport (fun x => x i * fderiv ℝ v x (Pi.single i 1)) from
        hd.mul_left).sub (hd.fderiv_apply ℝ (Pi.single i 1))
    have hleft (i : Fin n) : Integrable (fun x => u x * A v i x) γ :=
      (hu.continuous.mul (hAc hv i)).integrable_of_hasCompactSupport (hAsc i).mul_left
    have hright (i : Fin n) : Integrable (fun x => A u i x * v x) γ :=
      ((hAc hu i).mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
    have hexpand (L : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
        L x = ∑ i, x i * L (Pi.single i 1) := by
      calc
        L x = L (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) := by
          congr 1
          ext j
          simp [Pi.single_apply]
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    have hAexpand (w : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
        fderiv ℝ w x x -
          ∑ i, fderiv ℝ (fun y => fderiv ℝ w y (Pi.single i 1)) x (Pi.single i 1) =
        ∑ i, A w i x := by
      change fderiv ℝ w x x -
        ∑ i, fderiv ℝ (fun y => fderiv ℝ w y (Pi.single i 1)) x (Pi.single i 1) =
        ∑ i, (x i * fderiv ℝ w x (Pi.single i 1) -
          fderiv ℝ (fun y => fderiv ℝ w y (Pi.single i 1)) x (Pi.single i 1))
      rw [hexpand (fderiv ℝ w x) x, Finset.sum_sub_distrib]
    simp_rw [hAexpand, Finset.mul_sum, Finset.sum_mul]
    rw [integral_finset_sum Finset.univ (fun i _ => hleft i),
      integral_finset_sum Finset.univ (fun i _ => hright i)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_mul_gaussian_coordinate_generator hu hv hvc i
)

end BooleanAnalysis.GaussianSpace
