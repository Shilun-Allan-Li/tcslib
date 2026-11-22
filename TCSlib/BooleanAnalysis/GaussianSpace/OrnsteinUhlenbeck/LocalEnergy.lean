/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.Integration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Localized Gaussian energy estimates

## Main definitions

The Gaussian product law, coordinate derivatives, and smooth cutoffs are reused.

## Main results

* `integral_gaussian_weighted_gradient`: integration by parts with a compact cutoff.
* `gaussian_caccioppoli_cutoff`: localized gradient energy is bounded by
  the generator pairing and a controlled cutoff error.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Proposition 11.28.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Local Gaussian integration by parts with a compact C¹ cutoff.
[OD14, §11.1, Proposition 11.28, localized form]
**Proof sketch.** Apply coordinate integration by parts to the compact product
of the cutoff and the first function, with the derivative of the second function. -/
lemma integral_gaussian_weighted_coordinate
    {f g χ : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 2 g) (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) (i : Fin n) :
    (∫ x, χ x * fderiv ℝ f x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1) ∂γ) =
      (∫ x, χ x * f x * (x i * fderiv ℝ g x (Pi.single i 1) -
        fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) ∂γ) -
      ∫ x, f x * fderiv ℝ χ x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1) ∂γ := by
  let df := fun x => fderiv ℝ f x (Pi.single i 1)
  let dg := fun x => fderiv ℝ g x (Pi.single i 1)
  let dχ := fun x => fderiv ℝ χ x (Pi.single i 1)
  let ddg := fun x => fderiv ℝ dg x (Pi.single i 1)
  have hdf : Continuous df :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : ContDiff ℝ 1 dg :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdχ : Continuous dχ :=
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hddg : Continuous ddg :=
    (hdg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hA : Integrable (fun x => χ x * df x * dg x) γ :=
    ((hχ.continuous.mul hdf).mul hdg.continuous).integrable_of_hasCompactSupport
      hχc.mul_right.mul_right
  have hB : Integrable (fun x => χ x * f x * (x i * dg x - ddg x)) γ :=
    ((hχ.continuous.mul hf.continuous).mul
      (((continuous_apply i).mul hdg.continuous).sub hddg)).integrable_of_hasCompactSupport
        hχc.mul_right.mul_right
  have hC : Integrable (fun x => f x * dχ x * dg x) γ :=
    ((hf.continuous.mul hdχ).mul hdg.continuous).integrable_of_hasCompactSupport
      (hχc.fderiv_apply ℝ (Pi.single i 1)).mul_left.mul_right
  have hD : Integrable (fun x => ddg x * (χ x * f x)) γ :=
    (hddg.mul (hχ.continuous.mul hf.continuous)).integrable_of_hasCompactSupport
      hχc.mul_right.mul_left
  have hprod (x : Fin n → ℝ) :
      fderiv ℝ (fun y => χ y * f y) x (Pi.single i 1) = χ x * df x + f x * dχ x := by
    rw [fderiv_fun_mul (hχ.differentiable le_rfl x) (hf.differentiable le_rfl x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  have hh := integral_mul_gaussian_coordinate_adjoint hdg (hχ.mul hf) hχc.mul_right i
  have hsplit :
      (∫ x, dg x * (x i * (χ x * f x) -
        fderiv ℝ (fun y => χ y * f y) x (Pi.single i 1)) ∂γ) =
      (∫ x, χ x * f x * (x i * dg x - ddg x) ∂γ) -
      (∫ x, f x * dχ x * dg x ∂γ) -
      (∫ x, χ x * df x * dg x ∂γ) +
      ∫ x, ddg x * (χ x * f x) ∂γ := by
    calc
      _ = ∫ x, χ x * f x * (x i * dg x - ddg x) -
          f x * dχ x * dg x - χ x * df x * dg x + ddg x * (χ x * f x) ∂γ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hprod]
        ring
      _ = _ := by
        rw [integral_add
          (show Integrable (fun x => χ x * f x * (x i * dg x - ddg x) -
            f x * dχ x * dg x - χ x * df x * dg x) γ from (hB.sub hC).sub hA) hD,
          integral_sub
            (show Integrable (fun x => χ x * f x * (x i * dg x - ddg x) -
              f x * dχ x * dg x) γ from hB.sub hC) hA, integral_sub hB hC]
  change (∫ x, χ x * df x * dg x ∂γ) =
    (∫ x, χ x * f x * (x i * dg x - ddg x) ∂γ) - ∫ x, f x * dχ x * dg x ∂γ
  change (∫ x, dg x * (x i * (χ x * f x) -
    fderiv ℝ (fun y => χ y * f y) x (Pi.single i 1)) ∂γ) =
      ∫ x, ddg x * (χ x * f x) ∂γ at hh
  rw [hsplit] at hh
  linarith

/-- A compact C¹ cutoff localizes the Gaussian energy identity without any
growth hypotheses on the two functions. [OD14, §11.1, Proposition 11.28]
**Proof sketch.** Sum the coordinate weighted identities and expand the drift
in the standard coordinate basis. Compact support makes each summand integrable. -/
lemma integral_gaussian_weighted_gradient
    {f g χ : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 2 g) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    (∫ x, χ x * (∑ i, fderiv ℝ f x (Pi.single i 1) *
      fderiv ℝ g x (Pi.single i 1)) ∂γ) =
    (∫ x, χ x * f x * (fderiv ℝ g x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) ∂γ) -
    ∫ x, f x * (∑ i, fderiv ℝ χ x (Pi.single i 1) *
      fderiv ℝ g x (Pi.single i 1)) ∂γ := by
  let d (w : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) :=
    fderiv ℝ w x (Pi.single i 1)
  have hdf (i : Fin n) : Continuous (d f i) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg (i : Fin n) : ContDiff ℝ 1 (d g i) :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdχ (i : Fin n) : Continuous (d χ i) :=
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hddg (i : Fin n) : Continuous (fun x => fderiv ℝ (d g i) x (Pi.single i 1)) :=
    ((hdg i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hA (i : Fin n) : Integrable (fun x => χ x * (d f i x * d g i x)) γ :=
    (hχ.continuous.mul ((hdf i).mul (hdg i).continuous)).integrable_of_hasCompactSupport
      hχc.mul_right
  have hB (i : Fin n) : Integrable (fun x => χ x * f x *
      (x i * d g i x - fderiv ℝ (d g i) x (Pi.single i 1))) γ :=
    ((hχ.continuous.mul hf.continuous).mul
      (((continuous_apply i).mul (hdg i).continuous).sub (hddg i))).integrable_of_hasCompactSupport
        hχc.mul_right.mul_right
  have hC (i : Fin n) : Integrable (fun x => f x * (d χ i x * d g i x)) γ :=
    (hf.continuous.mul ((hdχ i).mul (hdg i).continuous)).integrable_of_hasCompactSupport
      (hχc.fderiv_apply ℝ (Pi.single i 1)).mul_right.mul_left
  have hraw (x : Fin n → ℝ) :
      fderiv ℝ g x x - ∑ i, fderiv ℝ (d g i) x (Pi.single i 1) =
      ∑ i, (x i * d g i x - fderiv ℝ (d g i) x (Pi.single i 1)) := by
    have hexpand : fderiv ℝ g x x = ∑ i, x i * d g i x := by
      have he (i : Fin n) : (fun j : Fin n => if i = j then (1 : ℝ) else 0) =
          Pi.single i 1 := by
        ext j
        simp [Pi.single_apply, eq_comm]
      simpa only [he, smul_eq_mul] using
        (LinearMap.pi_apply_eq_sum_univ (fderiv ℝ g x).toLinearMap x)
    rw [hexpand, Finset.sum_sub_distrib]
  change (∫ x, χ x * (∑ i, d f i x * d g i x) ∂γ) =
    (∫ x, χ x * f x * (fderiv ℝ g x x -
      ∑ i, fderiv ℝ (d g i) x (Pi.single i 1)) ∂γ) -
    ∫ x, f x * (∑ i, d χ i x * d g i x) ∂γ
  simp_rw [hraw, Finset.mul_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => hA i),
    integral_finset_sum Finset.univ (fun i _ => hB i),
    integral_finset_sum Finset.univ (fun i _ => hC i), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_assoc] using integral_gaussian_weighted_coordinate hf hg hχ hχc i

/-- Young's inequality absorbs the cutoff-gradient cross term into half of
the localized energy and a constant multiple of the squared function. -/
lemma cutoff_energy_young {n : ℕ} (a b C : ℝ) (hC : 0 ≤ C)
    (v w : Fin n → ℝ) (hw : ∀ i, |w i| ≤ C) :
    a ^ 2 * (∑ i, v i ^ 2) / 2 ≤ a ^ 2 * (∑ i, v i ^ 2) +
      b * (∑ i, (2 * a * w i) * v i) + 2 * (n : ℝ) * C ^ 2 * b ^ 2 := by
  have h (i : Fin n) : a ^ 2 * v i ^ 2 / 2 ≤
      a ^ 2 * v i ^ 2 + b * ((2 * a * w i) * v i) + 2 * C ^ 2 * b ^ 2 := by
    have hsq : w i ^ 2 ≤ C ^ 2 := by
      nlinarith [sq_abs (w i), abs_nonneg (w i), hw i]
    nlinarith [sq_nonneg (a * v i + 2 * b * w i),
      mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hsq)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  convert hs using 1
  ring

/-- For a smooth function whose value and differential Gaussian generator
belong to L², a compact cutoff bounds the localized squared gradient by twice
the absolute generator pairing plus its derivative error.
[OD14, §11.1, Prop. 11.28, localization estimate]
**Proof sketch.** Test localized integration by parts with the squared cutoff.
Young's inequality absorbs half of the localized gradient energy. Bound the
remaining derivative terms by the uniform cutoff bound and use L² product
integrability for the generator pairing. -/
lemma gaussian_caccioppoli_cutoff
    {f u χ : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hfl : MemLp f 2 γ) (hul : MemLp u 2 γ)
    (hu : u =ᵐ[γ] fun x => fderiv ℝ f x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχb : ∀ x, |χ x| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hdχ : ∀ x i, |fderiv ℝ χ x (Pi.single i 1)| ≤ C) :
    (∫ x, χ x ^ 2 * (∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2) ∂γ) ≤
      2 * (∫ x, |f x * u x| ∂γ) +
        4 * (n : ℝ) * C ^ 2 * (∫ x, f x ^ 2 ∂γ) := (by
    let d := fun (w : (Fin n → ℝ) → ℝ) i x => fderiv ℝ w x (Pi.single i 1)
    let W := fun x => χ x ^ 2
    let A := fun x => W x * ∑ i, (d f i x) ^ 2
    let J := fun x => f x * ∑ i, d W i x * d f i x
    let L := fun x => fderiv ℝ f x x - ∑ i, fderiv ℝ (d f i) x (Pi.single i 1)
    have hW : ContDiff ℝ 1 W := hχ.pow 2
    have hWc : HasCompactSupport W := hχc.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
    have hdf (i : Fin n) : Continuous (d f i) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hA : Integrable A γ :=
      (hW.continuous.mul (continuous_finset_sum _ fun i _ => (hdf i).pow 2)).integrable_of_hasCompactSupport
        hWc.mul_right
    have hJi (i : Fin n) : Integrable (fun x => f x * (d W i x * d f i x)) γ :=
      (hf.continuous.mul (((hW.continuous_fderiv (by norm_num)).clm_apply
        continuous_const).mul (hdf i))).integrable_of_hasCompactSupport
          (hWc.fderiv_apply ℝ (Pi.single i 1)).mul_right.mul_left
    have hJ : Integrable J γ := by
      dsimp only [J]
      simp_rw [Finset.mul_sum]
      exact integrable_finset_sum _ fun i _ => hJi i
    have hWb (x : Fin n → ℝ) : |W x| ≤ 1 := by
      obtain ⟨hl, hr⟩ := abs_le.mp (hχb x)
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith
    have hfu : Integrable (fun x => f x * u x) γ := hfl.integrable_mul hul
    have hB : Integrable (fun x => W x * f x * L x) γ := by
      apply (hfu.bdd_mul' hW.continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hWb x)).congr
      filter_upwards [hu] with x hx
      change W x * (f x * u x) = W x * f x * L x
      rw [hx]
      ring
    have hff : Integrable (fun x => f x ^ 2) γ := by
      simpa only [pow_two] using hfl.integrable_mul hfl
    have hw : (∫ x, A x ∂γ) = (∫ x, W x * f x * L x ∂γ) - ∫ x, J x ∂γ := by
      simpa only [A, J, L, d, pow_two] using integral_gaussian_weighted_gradient
        (hf.of_le (by norm_num)) hf hW hWc
    have hDW (x : Fin n → ℝ) (i : Fin n) : d W i x = 2 * χ x * d χ i x := by
      dsimp only [d, W]
      rw [fderiv_fun_pow 2 (hχ.differentiable le_rfl x)]
      simp
    have hpoint (x : Fin n → ℝ) : A x / 2 ≤ A x + J x + 2 * (n : ℝ) * C ^ 2 * f x ^ 2 := by
      simpa only [A, W, J, hDW] using
        cutoff_energy_young (χ x) (f x) C hC (fun i => d f i x) (fun i => d χ i x) (hdχ x)
    have hi := integral_mono (hA.div_const 2)
      ((hA.add hJ).add (hff.const_mul (2 * (n : ℝ) * C ^ 2))) hpoint
    have hBbound : (∫ x, W x * f x * L x ∂γ) ≤ ∫ x, |f x * u x| ∂γ := by
      apply integral_mono_ae hB hfu.abs
      filter_upwards [hu] with x hx
      change W x * f x * L x ≤ |f x * u x|
      change u x = L x at hx
      rw [← hx]
      calc
        _ ≤ |W x * (f x * u x)| := by rw [mul_assoc]; exact le_abs_self _
        _ = |W x| * |f x * u x| := abs_mul _ _
        _ ≤ |f x * u x| := mul_le_of_le_one_left (abs_nonneg _) (hWb x)
    change (∫ x, A x / 2 ∂γ) ≤
      ∫ x, A x + J x + 2 * (n : ℝ) * C ^ 2 * f x ^ 2 ∂γ at hi
    rw [integral_div, integral_add
        (show Integrable (fun x => A x + J x) γ from hA.add hJ)
        (hff.const_mul (2 * (n : ℝ) * C ^ 2)), integral_add hA hJ, integral_const_mul] at hi
    change (∫ x, A x ∂γ) ≤ _
    linarith
)

end BooleanAnalysis.GaussianSpace
