/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.LocalEnergy
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.Localization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Global Gaussian energy identity

## Main definitions

The Gaussian product law, coordinate derivatives, and smooth cutoffs are reused.

## Main results

* `memLp_fderiv_coordinates_of_gaussian_differential`: L² control of a smooth
  function and its Gaussian generator implies L² control of every coordinate derivative.
* `gaussian_differential_integration_by_parts`: Gaussian generator pairing equals
  the integral of the coordinate gradient product.

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

/-- Uniform bounds on localized squared gradient energy imply that all
coordinate derivatives belong to Gaussian L².
**Proof sketch.** The cutoff energy densities converge to the squared gradient
length. Fatou gives its integrability; each coordinate square is bounded by it. -/
lemma memLp_coordinate_derivatives_of_cutoff_energy_bound
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {χ : ℕ → (Fin n → ℝ) → ℝ}
    (hχ : ∀ k, Continuous (χ k)) (hχc : ∀ k, HasCompactSupport (χ k))
    (hχlim : ∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1))
    {A : ℝ} (hbound : ∀ k, (∫ x, χ k x ^ 2 *
      ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂γ) ≤ A) :
    ∀ i : Fin n, MemLp (fun x => fderiv ℝ f x (Pi.single i 1)) 2 γ := by
  let E := fun x => ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2
  have hdc (i : Fin n) : Continuous (fun x => fderiv ℝ f x (Pi.single i 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hEc : Continuous E := continuous_finset_sum _ fun i _ => (hdc i).pow 2
  have hEn (x) : 0 ≤ E x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : Integrable E γ := by
    apply integrable_of_nonneg_tendsto_integral_bounded
      (F := fun k x => χ k x ^ 2 * E x) (C := A)
    · intro k
      exact ((hχ k).pow 2 |>.mul hEc).integrable_of_hasCompactSupport
        (by simpa only [pow_two] using
          ((hχc k).mul_right (f' := χ k)).mul_right (f' := E))
    · exact fun k x => mul_nonneg (sq_nonneg _) (hEn x)
    · exact hEc.aestronglyMeasurable
    · exact Eventually.of_forall fun x => by simpa using (hχlim x).pow 2 |>.mul_const (E x)
    · exact hbound
  intro i
  apply (memLp_two_iff_integrable_sq (hdc i).aestronglyMeasurable).mpr
  apply hE.mono' ((hdc i).pow 2).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (fderiv ℝ f x (Pi.single j 1)))
      (Finset.mem_univ i)

/-- A C² function and its differential Gaussian generator belonging to L²
force every coordinate derivative to belong to Gaussian L².
[OD14, §11.1, Prop. 11.28, energy-domain justification]
**Proof sketch.** Apply the Caccioppoli estimate to the smooth cutoff sequence.
Its uniform derivative bound gives a common finite energy bound, and Fatou
then gives L² integrability of each coordinate derivative. -/
lemma memLp_fderiv_coordinates_of_gaussian_differential
    {f u : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hfl : MemLp f 2 γ) (hul : MemLp u 2 γ)
    (hu : u =ᵐ[γ] fun x => fderiv ℝ f x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)) :
    ∀ i : Fin n, MemLp (fun x => fderiv ℝ f x (Pi.single i 1)) 2 γ := by
  obtain ⟨χ, C, hC, hχ, hχlim, _, hdχ⟩ := exists_gaussian_smooth_cutoff_sequence n
  apply memLp_coordinate_derivatives_of_cutoff_energy_bound (hf.of_le (by norm_num))
    (fun k => (hχ k).1.continuous) (fun k => (hχ k).2.1) hχlim
    (A := 2 * (∫ x, |f x * u x| ∂γ) + 4 * (n : ℝ) * C ^ 2 * (∫ x, f x ^ 2 ∂γ))
  intro k
  apply gaussian_caccioppoli_cutoff hf hfl hul hu
    ((hχ k).1.of_le (WithTop.coe_le_coe.mpr le_top)) (hχ k).2.1
    (fun x => by rw [abs_of_nonneg ((hχ k).2.2.1 x).1]; exact ((hχ k).2.2.1 x).2) hC
  intro x i
  simpa only [Real.norm_eq_abs] using hdχ k x i

/-- Bounded measurable cutoffs converging to one preserve an integrable integral.
**Proof sketch.** The norm of the integrand dominates every cutoff product. -/
lemma tendsto_integral_cutoff_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ψ : ℕ → α → ℝ} {H : α → ℝ}
    (hψm : ∀ k, AEStronglyMeasurable (ψ k) μ)
    (hψ : ∀ k x, ψ k x ∈ Set.Icc (0 : ℝ) 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => ψ k x) atTop (𝓝 1))
    (hH : Integrable H μ) :
    Tendsto (fun k => ∫ x, ψ k x * H x ∂μ) atTop (𝓝 (∫ x, H x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖H x‖)
    (fun k => (hψm k).mul hH.aestronglyMeasurable) hH.norm
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg (hψ k x).1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hψ k x).2 (norm_nonneg (H x))
  · filter_upwards [hlim] with x hx
    simpa only [one_mul] using hx.mul_const (H x)

/-- Uniformly bounded measurable multipliers converging to zero make every
integrable pairing vanish. **Proof sketch.** Apply dominated convergence with
the uniform bound times the norm of the fixed integrable factor. -/
lemma tendsto_integral_vanishing_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ζ : ℕ → α → ℝ} {H : α → ℝ} {C : ℝ}
    (hζm : ∀ k, AEStronglyMeasurable (ζ k) μ)
    (hζ : ∀ k x, ‖ζ k x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => ζ k x) atTop (𝓝 0))
    (hH : Integrable H μ) :
    Tendsto (fun k => ∫ x, ζ k x * H x ∂μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun k => ∫ x, ζ k x * H x ∂μ) atTop
      (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => C * ‖H x‖)
      (fun k => (hζm k).mul hH.aestronglyMeasurable) (hH.norm.const_mul C)
    · intro k
      exact Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (hζ k x) (norm_nonneg (H x))
    · filter_upwards [hlim] with x hx
      simpa only [zero_mul] using hx.mul_const (H x)
  simpa only [integral_zero] using ht

/-- Coordinate L² derivatives give the global Gaussian energy identity when
compact cutoffs approach one with bounded derivatives tending to zero.
[OD14, §11.1, Proposition 11.28, cutoff justification]
**Proof sketch.** Products of L² coordinate derivatives are integrable. Apply
localized integration by parts, then dominated convergence to both bulk terms
and each boundary term. -/
lemma integral_gaussian_gradient_of_cutoffs
    {f g v : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hf2 : MemLp f 2 γ) (hv2 : MemLp v 2 γ)
    (hdf : ∀ i : Fin n, MemLp (fun x => fderiv ℝ f x (Pi.single i 1)) 2 γ)
    (hdg : ∀ i : Fin n, MemLp (fun x => fderiv ℝ g x (Pi.single i 1)) 2 γ)
    (hv : v =ᵐ[γ] (fun x => fderiv ℝ g x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)))
    (ψ : ℕ → (Fin n → ℝ) → ℝ) (hψ : ∀ k, ContDiff ℝ 1 (ψ k))
    (hψc : ∀ k, HasCompactSupport (ψ k))
    (hψrange : ∀ k x, ψ k x ∈ Set.Icc (0 : ℝ) 1)
    (hψlim : ∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 1))
    {C : ℝ} (hDψ : ∀ k (i : Fin n) x, ‖fderiv ℝ (ψ k) x (Pi.single i 1)‖ ≤ C)
    (hDψlim : ∀ (i : Fin n) x, Tendsto
      (fun k => fderiv ℝ (ψ k) x (Pi.single i 1)) atTop (𝓝 0)) :
    Integrable (fun x => ∑ i, fderiv ℝ f x (Pi.single i 1) *
      fderiv ℝ g x (Pi.single i 1)) γ ∧
    (∫ x, f x * v x ∂γ) = ∫ x, ∑ i, fderiv ℝ f x (Pi.single i 1) *
      fderiv ℝ g x (Pi.single i 1) ∂γ := by
  let E := fun x => ∑ i, fderiv ℝ f x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1)
  have hE : Integrable E γ :=
    integrable_finset_sum Finset.univ (fun i _ => (hdf i).integrable_mul (hdg i))
  have hfv : Integrable (fun x => f x * v x) γ := hf2.integrable_mul hv2
  have hA : Tendsto (fun k => ∫ x, ψ k x * E x ∂γ) atTop (𝓝 (∫ x, E x ∂γ)) :=
    tendsto_integral_cutoff_mul (fun k => (hψ k).continuous.aestronglyMeasurable)
      hψrange (Eventually.of_forall hψlim) hE
  have hB : Tendsto (fun k => ∫ x, ψ k x * (f x * v x) ∂γ)
      atTop (𝓝 (∫ x, f x * v x ∂γ)) :=
    tendsto_integral_cutoff_mul (fun k => (hψ k).continuous.aestronglyMeasurable)
      hψrange (Eventually.of_forall hψlim) hfv
  have hJi (k : ℕ) (i : Fin n) : Integrable (fun x => f x *
      (fderiv ℝ (ψ k) x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1))) γ := by
    have hdψ : Continuous (fun x => fderiv ℝ (ψ k) x (Pi.single i 1)) :=
      ((hψ k).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdgc : Continuous (fun x => fderiv ℝ g x (Pi.single i 1)) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact (hf.continuous.mul (hdψ.mul hdgc)).integrable_of_hasCompactSupport
      ((hψc k).fderiv_apply ℝ (Pi.single i 1)).mul_right.mul_left
  have hJilim (i : Fin n) : Tendsto
      (fun k => ∫ x, f x * (fderiv ℝ (ψ k) x (Pi.single i 1) *
        fderiv ℝ g x (Pi.single i 1)) ∂γ) atTop (𝓝 0) := by
    have hdψ (k : ℕ) : Continuous (fun x => fderiv ℝ (ψ k) x (Pi.single i 1)) :=
      ((hψ k).continuous_fderiv (by norm_num)).clm_apply continuous_const
    simpa only [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
      tendsto_integral_vanishing_mul (fun k => (hdψ k).aestronglyMeasurable)
        (fun k x => hDψ k i x) (Eventually.of_forall (hDψlim i))
        (hf2.integrable_mul (hdg i))
  have hJrep (k : ℕ) : (∫ x, f x * (∑ i, fderiv ℝ (ψ k) x (Pi.single i 1) *
      fderiv ℝ g x (Pi.single i 1)) ∂γ) =
      ∑ i, ∫ x, f x * (fderiv ℝ (ψ k) x (Pi.single i 1) *
        fderiv ℝ g x (Pi.single i 1)) ∂γ := by
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum Finset.univ (fun i _ => hJi k i)
  have hJ : Tendsto (fun k => ∫ x, f x *
      (∑ i, fderiv ℝ (ψ k) x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1)) ∂γ)
      atTop (𝓝 0) := by
    simpa only [← hJrep, Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun i _ => hJilim i)
  have hloc (k : ℕ) : (∫ x, ψ k x * E x ∂γ) =
      (∫ x, ψ k x * (f x * v x) ∂γ) -
      ∫ x, f x * (∑ i, fderiv ℝ (ψ k) x (Pi.single i 1) *
        fderiv ℝ g x (Pi.single i 1)) ∂γ := by
    calc
      _ = (∫ x, ψ k x * f x * (fderiv ℝ g x x -
          ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) ∂γ) -
          ∫ x, f x * (∑ i, fderiv ℝ (ψ k) x (Pi.single i 1) *
            fderiv ℝ g x (Pi.single i 1)) ∂γ :=
        integral_gaussian_weighted_gradient hf hg (hψ k) (hψc k)
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hv] with x hx
        rw [← hx]
        ring
  have hright : Tendsto (fun k => ∫ x, ψ k x * E x ∂γ)
      atTop (𝓝 (∫ x, f x * v x ∂γ)) := by
    simpa only [sub_zero, ← hloc] using hB.sub hJ
  exact ⟨hE, (tendsto_nhds_unique hA hright).symm⟩

/-- For C² functions with L² values and L² differential Gaussian generators,
the gradient product is integrable and its integral equals the generator pairing.
[OD14, Prop. 11.28]
**Proof sketch.** The energy estimate puts both gradients in L². Apply the
localized identity to compact cutoffs approaching one. Dominated convergence
passes the bulk terms to their limits and sends the boundary terms to zero. -/
lemma gaussian_differential_integration_by_parts
    {f g u v : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfl : MemLp f 2 γ) (hul : MemLp u 2 γ) (hgl : MemLp g 2 γ) (hvl : MemLp v 2 γ)
    (hu : u =ᵐ[γ] fun x => fderiv ℝ f x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1))
    (hv : v =ᵐ[γ] fun x => fderiv ℝ g x x -
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) :
    Integrable (fun x => ∑ i : Fin n,
      fderiv ℝ f x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1)) γ ∧
      (∫ x, f x * v x ∂γ) = ∫ x, ∑ i : Fin n,
        fderiv ℝ f x (Pi.single i 1) * fderiv ℝ g x (Pi.single i 1) ∂γ := (by
    have hdf := memLp_fderiv_coordinates_of_gaussian_differential hf hfl hul hu
    have hdg := memLp_fderiv_coordinates_of_gaussian_differential hg hgl hvl hv
    obtain ⟨χ, C, _, hχ, hχlim, hdχlim, hdχ⟩ := exists_gaussian_smooth_cutoff_sequence n
    exact integral_gaussian_gradient_of_cutoffs (hf.of_le (by norm_num)) hg hfl hvl hdf hdg hv
      χ (fun k => (hχ k).1.of_le (WithTop.coe_le_coe.mpr le_top))
      (fun k => (hχ k).2.1) (fun k => (hχ k).2.2.1) hχlim
      (fun k i x => hdχ k x i) (fun i x => hdχlim x i)
)

end BooleanAnalysis.GaussianSpace
