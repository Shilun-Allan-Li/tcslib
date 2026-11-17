/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.FunctionalDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Generator
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Regularization
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false

/-!
# Time differentiation of the Gaussian interpolation functional

## Main definitions

The bivariate probability profile and Ornstein–Uhlenbeck averaging are reused.

## Main results

* `hasDerivAt_gaussianProfile_exp_neg`: differentiating the positive-time
  profile gives the two slope-weighted Ornstein–Uhlenbeck generators.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/
set_option autoImplicit false
open MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
local instance {n : ℕ} (ρ : ℝ) : IsProbabilityMeasure (correlatedGaussianMeasure (n := n) ρ) := by
  rw [correlatedGaussianMeasure_eq]
  exact Measure.isProbabilityMeasure_map (by fun_prop)
/-- The Ornstein–Uhlenbeck generator of a C2 function is continuous. -/
private lemma continuous_gaussianGenerator {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : ContDiff ℝ 2 g) : Continuous (fun x =>
      (∑ i, fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single i 1)) -
        fderiv ℝ g x x) := by
  have hD := hg.continuous_fderiv (by norm_num)
  have hdf : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hH := hdf.continuous_fderiv le_rfl
  exact (continuous_finset_sum _ (fun i _ =>
    (hH.clm_apply continuous_const).clm_apply continuous_const)).sub (hD.clm_apply continuous_id)
/-- Bounded first and second derivatives give a linear-growth bound on the
Ornstein–Uhlenbeck generator.

**Proof sketch.** Bound each diagonal Hessian entry by the Hessian operator
norm, sum over the coordinates, and bound the drift by the gradient operator
norm times the input norm. -/
private lemma norm_gaussianGenerator_le {n : ℕ} {g : (Fin n → ℝ) → ℝ} {M K : ℝ}
    (hm : ∀ x, ‖fderiv ℝ g x‖ ≤ M)
    (hk : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ K) (x : Fin n → ℝ) :
    ‖(∑ i, fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single i 1)) -
      fderiv ℝ g x x‖ ≤ (n : ℝ) * K + M * ‖x‖ := by
  have he (i : Fin n) :
      ‖fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single i 1)‖ ≤ K := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) x (Pi.single i 1)‖ * ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖ :=
        (fderiv ℝ (fderiv ℝ g) x (Pi.single i 1)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖) *
          ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ g) x).le_opNorm _) (norm_nonneg _)
      _ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by rw [Pi.norm_single, norm_one, mul_one, mul_one]
      _ ≤ K := hk x
  calc
    _ ≤ ‖∑ i, fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single i 1)‖ +
        ‖fderiv ℝ g x x‖ := norm_sub_le _ _
    _ ≤ (∑ _i : Fin n, K) + M * ‖x‖ :=
      add_le_add (norm_sum_le_of_le _ (fun i _ => he i))
        (((fderiv ℝ g x).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hm x) (norm_nonneg x)))
    _ = _ := by simp
/-- For clipped C2 initial data with bounded first and second derivatives,
the positive-time derivative of the Gaussian profile functional is the
integral of its two slope-weighted Ornstein–Uhlenbeck generators.
[MN15, §2, interpolation derivative]

**Proof sketch.** The generator equation gives each pointwise time derivative.
Derivative commutation bounds the gradient and Hessian of every positive-time
average uniformly by the initial bounds. Hence the generator is bounded by a
constant plus the starting-point norm. The correlated Gaussian marginals have
finite first norm moments, so this bound is integrable and permits the profile
chain rule under the integral. -/
lemma hasDerivAt_gaussianProfile_exp_neg {n : ℕ} {ρ δ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (hδ : 0 < δ)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {M K : ℝ}
    (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (hrange : ∀ x, f x ∈ Set.Icc δ (1-δ)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∫ z, gaussianBivariateStability ρ
      (gaussianNoise (Real.exp (-u)) f z.1) (gaussianNoise (Real.exp (-u)) f z.2)
        ∂correlatedGaussianMeasure ρ)
      (∫ z, gaussianBivariateSlope ρ
          (gaussianNoise (Real.exp (-t)) f z.1) (gaussianNoise (Real.exp (-t)) f z.2) *
          ((∑ i, fderiv ℝ (fderiv ℝ (gaussianNoise (Real.exp (-t)) f)) z.1
            (Pi.single i 1) (Pi.single i 1)) -
            fderiv ℝ (gaussianNoise (Real.exp (-t)) f) z.1 z.1) +
        gaussianBivariateSlope ρ
          (gaussianNoise (Real.exp (-t)) f z.2) (gaussianNoise (Real.exp (-t)) f z.1) *
          ((∑ i, fderiv ℝ (fderiv ℝ (gaussianNoise (Real.exp (-t)) f)) z.2
            (Pi.single i 1) (Pi.single i 1)) -
            fderiv ℝ (gaussianNoise (Real.exp (-t)) f) z.2 z.2)
        ∂correlatedGaussianMeasure ρ) t := by
  let U := fun q : ℝ => gaussianNoise (Real.exp (-q)) f
  let L := fun q (x : Fin n → ℝ) =>
    (∑ i, fderiv ℝ (fderiv ℝ (U q)) x (Pi.single i 1) (Pi.single i 1)) -
      fderiv ℝ (U q) x x
  have hb (x) : |f x| ≤ 1 := by
    rw [abs_of_nonneg (hδ.le.trans (hrange x).1)]
    linarith [(hrange x).2]
  have hi : Integrable f (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    Integrable.of_bound hf.continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ f 0)).trans (hm 0)
  have hK : 0 ≤ K := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hk 0)
  have hr (q : ℝ) (hq : 0 < q) : Real.exp (-q) ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_trans (by norm_num) (Real.exp_pos _), Real.exp_lt_one_iff.mpr (neg_neg_of_pos hq)⟩
  have hUc (q) : Continuous (U q) := continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_gaussianNoise_of_contDiff_bounded (hf.of_le (by norm_num)) hb hm _ x).continuousAt
  have hUs (q) (hq : 0 < q) : ContDiff ℝ 2 (U q) :=
    (gaussianNoise_smooth (hr q hq) hi).of_le (WithTop.coe_le_coe.mpr le_top)
  have hLcont (q) (hq : 0 < q) : Continuous (L q) := continuous_gaussianGenerator (hUs q hq)
  have hUrange (q x) : U q x ∈ Set.Ioo (0 : ℝ) 1 := by
    have hh := gaussianNoise_mem_clippedInterval hδ hf.continuous.measurable hrange (Real.exp (-q)) x
    exact ⟨hδ.trans_le hh.1, by linarith [hh.2]⟩
  have hLbound (q) (hq : 0 < q) (x) : ‖L q x‖ ≤ (n : ℝ) * K + M * ‖x‖ := by
    apply norm_gaussianGenerator_le
    · intro x
      exact (norm_fderiv_gaussianNoise_commutation_le (hf.of_le (by norm_num)) hb hm _ x).trans
        (mul_le_of_le_one_left hM (abs_le.mpr ⟨(hr q hq).1.le, (hr q hq).2.le⟩))
    · intro x
      exact (norm_fderiv_fderiv_gaussianNoise_commutation_le hf hb hm hk _ x).trans
        (mul_le_of_le_one_left hK (by have hh := hr q hq; nlinarith [hh.1, hh.2]))
  have hnorm : Integrable (fun x : Fin n → ℝ => ‖x‖)
      (Measure.pi fun _ => standardGaussianMeasure) := by
    simpa only [pow_one] using (integrable_gaussianPi_norm_pow (n := n) 1)
  have hfst : MeasurePreserving Prod.fst (correlatedGaussianMeasure (n := n) ρ)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩
  have hsnd : MeasurePreserving Prod.snd (correlatedGaussianMeasure (n := n) ρ)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    ⟨measurable_snd, correlatedGaussianMeasure_snd ⟨hρ.1.le,hρ.2.le⟩⟩
  have hB : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      2 * (n : ℝ) * K + M * (‖z.1‖ + ‖z.2‖)) (correlatedGaussianMeasure ρ) :=
    (integrable_const _).add (((hfst.integrable_comp_of_integrable hnorm).add
      (hsnd.integrable_comp_of_integrable hnorm)).const_mul M)
  have hqpos (q) (hq : q ∈ Metric.ball t (t/2)) : 0 < q := by
    rw [Metric.mem_ball, Real.dist_eq] at hq
    have hh := (abs_lt.mp hq).1
    linarith
  exact (hasDerivAt_integral_gaussianBivariateStability (correlatedGaussianMeasure ρ) hρ
    (fun q z => U q z.1) (fun q z => U q z.2)
    (fun q z => L q z.1) (fun q z => L q z.2) (half_pos ht)
    (fun q => (hUc q).measurable.comp measurable_fst)
    (fun q => (hUc q).measurable.comp measurable_snd)
    ((hLcont t ht).measurable.comp measurable_fst) ((hLcont t ht).measurable.comp measurable_snd)
    (fun q _ z => hUrange q z.1) (fun q _ z => hUrange q z.2)
    (fun z q hq => hasDerivAt_gaussianNoise_exp_neg_generator hf hb hm hk z.1 (hqpos q hq))
    (fun z q hq => hasDerivAt_gaussianNoise_exp_neg_generator hf hb hm hk z.2 (hqpos q hq))
    _ hB (fun z q hq => by
      have h1 := hLbound q (hqpos q hq) z.1
      have h2 := hLbound q (hqpos q hq) z.2
      simp only [Real.norm_eq_abs] at h1 h2
      linarith)).2
end BooleanAnalysis.GaussianSpace
