/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.Derivative
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.Integration
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.TestFunctions
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.Energy
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.EntropyScalar
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.EntropyNormalized
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.Entropy
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The positive Ornstein–Uhlenbeck generator

## Contents

* `OrnsteinUhlenbeck.Derivative`: Gaussian noise time differentiation from a strong
  generator limit.
* `OrnsteinUhlenbeck.Integration`: Gaussian integration by parts against compact tests.
* `OrnsteinUhlenbeck.TestFunctions`: weak identification of strong generator limits.
* `OrnsteinUhlenbeck.Localization`: smooth cutoff sequences and Fatou integrability.
* `OrnsteinUhlenbeck.LocalEnergy`: localized Green identities and energy estimates.
* `OrnsteinUhlenbeck.Energy`: global gradient integrability and integration by parts.
* `OrnsteinUhlenbeck.EntropyScalar`: power secants, entropy Fatou bounds, and rescaling.
* `OrnsteinUhlenbeck.EntropyNormalized`: normalized Gaussian entropy bounds.
* `OrnsteinUhlenbeck.Entropy`: Gaussian log-Sobolev from the strong generator limit.

## Main definitions

* `HasGaussianGenerator`: the positive generator as a strong Gaussian L² limit.
* `InGaussianGeneratorDomain`: existence of that limit.
* `gaussianOUDifferential`: the ordinary differential expression `x·∇f-Δf`.
* `gaussianEntropy`: entropy relative to the existing product Gaussian law.

## Main results

The strong generator is unique, commutes with Gaussian noise, is symmetric,
and gives pointwise semigroup time and correlation derivatives. On smooth functions
it agrees almost everywhere with the differential expression and satisfies Gaussian
integration by parts. Gaussian log-Sobolev holds on the strong generator domain,
including entropy integrability. Its smooth gradient corollary identifies the
energy with the squared Euclidean gradient.
The generator relation avoids choosing representatives of almost-everywhere
equivalence classes and gives an explicit domain for the source's operator.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.24, Remark 11.25,
  Propositions 11.26–11.28, Gaussian Log-Sobolev and Exercise 11.18.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A function has positive Gaussian generator `g` when `(f-U_(exp(-t))f)/t`
converges to `g` in Gaussian L² as `t` decreases to zero.
[OD14, Def. 11.24; Remark 11.25; Ex. 11.18]
Both representatives belong to L². The positive sign agrees with the number
operator; its Hermite eigenvalues are the nonnegative total degrees. -/
def HasGaussianGenerator {n : ℕ} (f g : (Fin n → ℝ) → ℝ) : Prop :=
  MemLp f 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) ∧
    MemLp g 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) ∧
    Tendsto (fun t : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x)
      2 (Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The strong Gaussian generator relation consists of Gaussian L² membership
of both functions and convergence of the positive-time generator quotients.
[OD14, Def. 11.24; Remark 11.25; Ex. 11.18] -/
lemma HasGaussianGenerator_iff {n : ℕ} {f g : (Fin n → ℝ) → ℝ} :
    HasGaussianGenerator f g ↔
      MemLp f 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) ∧
      MemLp g 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) ∧
      Tendsto (fun t : ℝ => eLpNorm
        (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x)
        2 (Measure.pi fun _ : Fin n => standardGaussianMeasure))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := (by
  rfl
)

/-- The strong L² domain of the positive Ornstein–Uhlenbeck generator.
[OD14, Def. 11.24; Ex. 11.18] -/
def InGaussianGeneratorDomain {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g, HasGaussianGenerator f g

/-- The classical positive Ornstein–Uhlenbeck expression `x·∇f-Δf`, evaluated
using Fréchet derivatives and the standard coordinate vectors.
[OD14, Prop. 11.26] Totalized derivatives are used only under smoothness hypotheses. -/
noncomputable def gaussianOUDifferential {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (fderiv ℝ f x) x - ∑ i : Fin n,
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)

/-- The positive differential Gaussian generator is the derivative evaluated
on the input minus the sum of the coordinate second derivatives.
[OD14, Prop. 11.26] -/
lemma gaussianOUDifferential_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    gaussianOUDifferential f = fun x =>
      (fderiv ℝ f x) x - ∑ i : Fin n,
        (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i 1)) x)
          (Pi.single i 1) := (by
  rfl
)

/-- Entropy of a nonnegative function under the product standard Gaussian law.
[OD14, §11.1, Gaussian Log-Sobolev]
Analytic results impose the needed sign and integrability conditions explicitly. -/
noncomputable def gaussianEntropy {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
    (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) *
      Real.log (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))

/-- Gaussian entropy is the integral of the function times its logarithm
minus its mass times the logarithm of that mass.
[OD14, §11.1, Gaussian Log-Sobolev] -/
lemma gaussianEntropy_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    gaussianEntropy f =
      (∫ x, f x * Real.log (f x)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
      (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) *
        Real.log (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) :=
  (by
  rfl
)

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- The strong L² generator is unique up to Gaussian almost-everywhere equality.
[OD14, Def. 11.24] **Proof sketch.** Uniqueness of limits gives zero L² distance
between the two proposed limits, hence almost-everywhere equality. -/
theorem gaussianGenerator_unique {f g h : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (hfh : HasGaussianGenerator f h) :
    g =ᵐ[γ] h := (by
  rcases hfg with ⟨hf, hg, hlim_g⟩
  rcases hfh with ⟨_, hh, hlim_h⟩
  let q : ℝ → (Fin n → ℝ) → ℝ :=
    fun t x => (f x - gaussianNoise (Real.exp (-t)) f x) / t
  have hq (t : ℝ) (ht : 0 < t) : MemLp (q t) 2 γ := by
    have hρ : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Real.exp_pos _).le,
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
    convert (hf.sub (gaussianNoise_memLp hρ 2 (by norm_num) hf)).const_smul t⁻¹ using 1
    ext x
    change (f x - gaussianNoise (Real.exp (-t)) f x) / t =
      t⁻¹ * (f x - gaussianNoise (Real.exp (-t)) f x)
    ring
  have hsum : Tendsto
      (fun t => eLpNorm (q t - h) 2 γ + eLpNorm (q t - g) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_add] using hlim_h.add hlim_g
  have hzero : eLpNorm (g - h) 2 γ = 0 := by
    apply le_antisymm _ (zero_le _)
    apply ge_of_tendsto hsum
    filter_upwards [self_mem_nhdsWithin] with t ht
    calc
      eLpNorm (g - h) 2 γ =
          eLpNorm ((q t - h) - (q t - g)) 2 γ := by
        congr 1
        ext x
        change g x - h x = (q t x - h x) - (q t x - g x)
        ring
      _ ≤ eLpNorm (q t - h) 2 γ + eLpNorm (q t - g) 2 γ :=
        eLpNorm_sub_le ((hq t ht).sub hh).aestronglyMeasurable
          ((hq t ht).sub hg).aestronglyMeasurable (by norm_num)
  have hae := (eLpNorm_eq_zero_iff (hg.sub hh).aestronglyMeasurable (by norm_num)).mp hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx
)


/-- On smooth functions in the strong generator domain the generator agrees
almost everywhere with `x·∇f-Δf`. [OD14, Prop. 11.26]

**Proof sketch.** Pair the strong generator limit against compactly supported
smooth tests. Noise symmetry, the test function's pointwise Mehler quotient limit,
and dominated convergence give the differential pairing. Gaussian integration by
parts transfers the differential expression to the original function. Equality
against all compact smooth tests gives almost-everywhere equality. -/
theorem gaussianGenerator_eq_differential {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (hf : ContDiff ℝ 3 f) :
    g =ᵐ[γ] gaussianOUDifferential f := (by
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))
  rcases HasGaussianGenerator_iff.mp hfg with ⟨hfl, hgl, hlim⟩
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hD : Continuous (gaussianOUDifferential f) := by
    rw [gaussianOUDifferential_eq]
    convert (continuous_gaussianGenerator hf2).neg using 1
    funext x
    simp only [fderiv_fderiv_apply_const_of_contDiff hf2]
    ring
  refine ae_eq_of_integral_contDiff_smul_eq
    (hgl.integrable (by norm_num)).locallyIntegrable hD.locallyIntegrable ?_
  intro φ hφ hφc
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hs := integral_mul_gaussian_differential_of_strong_limit hfl hgl hlim hφ2 hφc
  have hw := integral_mul_gaussian_differential hf2 hφ2 hφc
  simpa only [gaussianOUDifferential_eq, smul_eq_mul, mul_comm] using hs.trans hw
)

/-- Gaussian noise commutes with the strong positive generator.
[OD14, Prop. 11.27] **Proof sketch.** Apply the bounded L² noise operator to the
generator difference quotients and use the semigroup law. -/
theorem gaussianGenerator_noise {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    HasGaussianGenerator (gaussianNoise ρ f) (gaussianNoise ρ g) := (by
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))
  rcases hfg with ⟨hf, hg, hlim⟩
  have hfi := hf.integrable (by norm_num)
  have hgi := hg.integrable (by norm_num)
  have hsub {u v : (Fin n → ℝ) → ℝ}
      (hu : Integrable u γ) (hv : Integrable v γ) :
      gaussianNoise ρ (fun x => u x - v x) =
        fun x => gaussianNoise ρ u x - gaussianNoise ρ v x := by
    have heq : (fun x => u x - v x) = (fun x => u x + (-1) * v x) := by
      funext x
      ring
    rw [heq, gaussianNoise_add hρ hu (hv.const_mul (-1)), gaussianNoise_const_mul]
    funext x
    ring
  have hdiv (u : (Fin n → ℝ) → ℝ) (t : ℝ) :
      gaussianNoise ρ (fun x => u x / t) =
        fun x => gaussianNoise ρ u x / t := by
    simpa only [div_eq_mul_inv, mul_comm] using gaussianNoise_const_mul ρ t⁻¹ u
  refine ⟨gaussianNoise_memLp hρ 2 (by norm_num) hf,
    gaussianNoise_memLp hρ 2 (by norm_num) hg, ?_⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      eLpNorm (fun x =>
        (gaussianNoise ρ f x -
          gaussianNoise (Real.exp (-t)) (gaussianNoise ρ f) x) / t -
            gaussianNoise ρ g x) 2 γ ≤
        eLpNorm (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) 2 γ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hτ : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Real.exp_pos _).le,
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
    have hft := gaussianNoise_memLp hτ 2 (by norm_num) hf
    have hfti := hft.integrable (by norm_num)
    have herr : MemLp
        (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) 2 γ := by
      convert ((hf.sub hft).const_smul t⁻¹).sub hg using 1
      ext x
      change (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x =
        t⁻¹ * (f x - gaussianNoise (Real.exp (-t)) f x) - g x
      ring
    have hcomm :
        gaussianNoise ρ (gaussianNoise (Real.exp (-t)) f) =ᵐ[γ]
          gaussianNoise (Real.exp (-t)) (gaussianNoise ρ f) :=
      (gaussianNoise_compose hρ hτ hfi).trans (by
        simpa only [mul_comm] using (gaussianNoise_compose hτ hρ hfi).symm)
    have herror :
        gaussianNoise ρ
            (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) =ᵐ[γ]
          (fun x => (gaussianNoise ρ f x -
            gaussianNoise (Real.exp (-t)) (gaussianNoise ρ f) x) / t -
              gaussianNoise ρ g x) := by
      rw [hsub
        (show Integrable (fun x =>
          (f x - gaussianNoise (Real.exp (-t)) f x) / t) γ from
            (hfi.sub hfti).div_const t) hgi,
        hdiv, hsub hfi hfti]
      filter_upwards [hcomm] with x hx
      rw [hx]
    calc
      _ = eLpNorm (gaussianNoise ρ
          (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x)) 2 γ :=
        eLpNorm_congr_ae herror.symm
      _ ≤ _ := gaussianNoise_contract hρ 2 (by norm_num) herr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le _) hbound
)

/-- Differentiating Gaussian noise in its correlation parameter gives the noisy
generator divided by that correlation. [OD14, Prop. 11.27]

**Proof sketch.** Differentiate the semigroup law at its identity in L², then use
the interior Gaussian kernel to obtain pointwise derivatives. -/
theorem hasDerivAt_gaussianNoise {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (hρne : ρ ≠ 0)
    (x : Fin n → ℝ) :
    HasDerivAt (fun r => gaussianNoise r f x) (gaussianNoise ρ g x / ρ) ρ := (by
  have hpos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (z : Fin n → ℝ) :
      HasDerivAt (fun s => gaussianNoise s f z) (gaussianNoise r g z / r) r := by
    have hd : HasDerivAt (fun s : ℝ => gaussianNoise (Real.exp (-s)) f z)
        (-gaussianNoise r g z) (-Real.log r) := by
      simpa only [neg_neg, Real.exp_log hr] using
        hasDerivAt_gaussianNoise_exp_of_strong_limit hfg.1 hfg.2.1 hfg.2.2
          (-Real.log r) (neg_pos.mpr (Real.log_neg hr hr1)) z
    have heq : (fun s => gaussianNoise s f z) =ᶠ[𝓝 r]
        (fun s => gaussianNoise (Real.exp (-(-Real.log s))) f z) := by
      filter_upwards [eventually_gt_nhds hr] with s hs
      simp only [neg_neg, Real.exp_log hs]
    simpa only [neg_mul_neg, div_eq_mul_inv] using
      ((hd.comp r (Real.hasDerivAt_log hr.ne').neg).congr_of_eventuallyEq heq)
  rcases lt_or_gt_of_ne hρne with hn | hp
  · have href (r : ℝ) (w : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
        gaussianNoise (-r) w (-z) = gaussianNoise r w z := by
      simp only [gaussianNoise_eq, neg_sq, Pi.neg_apply, neg_mul_neg]
    have hd := (hpos (-ρ) (neg_pos.mpr hn) (by linarith [hρ.1]) (-x)).comp ρ
      (show HasDerivAt (fun r : ℝ => -r) (-1) ρ from (hasDerivAt_id' ρ).neg)
    simpa only [Function.comp_def, href, div_neg, mul_neg_one, neg_neg] using hd
  · exact hpos ρ hp hρ.2 x
)

/-- In the time parameter, differentiating the noise semigroup gives the
negative noisy positive generator. [OD14, Prop. 11.27]
**Proof sketch.** Differentiate the time semigroup in L¹ using the strong
L² generator limit and noise contraction. Split the positive time into two
equal pieces and apply fixed interior smoothing to obtain the pointwise derivative. -/
theorem hasDerivAt_gaussianNoise_exp {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => gaussianNoise (Real.exp (-s)) f x)
      (-gaussianNoise (Real.exp (-t)) g x) t := (by
  exact hasDerivAt_gaussianNoise_exp_of_strong_limit
    hfg.1 hfg.2.1 hfg.2.2 t ht x
)

/-- The Gaussian generator is symmetric on its strong L² domain.
[OD14, Prop. 11.28] **Proof sketch.** Pair the difference quotients using
self-adjointness of noise, then pass to their L² limits. -/
theorem gaussianGenerator_selfAdjoint {f g u v : (Fin n → ℝ) → ℝ}
    (hfu : HasGaussianGenerator f u) (hgv : HasGaussianGenerator g v) :
    (∫ x, f x * v x ∂γ) = ∫ x, u x * g x ∂γ := (by
  rcases hfu with ⟨hf, hu, hfu⟩
  rcases hgv with ⟨hg, hv, hgv⟩
  -- Use zero at nonpositive times to obtain an L²-valued family.
  let q (w : (Fin n → ℝ) → ℝ) (t : ℝ) : (Fin n → ℝ) → ℝ :=
    if 0 < t then fun x => (w x - gaussianNoise (Real.exp (-t)) w x) / t else 0
  have hq (w : (Fin n → ℝ) → ℝ) (hw : MemLp w 2 γ) (t : ℝ) :
      MemLp (q w t) 2 γ := by
    dsimp only [q]
    split_ifs with ht
    · have hρ : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
        ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Real.exp_pos _).le,
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
      convert (hw.sub (gaussianNoise_memLp hρ 2 (by norm_num) hw)).const_smul t⁻¹ using 1
      ext x
      change (w x - gaussianNoise (Real.exp (-t)) w x) / t =
        t⁻¹ * (w x - gaussianNoise (Real.exp (-t)) w x)
      ring
    · exact MemLp.zero
  have hconv {w z : (Fin n → ℝ) → ℝ} (hw : MemLp w 2 γ) (hz : MemLp z 2 γ)
      (hlim : Tendsto (fun t : ℝ => eLpNorm
        (fun x => (w x - gaussianNoise (Real.exp (-t)) w x) / t - z x) 2 γ)
          (𝓝[>] (0 : ℝ)) (𝓝 0)) :
      Tendsto (fun t => (hq w hw t).toLp (q w t))
        (𝓝[>] (0 : ℝ)) (𝓝 (hz.toLp z)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (q w) (hq w hw) z hz).mpr
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    simp only [q, if_pos ht]
    rfl
  have hpair {a b : (Fin n → ℝ) → ℝ} (ha : MemLp a 2 γ) (hb : MemLp b 2 γ) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂γ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hax hbx
    simp [hax, hbx, mul_comm]
  -- Pass the generator limits through the continuous L² pairing.
  have hleft : Tendsto
      (fun t => inner ℝ (hf.toLp f) ((hq g hg t).toLp (q g t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (hf.toLp f) (hv.toLp v))) :=
    tendsto_const_nhds.inner (hconv hg hv hgv)
  have hright : Tendsto
      (fun t => inner ℝ ((hq f hf t).toLp (q f t)) (hg.toLp g))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (hu.toLp u) (hg.toLp g))) :=
    (hconv hf hu hfu).inner tendsto_const_nhds
  simp_rw [hpair] at hleft hright
  -- Noise symmetry pairs the two difference quotients for positive times.
  have hsym : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (∫ x, f x * q g t x ∂γ) = ∫ x, q f t x * g x ∂γ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hρ : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Real.exp_pos _).le,
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
    simp only [q, if_pos ht]
    simp only [← mul_div_assoc, div_mul_eq_mul_div, mul_sub, sub_mul]
    rw [integral_div, integral_div,
      integral_sub
        (show Integrable (fun x => f x * g x) γ from hf.integrable_mul hg)
        (show Integrable (fun x => f x * gaussianNoise (Real.exp (-t)) g x) γ from
          hf.integrable_mul (gaussianNoise_memLp hρ 2 (by norm_num) hg)),
      integral_sub
        (show Integrable (fun x => f x * g x) γ from hf.integrable_mul hg)
        (show Integrable (fun x => gaussianNoise (Real.exp (-t)) f x * g x) γ from
          (gaussianNoise_memLp hρ 2 (by norm_num) hf).integrable_mul hg),
      gaussianNoise_selfAdjoint hρ hf hg]
  exact tendsto_nhds_unique hleft (hright.congr' (hsym.mono fun t ht => ht.symm))
)

/-- Gaussian integration by parts identifies generator pairing with gradient
energy for smooth functions in its domain. [OD14, Prop. 11.28]

**Proof sketch.** Identify the generators with their differential expressions.
Localized Gaussian integration by parts and a cutoff energy estimate put each
coordinate derivative in L². Apply the localized identity to expanding compact
cutoffs; dominated convergence removes the boundary terms and gives the result. -/
theorem gaussianGenerator_integration_by_parts {f g u v : (Fin n → ℝ) → ℝ}
    (hfu : HasGaussianGenerator f u) (hgv : HasGaussianGenerator g v)
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) :
    Integrable (fun x => ∑ i : Fin n,
      (fderiv ℝ f x) (Pi.single i 1) * (fderiv ℝ g x) (Pi.single i 1)) γ ∧
      (∫ x, f x * v x ∂γ) = ∫ x, ∑ i : Fin n,
        (fderiv ℝ f x) (Pi.single i 1) * (fderiv ℝ g x) (Pi.single i 1) ∂γ := (by
  rcases HasGaussianGenerator_iff.mp hfu with ⟨hfl, hul, _⟩
  rcases HasGaussianGenerator_iff.mp hgv with ⟨hgl, hvl, _⟩
  apply gaussian_differential_integration_by_parts
    (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hfl hul hgl hvl
  · simpa only [gaussianOUDifferential_eq] using gaussianGenerator_eq_differential hfu hf
  · simpa only [gaussianOUDifferential_eq] using gaussianGenerator_eq_differential hgv hg
)

/-- Gaussian log-Sobolev bounds entropy of `f²` by twice its generator energy.
[OD14, §11.1, Gaussian Log-Sobolev] The entropy integrability is part of the
conclusion, avoiding a vacuous use of a totalized integral.

**Proof sketch.** The strong generator limit determines the noise-energy deficit.
Hypercontractivity at exponents below two controls power secants; Fatou's
inequality gives entropy integrability and the bound at unit square mass.
Rescale by the input's square mass to obtain the general inequality. -/
theorem gaussian_logSobolev {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ ∧
      gaussianEntropy (fun x => f x ^ 2) ≤ 2 * ∫ x, f x * g x ∂γ := (by
  rcases HasGaussianGenerator_iff.mp hfg with ⟨hf, hg, hlim⟩
  simpa only [gaussianEntropy_eq] using gaussian_entropy_of_strong_limit hf hg hlim
)

/-- The smooth form of Gaussian log-Sobolev uses the squared Euclidean gradient.
[OD14, §11.1, Gaussian Log-Sobolev]

**Proof sketch.** Apply generator log-Sobolev and identify its energy through
Gaussian integration by parts with the same smooth function in both slots. -/
theorem gaussian_logSobolev_gradient {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (hf : ContDiff ℝ 3 f) :
    gaussianEntropy (fun x => f x ^ 2) ≤
      2 * ∫ x, ∑ i : Fin n, ((fderiv ℝ f x) (Pi.single i 1)) ^ 2 ∂γ := (by
  have h := (gaussian_logSobolev hfg).2
  rw [(gaussianGenerator_integration_by_parts hfg hfg hf hf).2] at h
  simpa only [pow_two] using h
)

end BooleanAnalysis.GaussianSpace
