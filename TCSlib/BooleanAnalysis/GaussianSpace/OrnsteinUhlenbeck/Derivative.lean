/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.OpenPos

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Differentiating the Gaussian noise semigroup

## Main definitions

The Gaussian noise operator and its positive-time parametrization are reused.

## Main results

* `enorm_gaussianNoise_apply_le`: interior noise evaluation is bounded on L¹.
* `gaussianNoise_compose_apply`: interior Gaussian noise composes pointwise.
* `gaussianNoise_exp_tendsto_quotient_L1`: a strong Gaussian L² generator limit
  yields the time derivative of the noise semigroup in L¹.
* `tendsto_gaussianNoise_apply_zero`: fixed interior Gaussian averaging sends
  L¹ convergence to zero to pointwise convergence to zero.
* `hasDerivAt_gaussianNoise_exp_of_strong_limit`: the strong Gaussian generator
  gives pointwise time derivatives at every positive time.

The generator assumptions are stated directly as integrability and convergence
conditions, allowing the parent generator module to use these results without
an import cycle. Kernel bounds, pointwise composition, and linearity support
passing the strong difference quotients through a fixed smoothing step.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.24 and Proposition 11.27.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Interior Gaussian noise evaluation is bounded by a fixed multiple of the
Gaussian L¹ seminorm. [OD14, §11.1, Gaussian noise kernel]
**Proof sketch.** Dominate the affine Gaussian kernel by a finite multiple of
the standard Gaussian law and bound the integral by its absolute integral. -/
lemma enorm_gaussianNoise_apply_le {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (x : Fin n → ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ f : (Fin n → ℝ) → ℝ, Integrable f γ →
        ‖gaussianNoise ρ f x‖ₑ ≤ C * eLpNorm f 1 γ := by
  let s := Real.sqrt (1 - ρ ^ 2)
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by
    nlinarith [hρ.1, hρ.2]))
  let v : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩
  have hv : v ≠ 0 := by
    intro h
    exact hs (eq_zero_of_pow_eq_zero (congrArg (fun a : ℝ≥0 => (a : ℝ)) h))
  have hvar : (v : ℝ) + ρ ^ 2 = 1 := by
    dsimp [v, s]
    rw [Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by nlinarith [hρ.1, hρ.2])]
    ring
  obtain ⟨C, hC, hbound⟩ := pi_gaussianNoise_le_smul ρ x v hv hvar
  refine ⟨C, hC, ?_⟩
  intro f hf
  have hfk := (hf.smul_measure hC).mono_measure hbound
  calc
    ‖gaussianNoise ρ f x‖ₑ ≤
        eLpNorm (fun y : Fin n → ℝ => f (fun i => ρ * x i + s * y i)) 1 γ := by
      rw [gaussianNoise_eq, eLpNorm_one_eq_lintegral_enorm]
      exact enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 (Measure.pi fun i => gaussianReal (ρ * x i) v) :=
      eLpNorm_comp_measurePreserving hfk.aestronglyMeasurable
        (measurePreserving_gaussianAffine_pi (fun i => ρ * x i) s)
    _ ≤ eLpNorm f 1 (C • γ) := eLpNorm_mono_measure f hbound
    _ = C * eLpNorm f 1 γ := by
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)]
      simp

local instance : Measure.IsOpenPosMeasure standardGaussianMeasure := by
  change Measure.IsOpenPosMeasure (gaussianReal 0 1)
  exact (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure

/-- Interior Gaussian noise sends Gaussian almost-everywhere equal integrable
inputs to functions equal at every point. [OD14, §11.1, Gaussian noise kernel]
**Proof sketch.** Noise respects almost-everywhere equality, and its interior
outputs are continuous. The Gaussian law gives positive mass to every open set. -/
lemma gaussianNoise_congr_ae_apply {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : Integrable f γ)
    (hfg : f =ᵐ[γ] g) (x : Fin n → ℝ) :
    gaussianNoise ρ f x = gaussianNoise ρ g x := by
  exact congrFun (Measure.eq_of_ae_eq
    (gaussianNoise_congr_ae ⟨hρ.1.le, hρ.2.le⟩ hfg)
    (gaussianNoise_smooth hρ hf).continuous
    (gaussianNoise_smooth hρ (hf.congr hfg)).continuous) x

/-- Composing two interior Gaussian noise operators multiplies their
correlations pointwise. [OD14, §11.1, Mehler semigroup]
**Proof sketch.** The almost-everywhere semigroup identity holds between
continuous interior noise outputs, so Gaussian full support makes it pointwise. -/
lemma gaussianNoise_compose_apply {ρ σ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (hσ : σ ∈ Set.Ioo (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) (x : Fin n → ℝ) :
    gaussianNoise ρ (gaussianNoise σ f) x = gaussianNoise (ρ * σ) f x := by
  have hprod : ρ * σ ∈ Set.Ioo (-1 : ℝ) 1 := by
    apply abs_lt.mp
    calc
      |ρ * σ| = |ρ| * |σ| := abs_mul _ _
      _ ≤ |ρ| * 1 :=
        mul_le_mul_of_nonneg_left (abs_lt.mpr hσ).le (abs_nonneg _)
      _ < 1 := by simpa only [mul_one] using abs_lt.mpr hρ
  have hinner : Integrable (gaussianNoise σ f) γ :=
    memLp_one_iff_integrable.mp (gaussianNoise_memLp
      ⟨hσ.1.le, hσ.2.le⟩ 1 le_rfl (memLp_one_iff_integrable.mpr hf))
  exact congrFun (Measure.eq_of_ae_eq
    (gaussianNoise_compose ⟨hρ.1.le, hρ.2.le⟩ ⟨hσ.1.le, hσ.2.le⟩ hf)
    (gaussianNoise_smooth hρ hinner).continuous
    (gaussianNoise_smooth hprod hf).continuous) x

/-- Gaussian noise distributes over subtraction of Gaussian integrable inputs.
[OD14, Def. 11.12] **Proof sketch.** Express subtraction as addition and scalar
multiplication, then use linearity of the Gaussian integral. -/
lemma gaussianNoise_sub {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) (hg : Integrable g γ) :
    gaussianNoise ρ (fun x => f x - g x) =
      fun x => gaussianNoise ρ f x - gaussianNoise ρ g x := by
  have heq : (fun x => f x - g x) = (fun x => f x + (-1) * g x) := by
    funext x
    ring
  rw [heq, gaussianNoise_add hρ hf (hg.const_mul (-1)), gaussianNoise_const_mul]
  funext x
  ring

/-- Gaussian noise commutes with division by a real constant.
[OD14, Def. 11.12] -/
lemma gaussianNoise_div_const (ρ c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    gaussianNoise ρ (fun x => f x / c) =
      fun x => gaussianNoise ρ f x / c := by
  simpa only [div_eq_mul_inv, mul_comm] using gaussianNoise_const_mul ρ c⁻¹ f

/-- A strong Gaussian L² generator limit gives the time derivative of its noise
orbit in L¹. [OD14, Prop. 11.27, strong-semigroup formulation]
**Proof sketch.** For positive increments commute the noise operator with the
original generator quotient. For negative increments use the preceding time
and control the extra generator term by strong continuity of noise in L¹.
Contraction bounds both errors by their corresponding errors at time zero. -/
lemma gaussianNoise_exp_tendsto_quotient_L1
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hlim : Tendsto (fun a : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-a)) f x) / a - g x) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun h : ℝ => eLpNorm
      (fun x => (gaussianNoise (Real.exp (-(s+h))) f x -
        gaussianNoise (Real.exp (-s)) f x) / h +
        gaussianNoise (Real.exp (-s)) g x) 1 γ)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let U (r : ℝ) := gaussianNoise (n := n) (Real.exp (-r))
  let q (a : ℝ) := fun x => (f x - U a f x) / a - g x
  have hc (r : ℝ) (hr : 0 ≤ r) : Real.exp (-r) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)⟩
  have hfi := hf.integrable (by norm_num)
  have hgi := hg.integrable (by norm_num)
  have hUm (r : ℝ) (hr : 0 ≤ r) {w : (Fin n → ℝ) → ℝ}
      (hw : MemLp w 2 γ) : MemLp (U r w) 2 γ :=
    gaussianNoise_memLp (hc r hr) 2 (by norm_num) hw
  have hqm (a : ℝ) (ha : 0 < a) : MemLp (q a) 2 γ := by
    convert ((hf.sub (hUm a ha.le hf)).const_smul a⁻¹).sub hg using 1
    ext x
    change (f x - U a f x) / a - g x = a⁻¹ * (f x - U a f x) - g x
    ring
  have hL1 : Tendsto (fun a => eLpNorm (q a) 1 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le _)
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      (hqm a ha).aestronglyMeasurable
  have hUs (r : ℝ) (hr : 0 ≤ r) {u v : (Fin n → ℝ) → ℝ}
      (hu : Integrable u γ) (hv : Integrable v γ) :
      U r (fun x => u x - v x) = fun x => U r u x - U r v x :=
    gaussianNoise_sub (hc r hr) hu hv
  have hUd (r : ℝ) (u : (Fin n → ℝ) → ℝ) (a : ℝ) :
      U r (fun x => u x / a) = fun x => U r u x / a :=
    gaussianNoise_div_const (Real.exp (-r)) a u
  have hUc (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a)
      {w : (Fin n → ℝ) → ℝ} (hw : Integrable w γ) :
      U r (U a w) =ᵐ[γ] U (r+a) w := by
    simpa only [U, neg_add, Real.exp_add] using
      gaussianNoise_compose (hc r hr) (hc a ha) hw
  have htransport (r a : ℝ) (hr : 0 ≤ r) (ha : 0 < a) :
      U r (q a) =ᵐ[γ]
        (fun x => (U r f x - U (r+a) f x) / a - U r g x) := by
    dsimp only [q]
    rw [hUs r hr
      (show Integrable (fun x => (f x - U a f x) / a) γ from
        (hfi.sub ((hUm a ha.le hf).integrable (by norm_num))).div_const a) hgi,
      hUd, hUs r hr hfi ((hUm a ha.le hf).integrable (by norm_num))]
    filter_upwards [hUc r a hr ha.le hfi] with x hx
    rw [hx]
  have hparam : Tendsto (fun a : ℝ => Real.exp (-a))
      (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((Real.continuous_exp.comp continuous_neg).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hC : Tendsto (fun a : ℝ => eLpNorm (fun x => U a g x - g x) 1 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (gaussianNoise_tendsto_one hgi).comp hparam
  have habs : Tendsto (fun h : ℝ => |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact abs_pos.mpr (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh)
  have hsum : Tendsto
      (fun h : ℝ => eLpNorm (q |h|) 1 γ +
        eLpNorm (fun x => U |h| g x - g x) 1 γ)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_add] using (hL1.comp habs).add (hC.comp habs)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le _)
  filter_upwards [
    (habs.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds hs),
    self_mem_nhdsWithin] with h hsmall hne
  have hne : h ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
  change eLpNorm (fun x => (U (s+h) f x - U s f x) / h + U s g x) 1 γ ≤ _
  by_cases hh : 0 < h
  · calc
      _ = eLpNorm (fun x => -(U s (q h) x)) 1 γ := by
        apply eLpNorm_congr_ae
        filter_upwards [htransport s h hs.le hh] with x hx
        rw [hx]
        ring
      _ = eLpNorm (U s (q h)) 1 γ := eLpNorm_neg _ _ _
      _ ≤ eLpNorm (q h) 1 γ :=
        gaussianNoise_contract (hc s hs.le) 1 le_rfl
          ((hqm h hh).mono_exponent (by norm_num))
      _ ≤ eLpNorm (q |h|) 1 γ + eLpNorm (fun x => U |h| g x - g x) 1 γ := by
        rw [abs_of_pos hh]
        exact le_add_of_nonneg_right (zero_le _)
  · have hn : h < 0 := lt_of_le_of_ne (le_of_not_gt hh) hne
    have ha : 0 < -h := neg_pos.mpr hn
    have hr : 0 < s+h := by
      have := (abs_lt.mp hsmall).1
      linarith
    have hcancel : s+h+(-h) = s := by ring
    have hcg := hUc (s+h) (-h) hr.le ha.le hgi
    have htr := htransport (s+h) (-h) hr.le ha
    rw [hcancel] at hcg htr
    have hv := (hUm (-h) ha.le hg).sub hg
    calc
      _ = eLpNorm (fun x => U (s+h) (fun y => U (-h) g y - g y) x -
          U (s+h) (q (-h)) x) 1 γ := by
        rw [hUs (s+h) hr.le ((hUm (-h) ha.le hg).integrable (by norm_num)) hgi]
        apply eLpNorm_congr_ae
        filter_upwards [hcg, htr] with x hx hy
        rw [hx, hy]
        simp only [div_neg]
        ring
      _ ≤ eLpNorm (U (s+h) (fun x => U (-h) g x - g x)) 1 γ +
          eLpNorm (U (s+h) (q (-h))) 1 γ :=
        eLpNorm_sub_le (hUm (s+h) hr.le hv).aestronglyMeasurable
          (hUm (s+h) hr.le (hqm (-h) ha)).aestronglyMeasurable le_rfl
      _ ≤ eLpNorm (fun x => U (-h) g x - g x) 1 γ + eLpNorm (q (-h)) 1 γ := by
        apply add_le_add
        · exact gaussianNoise_contract (hc (s+h) hr.le) 1 le_rfl
            (hv.mono_exponent (by norm_num))
        · exact gaussianNoise_contract (hc (s+h) hr.le) 1 le_rfl
            ((hqm (-h) ha).mono_exponent (by norm_num))
      _ = _ := by rw [abs_of_neg hn, add_comm]

/-- Fixed interior Gaussian averaging sends Gaussian L¹ convergence to zero
to pointwise convergence to zero. [OD14, §11.1, Gaussian noise kernel]
**Proof sketch.** Bound evaluation by a fixed finite multiple of the L¹
seminorm and apply the squeeze theorem. -/
lemma tendsto_gaussianNoise_apply_zero {ι : Type*} {l : Filter ι}
    {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (x : Fin n → ℝ)
    {F : ι → (Fin n → ℝ) → ℝ}
    (hF : ∀ᶠ i in l, Integrable (F i) γ)
    (hlim : Tendsto (fun i => eLpNorm (F i) 1 γ) l (𝓝 0)) :
    Tendsto (fun i => gaussianNoise ρ (F i) x) l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := enorm_gaussianNoise_apply_le hρ x
  have hmajor : Tendsto (fun i => C * eLpNorm (F i) 1 γ) l (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hC)
  have hnorm : Tendsto (fun i => ‖gaussianNoise ρ (F i) x‖ₑ) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajor (Eventually.of_forall fun _ => zero_le _) ?_
    filter_upwards [hF] with i hi
    exact hbound (F i) hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_apply, toReal_enorm, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hnorm

/-- A strong Gaussian L² generator limit differentiates the noise orbit at
every positive time and every starting point. [OD14, Prop. 11.27]
**Proof sketch.** Split the time into two equal positive pieces. The centered
quotient error at the first piece converges in L¹. Apply the fixed smoothing
operator for the second piece, whose evaluation is bounded on L¹, and use the
pointwise semigroup identity. -/
lemma hasDerivAt_gaussianNoise_exp_of_strong_limit
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hlim : Tendsto (fun b : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-b)) f x) / b - g x) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => gaussianNoise (Real.exp (-s)) f x)
      (-gaussianNoise (Real.exp (-t)) g x) t := (by
  let a := t / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have haa : a + a = t := by dsimp [a]; ring
  have hc (r : ℝ) (hr : 0 < r) : Real.exp (-r) ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) (Real.exp_pos _),
      Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hr)⟩
  have hi (r : ℝ) (hr : 0 < r) {w : (Fin n → ℝ) → ℝ}
      (hw : MemLp w 2 γ) : Integrable (gaussianNoise (Real.exp (-r)) w) γ :=
    (gaussianNoise_memLp ⟨(hc r hr).1.le, (hc r hr).2.le⟩
      2 (by norm_num) hw).integrable (by norm_num)
  let E (h : ℝ) := fun y =>
    (gaussianNoise (Real.exp (-(a+h))) f y -
      gaussianNoise (Real.exp (-a)) f y) / h +
      gaussianNoise (Real.exp (-a)) g y
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), 0 < a + h := by
    have hb : -a < (0 : ℝ) := by linarith
    filter_upwards [(eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds] with h hh
    linarith
  have hE : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ), Integrable (E h) γ := by
    filter_upwards [hsmall] with h hh
    exact (((hi (a+h) hh hf).sub (hi a ha hf)).div_const h).add (hi a ha hg)
  have hzero : Tendsto (fun h => gaussianNoise (Real.exp (-a)) (E h) x)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_gaussianNoise_apply_zero (hc a ha) x hE
      (gaussianNoise_exp_tendsto_quotient_L1 hf hg hlim a ha)
  have hcomp (r : ℝ) (hr : 0 < r) {w : (Fin n → ℝ) → ℝ}
      (hw : Integrable w γ) :
      gaussianNoise (Real.exp (-a)) (gaussianNoise (Real.exp (-r)) w) x =
        gaussianNoise (Real.exp (-(a+r))) w x := by
    simpa only [neg_add, Real.exp_add] using
      gaussianNoise_compose_apply (hc a ha) (hc r hr) hw x
  have heq : ∀ᶠ h : ℝ in 𝓝[≠] (0 : ℝ),
      gaussianNoise (Real.exp (-a)) (E h) x =
        (gaussianNoise (Real.exp (-(t+h))) f x -
          gaussianNoise (Real.exp (-t)) f x) / h +
          gaussianNoise (Real.exp (-t)) g x := by
    filter_upwards [hsmall] with h hh
    dsimp only [E]
    rw [gaussianNoise_add ⟨(hc a ha).1.le, (hc a ha).2.le⟩
      (show Integrable (fun y =>
        (gaussianNoise (Real.exp (-(a+h))) f y -
          gaussianNoise (Real.exp (-a)) f y) / h) γ from
        ((hi (a+h) hh hf).sub (hi a ha hf)).div_const h)
      (hi a ha hg),
      gaussianNoise_div_const,
      gaussianNoise_sub ⟨(hc a ha).1.le, (hc a ha).2.le⟩
        (hi (a+h) hh hf) (hi a ha hf)]
    change
      (gaussianNoise (Real.exp (-a))
          (gaussianNoise (Real.exp (-(a+h))) f) x -
        gaussianNoise (Real.exp (-a)) (gaussianNoise (Real.exp (-a)) f) x) / h +
        gaussianNoise (Real.exp (-a)) (gaussianNoise (Real.exp (-a)) g) x = _
    rw [hcomp (a+h) hh (hf.integrable (by norm_num)),
      hcomp a ha (hf.integrable (by norm_num)),
      hcomp a ha (hg.integrable (by norm_num)),
      show a + (a+h) = t+h by linarith, haa]
  have htarget := hzero.congr' heq
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [add_sub_cancel_right, zero_sub, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    htarget.sub_const (gaussianNoise (Real.exp (-t)) g x)
)

end BooleanAnalysis.GaussianSpace
