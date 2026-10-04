/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import TCSlib.CommunicationComplexity.NewmanTheorem.TVDistance
import Mathlib.Probability.Moments.SubGaussian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory
open ProbabilityTheory

open scoped ENNReal

/-!
# Pinsker's Inequality

Pinsker's inequality `2 · TV(μ, ν)² ≤ KL(μ ‖ ν)` for probability measures on an arbitrary
measurable space, with Mathlib's natural-logarithm `InformationTheory.klDiv` and the total
variation distance `tvDistance` of
`TCSlib.CommunicationComplexity.NewmanTheorem.TVDistance`.

The proof does not follow the textbook reduction to the two-point case. Instead it works with
the density `f = dμ/dν`: the total variation distance is `½ ∫ |f − 1| dν`, and the bound
`½ (∫ |f − 1| dν)² ≤ ∫ (f log f − f + 1) dν = KL(μ ‖ ν)` is obtained from a variational
inequality (`t ∫ f X ≤ ∫ klFun f + cgf_X(t)`, from the pointwise bound
`u y ≤ klFun u + eʸ − 1`) applied to the centred sign variable `X = sign(f − 1) − E[sign(f − 1)]`,
whose cumulant generating function is bounded by `t²/2` by Hoeffding's lemma (Mathlib's
sub-Gaussian API). All the intermediate lemmas are private.

## Main definitions

None.

## Main results

- `pinsker_inequality`: Pinsker's inequality in ENNReal form: `2 * TV(μ, ν)^2 ≤ KL(μ ‖ ν)`
- `two_mul_tvDistance_sq_le_toReal_klDiv`: real-valued corollary when KL divergence is finite

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [CT06] T. M. Cover, J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  Wiley, 2006.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

/-- The real-valued Radon-Nikodym density `dμ/dν` (as a real number, via `toReal`) used in the
absolutely-continuous part of Pinsker. -/
private noncomputable def rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Ω) : ℝ :=
  ((μ.rnDeriv ν x).toReal)

/-- The density `dμ/dν` is pointwise nonnegative. -/
private theorem rnDensity_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Ω) :
    0 ≤ rnDensity μ ν x :=
  ENNReal.toReal_nonneg

/-- The density `dμ/dν` is measurable. -/
private theorem measurable_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measurable (rnDensity μ ν) := by
  unfold rnDensity
  fun_prop

/-- The density `dμ/dν` is `ν`-integrable. -/
private theorem integrable_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (rnDensity μ ν) ν := by
  simpa [rnDensity] using
    (Measure.integrable_toReal_rnDeriv
      (μ := μ) (ν := ν))

/-- If `μ ≪ ν` then the density `dμ/dν` integrates to `1` against `ν` (both are probability
measures). -/
private theorem integral_rnDensity_eq_one_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ∫ x, rnDensity μ ν x ∂ν = 1 := by
  have h := Measure.integral_toReal_rnDeriv h_ac
  simpa [rnDensity] using h

/-- The centred density `dμ/dν − 1` is `ν`-integrable. -/
private theorem integrable_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun x => rnDensity μ ν x - 1) ν :=
  (integrable_rnDensity μ ν).sub (integrable_const 1)

/-- The absolute centred density `|dμ/dν − 1|` is `ν`-integrable. -/
private theorem integrable_abs_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun x => |rnDensity μ ν x - 1|) ν :=
  (integrable_rnDensity_sub_one μ ν).abs

/-- If `μ ≪ ν` then the centred density `dμ/dν − 1` has `ν`-mean zero. -/
private theorem integral_rnDensity_sub_one_eq_zero_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ∫ x, rnDensity μ ν x - 1 ∂ν = 0 := by
  rw [integral_sub (integrable_rnDensity μ ν) (integrable_const 1),
    integral_rnDensity_eq_one_of_ac μ ν h_ac]
  simp

/-- If `μ ≪ ν` then for every set `S`, `μ(S) − ν(S) = ∫_S (dμ/dν − 1) dν`. -/
private theorem measureReal_sub_eq_setIntegral_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) (S : Set Ω) :
    μ.real S - ν.real S =
      ∫ x in S, (rnDensity μ ν x - 1) ∂ν := by
  have h_rn_int :
      Integrable (rnDensity μ ν) (ν.restrict S) :=
    (integrable_rnDensity μ ν).mono_measure Measure.restrict_le_self
  have h_one_int :
      Integrable (fun _ : Ω => (1 : ℝ)) (ν.restrict S) :=
    integrable_const 1
  rw [integral_sub h_rn_int h_one_int]
  rw [← Measure.setIntegral_toReal_rnDeriv h_ac S, setIntegral_one_eq_measureReal]
  rfl

/-- For an integrable function `g` with mean zero, the integral of `g` over its nonnegative
set `{g ≥ 0}` equals half the integral of `|g|`.

**Proof sketch.** Split the integrals over `A = {g ≥ 0}` and its complement. Mean zero gives
`∫_A g + ∫_{Aᶜ} g = 0`; on `A` we have `|g| = g` and on `Aᶜ` we have `|g| = −g`, so
`∫ |g| = ∫_A g − ∫_{Aᶜ} g = 2 ∫_A g`. -/
private theorem integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ)
    (h_mean : ∫ x, g x ∂μ = 0) :
    ∫ x in {x | 0 ≤ g x}, g x ∂μ = (1 / 2 : ℝ) * ∫ x, |g x| ∂μ := by
  let A : Set Ω := {x | 0 ≤ g x}
  have hA : MeasurableSet A := measurableSet_Ici.preimage hg_meas
  have hmean_decomp :
      ∫ x in A, g x ∂μ + ∫ x in Aᶜ, g x ∂μ = 0 := by
    rw [integral_add_compl hA hg, h_mean]
  have h_abs_A :
      ∫ x in A, |g x| ∂μ = ∫ x in A, g x ∂μ := by
    apply setIntegral_congr_fun hA
    intro x hx
    exact abs_of_nonneg hx
  have h_abs_Ac :
      ∫ x in Aᶜ, |g x| ∂μ = -∫ x in Aᶜ, g x ∂μ := by
    calc
      ∫ x in Aᶜ, |g x| ∂μ = ∫ x in Aᶜ, -g x ∂μ := by
        apply setIntegral_congr_fun hA.compl
        intro x hx
        exact abs_of_nonpos (le_of_not_ge hx)
      _ = -∫ x in Aᶜ, g x ∂μ := by
        rw [integral_neg]
  have h_abs_decomp :
      ∫ x, |g x| ∂μ = ∫ x in A, g x ∂μ - ∫ x in Aᶜ, g x ∂μ := by
    rw [← integral_add_compl hA hg.abs, h_abs_A, h_abs_Ac]
    ring
  rw [h_abs_decomp]
  linarith

/-- For an integrable function `g` with mean zero, the supremum over measurable sets `S` of
`|∫_S g|` is attained at `S = {g ≥ 0}` and equals `∫_{g ≥ 0} g`.

**Proof sketch.** Write `pos = ∫_{g ≥ 0} g ≥ 0`.
Step 1: for every measurable `S`, both `∫_S g ≤ pos` and `∫_{Sᶜ} g ≤ pos` (dropping the
negative part of `g` only increases a set integral), and `∫_{Sᶜ} g = −∫_S g` by mean zero; so
`|∫_S g| ≤ pos`.
Step 2: hence the supremum is at most `pos`.
Step 3: the set `{g ≥ 0}` itself achieves the value `pos`, so the supremum is at least `pos`. -/
private theorem sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ)
    (h_mean : ∫ x, g x ∂μ = 0) :
    sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
      |∫ x in (S : Set Ω), g x ∂μ|) =
      ∫ x in {x | 0 ≤ g x}, g x ∂μ := by
  let A : Set Ω := {x | 0 ≤ g x}
  let pos : ℝ := ∫ x in A, g x ∂μ
  have hA : MeasurableSet A := measurableSet_Ici.preimage hg_meas
  have hpos_nonneg : 0 ≤ pos := by
    dsimp [pos, A]
    exact setIntegral_nonneg hA fun x hx => hx
  -- Step 1: every set integral is bounded in absolute value by the positive part
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |∫ x in (S : Set Ω), g x ∂μ| ≤ pos := by
    have hupper : ∫ x in (S : Set Ω), g x ∂μ ≤ pos := by
      simpa [pos, A] using
        setIntegral_le_nonneg (S.property) hg_meas.stronglyMeasurable hg
    have hcompl_upper : ∫ x in ((S : Set Ω)ᶜ), g x ∂μ ≤ pos := by
      simpa [pos, A] using
        setIntegral_le_nonneg (S.property.compl) hg_meas.stronglyMeasurable hg
    have hcompl_eq_neg :
        ∫ x in ((S : Set Ω)ᶜ), g x ∂μ = -∫ x in (S : Set Ω), g x ∂μ := by
      have hdecomp := integral_add_compl S.property hg
      rw [h_mean] at hdecomp
      linarith
    rw [abs_le]
    constructor
    · linarith
    · exact hupper
  -- Step 2: the supremum is at most the positive part
  have hupper_sSup :
      sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) ≤ pos := by
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hpos_nonneg
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) :=
    ⟨pos, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  -- Step 3: the set `{g ≥ 0}` attains the positive part
  have hlower_sSup :
      pos ≤ sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) := by
    let Aset : {S : Set Ω // MeasurableSet S} := ⟨A, hA⟩
    have hA_value :
        |∫ x in (Aset : Set Ω), g x ∂μ| = pos := by
      dsimp [Aset, pos]
      rw [abs_of_nonneg hpos_nonneg]
    rw [← hA_value]
    exact le_csSup hbdd (Set.mem_range_self Aset)
  exact le_antisymm hupper_sSup hlower_sSup

/-- The `L¹` distance `∫ |dμ/dν − 1| dν` between the density and the constant `1`. -/
private noncomputable def densityAbsIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  ∫ x, |rnDensity μ ν x - 1| ∂ν

/-- The set `{dμ/dν ≥ 1}` on which `μ` has at least as much density as `ν`. -/
private def densityPositiveSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Set Ω :=
  {x | 1 ≤ rnDensity μ ν x}

/-- The set `{dμ/dν ≥ 1}` is measurable. -/
private theorem measurableSet_densityPositiveSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurableSet (densityPositiveSet μ ν) := by
  exact measurableSet_Ici.preimage (measurable_rnDensity μ ν)

/-- The positive part `∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν` of the centred density. -/
private noncomputable def densityPositiveIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  ∫ x in densityPositiveSet μ ν, (rnDensity μ ν x - 1) ∂ν

/-- If `μ ≪ ν`, the supremum form of the total variation distance equals the positive part
`∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν` of the centred density.

**Proof sketch.** By `measureReal_sub_eq_setIntegral_rnDensity_sub_one` the family of values
`|μ(S) − ν(S)|` over measurable `S` coincides with the family `|∫_S (dμ/dν − 1) dν|`; since the
centred density is integrable with mean zero, the supremum of the latter is its positive part
(`sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero`). -/
private theorem tvDistanceSup_eq_densityPositiveIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistanceSup μ ν = densityPositiveIntegral μ ν := by
  rw [tvDistanceSup]
  have h_range :
      (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|) =
      (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), (rnDensity μ ν x - 1) ∂ν|) := by
    ext r
    constructor
    · rintro ⟨S, rfl⟩
      refine ⟨S, ?_⟩
      change |∫ x in (S : Set Ω), (rnDensity μ ν x - 1) ∂ν| =
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|
      rw [← measureReal_sub_eq_setIntegral_rnDensity_sub_one μ ν h_ac (S : Set Ω)]
    · rintro ⟨S, rfl⟩
      refine ⟨S, ?_⟩
      change |μ.real (S : Set Ω) - ν.real (S : Set Ω)| =
        |∫ x in (S : Set Ω), (rnDensity μ ν x - 1) ∂ν|
      rw [measureReal_sub_eq_setIntegral_rnDensity_sub_one μ ν h_ac (S : Set Ω)]
  rw [h_range]
  have hsup :=
    sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero
      (μ := ν) (g := fun x => rnDensity μ ν x - 1)
      ((measurable_rnDensity μ ν).sub measurable_const)
      (integrable_rnDensity_sub_one μ ν)
      (integral_rnDensity_sub_one_eq_zero_of_ac μ ν h_ac)
  simpa [densityPositiveIntegral, densityPositiveSet, sub_nonneg] using hsup

/-- If `μ ≪ ν`, the total variation distance equals the positive part
`∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν` of the centred density. -/
private theorem tvDistance_eq_densityPositiveIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistance μ ν = densityPositiveIntegral μ ν := by
  rw [TVDistance.tvDistance_eq_tvDistanceSup,
    tvDistanceSup_eq_densityPositiveIntegral_of_ac μ ν h_ac]

/-- If `μ ≪ ν`, the positive part of the centred density is half its `L¹` norm:
`∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν = ½ ∫ |dμ/dν − 1| dν`. -/
private theorem densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    densityPositiveIntegral μ ν = (1 / 2 : ℝ) * densityAbsIntegral μ ν := by
  have h :=
    integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero
      (μ := ν) (g := fun x => rnDensity μ ν x - 1)
      ((measurable_rnDensity μ ν).sub measurable_const)
      (integrable_rnDensity_sub_one μ ν)
      (integral_rnDensity_sub_one_eq_zero_of_ac μ ν h_ac)
  simpa [densityPositiveIntegral, densityAbsIntegral, densityPositiveSet, sub_nonneg] using h

/-- The pointwise Fenchel–Young-type inequality `u · y ≤ klFun u + exp y − 1` for `u ≥ 0`, where
`klFun u = u log u − u + 1` is the integrand of the KL divergence; it follows from
`log z ≤ z − 1` applied to `z = exp y / u`. -/
private theorem mul_le_klFun_add_exp_sub_one {u y : ℝ} (hu : 0 ≤ u) :
    u * y ≤ InformationTheory.klFun u + Real.exp y - 1 := by
  rcases hu.eq_or_lt with rfl | hu_pos
  · simp [InformationTheory.klFun, (Real.exp_pos y).le]
  · have hlog :=
      Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos y) hu_pos)
    rw [Real.log_div (Real.exp_pos y).ne' hu_pos.ne', Real.log_exp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hu
    have hmul' : u * (y - Real.log u) ≤ Real.exp y - u := by
      calc
        u * (y - Real.log u) ≤ u * (Real.exp y / u - 1) := hmul
        _ = Real.exp y - u := by field_simp [hu_pos.ne']
    rw [InformationTheory.klFun]
    nlinarith

/-- Function-level rewrite shared by `integral_exp_sub_cgf_eq_one` and `integrable_exp_sub_cgf`:
`exp (t X - cgf X μ t)` is the constant `exp (-cgf X μ t)` times `exp (t X)`. -/
private theorem exp_sub_cgf_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) =
      fun x => (Real.exp (-ProbabilityTheory.cgf X μ t)) * Real.exp (t * X x) := by
  ext x
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- The exponentially tilted density `exp (t X − cgf_X(t))` integrates to `1` whenever
`exp (t X)` is integrable. -/
private theorem integral_exp_sub_cgf_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {t : ℝ} (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ) :
    ∫ x, Real.exp (t * X x - ProbabilityTheory.cgf X μ t) ∂μ = 1 := by
  rw [exp_sub_cgf_eq, integral_const_mul]
  change Real.exp (-ProbabilityTheory.cgf X μ t) * ProbabilityTheory.mgf X μ t = 1
  rw [← ProbabilityTheory.exp_cgf h_exp_int]
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]

/-- The exponentially tilted density `exp (t X − cgf_X(t))` is integrable whenever `exp (t X)`
is. -/
private theorem integrable_exp_sub_cgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {t : ℝ} (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ) :
    Integrable (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) μ := by
  rw [exp_sub_cgf_eq]
  exact h_exp_int.const_mul _

/-- Variational (Donsker–Varadhan-type) inequality: for a nonnegative density `f` with
`∫ f dμ = 1` and any `X` with `exp (t X)` integrable,
`t ∫ f X dμ ≤ ∫ klFun (f) dμ + cgf_X(t)`.

**Proof sketch.** Write `c = cgf_X(t)`.
Step 1: the pointwise bound `mul_le_klFun_add_exp_sub_one` with `u = f x`, `y = t X x − c` gives
`f · (t X − c) ≤ klFun f + exp (t X − c) − 1`, and both sides are integrable; integrate.
Step 2: the left integral is `t ∫ f X − c ∫ f = t ∫ f X − c`.
Step 3: the right integral is `∫ klFun f + ∫ exp (t X − c) − 1 = ∫ klFun f`, since the tilted
density integrates to `1`. Rearranging gives the claim. -/
private theorem variational_integral_mul_le_integral_klFun_add_cgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f X : Ω → ℝ} {t : ℝ}
    (hf_int : Integrable f μ)
    (h_kl_int : Integrable (fun x => InformationTheory.klFun (f x)) μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (h_integral : ∫ x, f x ∂μ = 1)
    (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ)
    (hfX_int : Integrable (fun x => f x * X x) μ) :
    t * ∫ x, f x * X x ∂μ ≤
      ∫ x, InformationTheory.klFun (f x) ∂μ + ProbabilityTheory.cgf X μ t := by
  let c := ProbabilityTheory.cgf X μ t
  -- Step 1: integrate the pointwise inequality
  have h_left_int :
      Integrable (fun x => f x * (t * X x - c)) μ := by
    have h1 : Integrable (fun x => t * (f x * X x)) μ := hfX_int.const_mul t
    have h2 : Integrable (fun x => c * f x) μ := hf_int.const_mul c
    simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using h1.sub h2
  have h_right_int :
      Integrable (fun x =>
        InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1) μ :=
    (h_kl_int.add (integrable_exp_sub_cgf h_exp_int)).sub (integrable_const 1)
  have h_pointwise :
      (fun x => f x * (t * X x - c)) ≤
      fun x => InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 := by
    intro x
    exact mul_le_klFun_add_exp_sub_one (hf_nonneg x)
  have h_integral_le :
      ∫ x, f x * (t * X x - c) ∂μ ≤
      ∫ x, InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 ∂μ :=
    integral_mono h_left_int h_right_int h_pointwise
  -- Step 2: evaluate the left integral using `∫ f = 1`
  have h_left_eq :
      ∫ x, f x * (t * X x - c) ∂μ =
        t * ∫ x, f x * X x ∂μ - c := by
    calc
      ∫ x, f x * (t * X x - c) ∂μ =
          ∫ x, t * (f x * X x) - c * f x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = t * ∫ x, f x * X x ∂μ - c * ∫ x, f x ∂μ := by
        rw [integral_sub (hfX_int.const_mul t) (hf_int.const_mul c),
          integral_const_mul, integral_const_mul]
      _ = t * ∫ x, f x * X x ∂μ - c := by rw [h_integral, mul_one]
  -- Step 3: the tilted density integrates to `1`, so the right integral is `∫ klFun f`
  have h_right_eq :
      ∫ x, InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 ∂μ =
        ∫ x, InformationTheory.klFun (f x) ∂μ := by
    have h_exp_sub_int :
        Integrable (fun x => Real.exp (t * X x - c)) μ := by
      simpa [c] using integrable_exp_sub_cgf (μ := μ) (X := X) (t := t) h_exp_int
    have h_exp_sub_eq_one :
        ∫ x, Real.exp (t * X x - c) ∂μ = 1 := by
      simpa [c] using integral_exp_sub_cgf_eq_one (μ := μ) (X := X) (t := t) h_exp_int
    calc
      ∫ x, InformationTheory.klFun (f x) + Real.exp (t * X x - c) - 1 ∂μ =
          (∫ x, InformationTheory.klFun (f x) ∂μ) +
            ∫ x, Real.exp (t * X x - c) ∂μ - ∫ _x : Ω, (1 : ℝ) ∂μ := by
        have hsub :=
          integral_sub (h_kl_int.add h_exp_sub_int) (integrable_const (1 : ℝ))
        have hadd := integral_add h_kl_int h_exp_sub_int
        have hadd' :
            ∫ a, ((fun x => InformationTheory.klFun (f x)) +
                fun x => Real.exp (t * X x - c)) a ∂μ =
              ∫ a, InformationTheory.klFun (f a) ∂μ +
                ∫ a, Real.exp (t * X a - c) ∂μ := by
          simpa [Pi.add_apply] using hadd
        rw [hadd'] at hsub
        simpa [Pi.add_apply, Pi.sub_apply] using hsub
      _ = ∫ x, InformationTheory.klFun (f x) ∂μ := by
        rw [h_exp_sub_eq_one, integral_const, measureReal_univ_eq_one]
        simp
  rw [h_left_eq, h_right_eq] at h_integral_le
  linarith

/-- The density form of Pinsker's inequality: for a measurable nonnegative density `f` with
`∫ f dμ = 1` and `klFun ∘ f` integrable, `½ (∫ |f − 1| dμ)² ≤ ∫ klFun (f) dμ`.

**Proof sketch.** Let `s = sign (f − 1)` (with value `1` where `f ≥ 1`), `m = ∫ s dμ`,
`X = s − m` and `L = ∫ |f − 1| dμ`.
Step 1: `X` is measurable, centred, and takes values in the interval `[−1 − m, 1 − m]` of
length `2`, so by Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) it is
sub-Gaussian and `cgf_X(t) ≤ t²/2`; in particular `exp (t X)` is integrable.
Step 2: `∫ f X dμ = L`: since `|f − 1| = (f − 1) s` pointwise, `∫ f X = ∫ (f − 1) s + ∫ s −
m ∫ (f − 1) − m = L + m − 0 − m`.
Step 3: apply the variational inequality
`variational_integral_mul_le_integral_klFun_add_cgf` with `t = L` to get
`L² ≤ ∫ klFun f + cgf_X(L) ≤ ∫ klFun f + L²/2`, and rearrange. -/
private theorem half_integral_abs_sub_one_sq_le_integral_klFun
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (h_kl_int : Integrable (fun x => InformationTheory.klFun (f x)) μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (h_integral : ∫ x, f x ∂μ = 1) :
    (1 / 2 : ℝ) * (∫ x, |f x - 1| ∂μ) ^ 2 ≤
      ∫ x, InformationTheory.klFun (f x) ∂μ := by
  let s : Ω → ℝ := fun x => if 0 ≤ f x - 1 then 1 else -1
  let m : ℝ := ∫ x, s x ∂μ
  let X : Ω → ℝ := fun x => s x - m
  let L : ℝ := ∫ x, |f x - 1| ∂μ
  -- Step 1: the centred sign variable `X` is bounded and centred, hence sub-Gaussian
  have hset : MeasurableSet {x | 0 ≤ f x - 1} :=
    measurableSet_Ici.preimage (hf_meas.sub measurable_const)
  have hs_meas : Measurable s := by
    dsimp [s]
    exact Measurable.ite hset measurable_const measurable_const
  have hs_bound : ∀ᵐ x ∂μ, s x ∈ Set.Icc (-1 : ℝ) 1 := by
    refine ae_of_all μ ?_
    intro x
    by_cases hx : 1 ≤ f x <;> simp [s, sub_nonneg, hx]
  have hs_int : Integrable s μ :=
    Integrable.of_mem_Icc (-1 : ℝ) 1 hs_meas.aemeasurable hs_bound
  have hX_meas : Measurable X := hs_meas.sub measurable_const
  have hX_integral_zero : μ[X] = 0 := by
    dsimp [X, m]
    rw [integral_sub hs_int (integrable_const _), integral_const, measureReal_univ_eq_one]
    simp
  have hX_mem_Icc :
      ∀ᵐ x ∂μ, X x ∈ Set.Icc ((-1 : ℝ) - m) (1 - m) := by
    refine ae_of_all μ ?_
    intro x
    by_cases hx : 1 ≤ f x
    · simp [X, s, sub_nonneg, hx]
    · simp [X, s, sub_nonneg, hx]
  have hX_subG :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := μ) (X := X) (a := (-1 : ℝ) - m) (b := 1 - m)
      hX_meas.aemeasurable hX_mem_Icc hX_integral_zero
  have hX_norm_bound : ∀ᵐ x ∂μ, ‖X x‖ ≤ |m| + 1 := by
    refine ae_of_all μ ?_
    intro x
    have hs_abs : |s x| ≤ (1 : ℝ) := by
      by_cases hx : 1 ≤ f x <;> simp [s, sub_nonneg, hx]
    calc
      ‖X x‖ = |s x - m| := rfl
      _ ≤ |s x| + |m| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (s x) (-m)
      _ ≤ |m| + 1 := by linarith
  have hfX_int : Integrable (fun x => f x * X x) μ :=
    (hf_int.bdd_mul' hX_meas.aestronglyMeasurable hX_norm_bound).congr
      (Filter.Eventually.of_forall (fun x => mul_comm (X x) (f x)))
  -- Step 2: `∫ f X = L`, the `L¹` distance of `f` from `1`
  have h_abs_int : Integrable (fun x => |f x - 1|) μ :=
    (hf_int.sub (integrable_const 1)).abs
  have h_sub_integral_zero : ∫ x, f x - 1 ∂μ = 0 := by
    rw [integral_sub hf_int (integrable_const 1), h_integral, integral_const, measureReal_univ_eq_one]
    simp
  have h_abs_eq_signed : L = ∫ x, (f x - 1) * s x ∂μ := by
    dsimp [L, s]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 ≤ f x - 1
    · simp [hx, abs_of_nonneg hx]
    · have hx' : f x - 1 ≤ 0 := le_of_not_ge hx
      simp [hx, abs_of_nonpos hx']
  have h_signed_int : Integrable (fun x => (f x - 1) * s x) μ := by
    have hs_norm_bound : ∀ᵐ x ∂μ, ‖s x‖ ≤ (1 : ℝ) := by
      filter_upwards [hs_bound] with x hx
      rw [Real.norm_eq_abs]
      exact abs_le.2 hx
    exact ((hf_int.sub (integrable_const 1)).bdd_mul' hs_meas.aestronglyMeasurable hs_norm_bound).congr
      (Filter.Eventually.of_forall (fun x => mul_comm (s x) (f x - 1)))
  have h_signed_integral_zero :
      ∫ x, (f x - 1) * m ∂μ = 0 := by
    rw [integral_mul_const, h_sub_integral_zero, zero_mul]
  have h_fX_eq_L : ∫ x, f x * X x ∂μ = L := by
    calc
      ∫ x, f x * X x ∂μ =
          ∫ x, (f x - 1) * s x + s x - (f x - 1) * m - m ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [X]
        ring
      _ = ∫ x, (f x - 1) * s x ∂μ + ∫ x, s x ∂μ -
          ∫ x, (f x - 1) * m ∂μ - ∫ _x : Ω, m ∂μ := by
        rw [integral_sub, integral_sub, integral_add]
        · exact h_signed_int
        · exact hs_int
        · exact h_signed_int.add hs_int
        · exact (hf_int.sub (integrable_const 1)).mul_const m
        · exact (h_signed_int.add hs_int).sub ((hf_int.sub (integrable_const 1)).mul_const m)
        · exact integrable_const m
      _ = L := by
        rw [← h_abs_eq_signed, h_signed_integral_zero, integral_const, measureReal_univ_eq_one]
        simp [m]
  -- Step 3: Hoeffding bound on the cgf and the variational inequality at `t = L`
  have h_cgf :
      ProbabilityTheory.cgf X μ L ≤ L ^ 2 / 2 := by
    have h := hX_subG.cgf_le L
    norm_num [Real.norm_eq_abs] at h
    simpa using h
  have h_var :=
    variational_integral_mul_le_integral_klFun_add_cgf
      (μ := μ) (f := f) (X := X) (t := L)
      hf_int h_kl_int hf_nonneg h_integral (hX_subG.integrable_exp_mul L) hfX_int
  have h_var' :
      L ^ 2 ≤ ∫ x, InformationTheory.klFun (f x) ∂μ + ProbabilityTheory.cgf X μ L := by
    rw [h_fX_eq_L] at h_var
    simpa [sq] using h_var
  nlinarith

/-- If `μ ≪ ν`, the total variation distance is half the `L¹` distance of the density from `1`:
`TV(μ, ν) = ½ ∫ |dμ/dν − 1| dν`. -/
private theorem tvDistance_eq_half_densityAbsIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistance μ ν = (1 / 2 : ℝ) * densityAbsIntegral μ ν := by
  rw [tvDistance_eq_densityPositiveIntegral_of_ac μ ν h_ac,
    densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac μ ν h_ac]

/-- If `μ ≪ ν` and the log-likelihood ratio is `μ`-integrable, then
`½ (∫ |dμ/dν − 1| dν)² ≤ ∫ klFun (dμ/dν) dν`; this is
`half_integral_abs_sub_one_sq_le_integral_klFun` applied to the density `dμ/dν`. -/
private theorem half_densityAbsIntegral_sq_le_integral_klFun_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2 ≤
      ∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν := by
  have h_kl_int :
      Integrable (fun x => InformationTheory.klFun (rnDensity μ ν x)) ν := by
    simpa [rnDensity] using
      (InformationTheory.integrable_klFun_rnDeriv_iff
        (μ := μ) (ν := ν) h_ac).2 h_int
  simpa [densityAbsIntegral] using
    half_integral_abs_sub_one_sq_le_integral_klFun
      (μ := ν) (f := rnDensity μ ν)
      (measurable_rnDensity μ ν) (integrable_rnDensity μ ν) h_kl_int
      (rnDensity_nonneg μ ν) (integral_rnDensity_eq_one_of_ac μ ν h_ac)

/-- If `μ ≪ ν` and the log-likelihood ratio is `μ`-integrable, then
`∫ klFun (dμ/dν) dν = ∫ llr μ ν dμ`, the real-valued KL divergence (Mathlib's
`integral_klFun_rnDeriv`). -/
private theorem integral_klFun_rnDeriv_eq_kl_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν) =
      ∫ x, llr μ ν x ∂μ := by
  have h := InformationTheory.integral_klFun_rnDeriv h_ac h_int
  simpa [rnDensity] using h

/-- If `μ ≪ ν` and the log-likelihood ratio is `μ`-integrable, then
`½ (∫ |dμ/dν − 1| dν)² ≤ ∫ llr μ ν dμ`. -/
private theorem density_l1_pinsker_le_kl_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2 ≤
      ∫ x, llr μ ν x ∂μ := by
  calc
    (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2
        ≤ ∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν :=
      half_densityAbsIntegral_sq_le_integral_klFun_rnDensity μ ν h_ac h_int
    _ = ∫ x, llr μ ν x ∂μ :=
      integral_klFun_rnDeriv_eq_kl_integral μ ν h_ac h_int

/-- Real-valued Pinsker inequality under `μ ≪ ν` and integrability of the log-likelihood ratio:
`2 · TV(μ, ν)² ≤ ∫ llr μ ν dμ`. -/
private theorem real_pinsker_inequality_of_ac_of_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    2 * tvDistance μ ν ^ 2 ≤
      ∫ x, llr μ ν x ∂μ := by
  have h_tv := tvDistance_eq_half_densityAbsIntegral_of_ac μ ν h_ac
  have h_l1 := density_l1_pinsker_le_kl_integral μ ν h_ac h_int
  calc
    2 * tvDistance μ ν ^ 2 = (1 / 2 : ℝ) * densityAbsIntegral μ ν ^ 2 := by
      rw [h_tv]
      ring
    _ ≤ ∫ x, llr μ ν x ∂μ := h_l1

/-- Pinsker's inequality in `ℝ≥0∞` form under `μ ≪ ν` and integrability of the log-likelihood
ratio: `2 · TV(μ, ν)² ≤ KL(μ ‖ ν)`. -/
private theorem pinsker_inequality_of_ac_of_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  rw [InformationTheory.klDiv_of_ac_of_integrable h_ac h_int]
  apply ENNReal.ofReal_le_ofReal
  have h_real := real_pinsker_inequality_of_ac_of_integrable μ ν h_ac h_int
  simpa using h_real

/-- Pinsker's inequality in `ℝ≥0∞` form under `μ ≪ ν`: `2 · TV(μ, ν)² ≤ KL(μ ‖ ν)`; when the
log-likelihood ratio is not integrable the divergence is `∞`. -/
private theorem pinsker_inequality_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  by_cases h_int : Integrable (llr μ ν) μ
  · exact pinsker_inequality_of_ac_of_integrable μ ν h_ac h_int
  · rw [InformationTheory.klDiv_of_not_integrable h_int]
    exact le_top

/-- Pinsker's inequality: for probability measures `μ`, `ν` on any measurable space,
`2 · TV(μ, ν)² ≤ KL(μ ‖ ν)`, stated in `ℝ≥0∞` with Mathlib's KL divergence.
[RY20, Lemma 6.6] (Pinsker's inequality). Deviation: RY state `D(p‖q) ≥ (2 / ln 2) |p − q|²`
with the divergence in bits; here the divergence uses the natural logarithm, so the constant
is `2`, the inequality lives in `ℝ≥0∞` (it is trivial when the divergence is infinite), and the
measures are arbitrary probability measures rather than distributions on a finite set. The
proof route also differs from RY's reduction to the two-point case via the chain rule; see
below.

**Proof sketch.** The body only dispatches the degenerate cases; the argument lives in the
private lemmas of this file.
Step 1 (reductions): if `μ` is not absolutely continuous with respect to `ν`, or the
log-likelihood ratio is not `μ`-integrable, the divergence is `∞` and there is nothing to
prove (`pinsker_inequality_of_ac`, `pinsker_inequality_of_ac_of_integrable`).
Step 2 (total variation as an `L¹` norm): with `f = dμ/dν`, the supremum form of the total
variation distance is `sup_S |∫_S (f − 1) dν|`, which for a mean-zero integrand is its positive
part `∫_{f ≥ 1} (f − 1) dν`, and that is `½ ∫ |f − 1| dν`
(`tvDistanceSup_eq_densityPositiveIntegral_of_ac`,
`densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac`).
Step 3 (sub-Gaussian bound): let `s = sign (f − 1)`, `X = s − E[s]` and `L = ∫ |f − 1| dν`.
Then `X` is centred with values in an interval of length `2`, so by Hoeffding's lemma
`cgf_X(t) ≤ t²/2`; moreover `∫ f X dν = L`.
Step 4 (variational bound): from the pointwise inequality `u y ≤ klFun u + eʸ − 1` one gets
`t ∫ f X dν ≤ ∫ klFun (f) dν + cgf_X(t)` for every `t`
(`variational_integral_mul_le_integral_klFun_add_cgf`); taking `t = L` and using Step 3 gives
`½ L² ≤ ∫ klFun (f) dν` (`half_integral_abs_sub_one_sq_le_integral_klFun`).
Step 5 (identify the divergence): `∫ klFun (f) dν = ∫ llr μ ν dμ = KL(μ ‖ ν)` by Mathlib's
`integral_klFun_rnDeriv`; combining with Step 2, `2 · TV² = ½ L² ≤ KL(μ ‖ ν)`. -/
theorem pinsker_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  by_cases h_ac : μ ≪ ν
  · exact pinsker_inequality_of_ac μ ν h_ac
  · rw [InformationTheory.klDiv_of_not_ac h_ac]
    exact le_top

/-- Real-valued Pinsker inequality: if `KL(μ ‖ ν)` is finite then
`2 · TV(μ, ν)² ≤ KL(μ ‖ ν)` as real numbers. [RY20, Lemma 6.6] (Pinsker's inequality);
deviation: natural logarithm (constant `2` instead of `2 / ln 2`) and the finiteness hypothesis
replaces the `ℝ≥0∞` formulation of `pinsker_inequality`, from which it follows. -/
theorem two_mul_tvDistance_sq_le_toReal_klDiv
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : InformationTheory.klDiv μ ν ≠ ∞) :
    2 * tvDistance μ ν ^ 2 ≤
      (InformationTheory.klDiv μ ν).toReal := by
  have h :=
    ENNReal.toReal_mono hkl (pinsker_inequality μ ν)
  have hsq_nonneg : 0 ≤ tvDistance μ ν ^ 2 := sq_nonneg (tvDistance μ ν)
  simpa [ENNReal.toReal_ofReal hsq_nonneg] using h

end CommunicationComplexity
