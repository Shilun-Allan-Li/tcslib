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

## Main results

- `pinsker_inequality`: Pinsker's inequality in ENNReal form: `2 * TV(μ, ν)^2 ≤ KL(μ ‖ ν)`
- `two_mul_tvDistance_sq_le_toReal_klDiv`: real-valued corollary when KL divergence is finite

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

/-- The real-valued Radon-Nikodym density used in the absolutely-continuous part of Pinsker. -/
private noncomputable def rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Ω) : ℝ :=
  ((μ.rnDeriv ν x).toReal)

private theorem rnDensity_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Ω) :
    0 ≤ rnDensity μ ν x :=
  ENNReal.toReal_nonneg

private theorem measurable_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measurable (rnDensity μ ν) := by
  unfold rnDensity
  fun_prop

private theorem integrable_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (rnDensity μ ν) ν := by
  simpa [rnDensity] using
    (Measure.integrable_toReal_rnDeriv
      (μ := μ) (ν := ν))

private theorem integral_rnDensity_eq_one_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ∫ x, rnDensity μ ν x ∂ν = 1 := by
  have h := Measure.integral_toReal_rnDeriv h_ac
  simpa [rnDensity] using h

private theorem integrable_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun x => rnDensity μ ν x - 1) ν :=
  (integrable_rnDensity μ ν).sub (integrable_const 1)

private theorem integrable_abs_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun x => |rnDensity μ ν x - 1|) ν :=
  (integrable_rnDensity_sub_one μ ν).abs

private theorem integral_rnDensity_sub_one_eq_zero_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ∫ x, rnDensity μ ν x - 1 ∂ν = 0 := by
  rw [integral_sub (integrable_rnDensity μ ν) (integrable_const 1),
    integral_rnDensity_eq_one_of_ac μ ν h_ac]
  simp

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
  have hupper_sSup :
      sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) ≤ pos := by
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hpos_nonneg
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) :=
    ⟨pos, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
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

private noncomputable def densityAbsIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  ∫ x, |rnDensity μ ν x - 1| ∂ν

private def densityPositiveSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Set Ω :=
  {x | 1 ≤ rnDensity μ ν x}

private theorem measurableSet_densityPositiveSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurableSet (densityPositiveSet μ ν) := by
  exact measurableSet_Ici.preimage (measurable_rnDensity μ ν)

private noncomputable def densityPositiveIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  ∫ x in densityPositiveSet μ ν, (rnDensity μ ν x - 1) ∂ν

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

private theorem tvDistance_eq_densityPositiveIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistance μ ν = densityPositiveIntegral μ ν := by
  rw [TVDistance.tvDistance_eq_tvDistanceSup,
    tvDistanceSup_eq_densityPositiveIntegral_of_ac μ ν h_ac]

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

private theorem integral_exp_sub_cgf_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {t : ℝ} (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ) :
    ∫ x, Real.exp (t * X x - ProbabilityTheory.cgf X μ t) ∂μ = 1 := by
  rw [show (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) =
      fun x => (Real.exp (-ProbabilityTheory.cgf X μ t)) * Real.exp (t * X x) by
        ext x
        rw [sub_eq_add_neg, Real.exp_add]
        ring]
  rw [integral_const_mul]
  change Real.exp (-ProbabilityTheory.cgf X μ t) * ProbabilityTheory.mgf X μ t = 1
  rw [← ProbabilityTheory.exp_cgf h_exp_int]
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]

private theorem integrable_exp_sub_cgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {t : ℝ} (h_exp_int : Integrable (fun x => Real.exp (t * X x)) μ) :
    Integrable (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) μ := by
  rw [show (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) =
      fun x => (Real.exp (-ProbabilityTheory.cgf X μ t)) * Real.exp (t * X x) by
        ext x
        rw [sub_eq_add_neg, Real.exp_add]
        ring]
  exact h_exp_int.const_mul _

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

private theorem tvDistance_eq_half_densityAbsIntegral_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    tvDistance μ ν = (1 / 2 : ℝ) * densityAbsIntegral μ ν := by
  rw [tvDistance_eq_densityPositiveIntegral_of_ac μ ν h_ac,
    densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac μ ν h_ac]

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

private theorem integral_klFun_rnDeriv_eq_kl_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (∫ x, InformationTheory.klFun (rnDensity μ ν x) ∂ν) =
      ∫ x, llr μ ν x ∂μ := by
  have h := InformationTheory.integral_klFun_rnDeriv h_ac h_int
  simpa [rnDensity] using h

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

/-- Pinsker's inequality: total variation distance is bounded by KL divergence. This is stated in
the `ℝ≥0∞` form `2 * TV^2 ≤ KL`, using natural logarithms in Mathlib's KL divergence. -/
theorem pinsker_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  by_cases h_ac : μ ≪ ν
  · exact pinsker_inequality_of_ac μ ν h_ac
  · rw [InformationTheory.klDiv_of_not_ac h_ac]
    exact le_top

/-- Real-valued Pinsker corollary, useful once the relevant KL divergence is known to be finite. -/
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
