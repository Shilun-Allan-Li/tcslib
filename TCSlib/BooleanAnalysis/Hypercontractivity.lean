import TCSlib.BooleanAnalysis.Circuit
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Hypercontractivity


open MeasureTheory ProbabilityTheory

def IsBReasonable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) (B : ℝ) : Prop :=
  moment X 4 P ≤ B * (moment X 2 P) ^ 2

lemma b_reasonable_tail_bound -- the extended non negative reals make this annoying
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {B : ℝ} (hB : IsBReasonable X P B)
  (t : ℝ) (ht : 0 < t) (hX_pos : 0 < moment X 2 P) -- True if X isn't equivalent to 0
  (hX_int : Integrable (fun ω ↦ X ω ^ 4) P) : -- probably don't need; target for rewrite
  -- Below I already applied the power of 4; might want to rewrite later
  (P {ω | X ω ^ 4 ≥ t ^ 4 * (moment X 2 P) ^ 2}).toReal ≤ B / t ^ 4 := by
  set c : ℝ := t ^ 4 * (moment X 2 P) ^ 2 -- define c to make it easier to write out
  have hc_pos : c > 0 := by positivity
  have h_set : {ω | c ≤ X ω ^ 4} = {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (X ω ^ 4)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    -- ENNReal.ofReal_le_ofReal_iff requires proof that 0 ≤ c
    rw [ENNReal.ofReal_le_ofReal_iff]
    positivity
  calc -- calc out the inequality
    (P {ω | X ω ^ 4 ≥ c}).toReal
    = (P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (X ω ^ 4)}).toReal := by -- turn real to ENNReal
      rw [h_set]
    _ ≤ ((∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂P) / ENNReal.ofReal c).toReal := by -- show integral ineq
      apply ENNReal.toReal_mono
      · -- show integral isn't infinity
        apply ne_of_lt
        apply ENNReal.div_lt_top
        · -- show the term is everywhere nonnegative
          have h_nonneg : 0 ≤ᵐ[P] fun ω ↦ X ω ^ 4 := by
            filter_upwards
            intro ω
            positivity
          apply ne_of_lt
          exact (MeasureTheory.hasFiniteIntegral_iff_ofReal h_nonneg).mp hX_int.hasFiniteIntegral
        · -- show c ≠ 0
          exact (ENNReal.ofReal_pos.mpr hc_pos).ne'
      · -- apply markov ineq
        apply MeasureTheory.meas_ge_le_lintegral_div
        · -- need to show f everywhere measurable
          exact hX_int.1.aemeasurable.ennreal_ofReal
        · -- c ≠ 0 again
          exact (ENNReal.ofReal_pos.mpr hc_pos).ne'
        · -- c ≠ infinity
          exact ENNReal.ofReal_ne_top
    -- get to real integral
    _ = (∫ ω, X ω ^ 4 ∂P) / c := by
      rw [ENNReal.toReal_div]
      have h_nonneg : 0 ≤ᵐ[P] fun ω ↦ X ω ^ 4 := by
        filter_upwards
        intro ω
        positivity
      -- changes integral
      rw [← integral_eq_lintegral_of_nonneg_ae h_nonneg]
      -- simplify denominator
      rw [ENNReal.toReal_ofReal hc_pos.le]
      · exact hX_int.aestronglyMeasurable
    -- unfold definitions
    _ = (moment X 4 P) / (t ^ 4 * (moment X 2 P) ^ 2) := by
      simp [moment]
      rfl
    _ ≤ (B * (moment X 2 P) ^ 2) / (t ^ 4 * (moment X 2 P) ^ 2) := by
      gcongr
      exact hB
    _ = B / t^4 := by
      rw [mul_div_mul_right B (t ^ 4) (_)]
      · exact ne_of_gt (by positivity)

lemma b_reasonable_anticoncentration_bound
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} (hB : IsBReasonable X P B)
  (t : ℝ) (htg : 0 ≤ t) (htl : t ≤ 1) (hX_pos : 0 < moment X 2 P)
  (hX_int2 : Integrable (fun ω ↦ X ω ^ 2) P)
  (hX_int4 : Integrable (fun ω ↦ X ω ^ 4) P) (hX_meas : Measurable X) :
  (P {ω | |X ω| ≥ t * Real.sqrt (moment X 2 P)}).toReal ≥ ((1 - t ^ 2) ^ 2) / B := by
  set M2 := moment X 2 P
  have h_set_eq : {ω | |X ω| ≥ t * Real.sqrt M2} = {ω | X ω ^ 2 ≥ t^2 * M2} := by
    ext ω
    simp only [Set.mem_setOf_eq, ge_iff_le]
    have hM2 : 0 ≤ M2 := le_of_lt hX_pos
    -- Goal: t * Real.sqrt M2 ≤ |X ω| ↔ t^2 * M2 ≤ X ω ^ 2
    constructor
    · intro h
      -- If t * ||X||_2 <= |X(ω)|, then square both sides
      calc t^2 * M2 = t^2 * (Real.sqrt M2)^2 := by rw [Real.sq_sqrt hM2]
        _ = (t * Real.sqrt M2)^2 := by rw [mul_pow]
        _ ≤ |X ω|^2 := by gcongr
        _ = X ω ^ 2 := by rw [sq_abs]
    · intro h
      -- If t^2 * M2 <= X(ω)^2, then take the square root of both sides
      have h_sqrt : Real.sqrt (t^2 * M2) ≤ Real.sqrt (X ω ^ 2) := by gcongr
      have h_left : Real.sqrt (t^2 * M2) = t * Real.sqrt M2 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq htg]
      have h_right : Real.sqrt (X ω ^ 2) = |X ω| := by
        exact Real.sqrt_sq_eq_abs (X ω)
      rw [h_left, h_right] at h_sqrt
      exact h_sqrt
  rw [h_set_eq]

  -- Give the "large" set a name to make our integrals cleaner
  set A := {ω | X ω ^ 2 ≥ t^2 * M2}
  have h_split : (1 - t^2) * M2 ≤ ∫ ω in A, X ω ^ 2 ∂P := by
    have hA_meas : MeasurableSet A :=
      measurableSet_le measurable_const (hX_meas.pow_const 2)
      -- 2. Split the total expected value (M2) into A and Aᶜ
    have h_split_eq : M2 = (∫ ω in A, X ω ^ 2 ∂P) + (∫ ω in Aᶜ, X ω ^ 2 ∂P) :=
      (integral_add_compl hA_meas hX_int2).symm

    -- 3. Bound the integral over the complement Aᶜ
    have h_compl_bound : ∫ ω in Aᶜ, X ω ^ 2 ∂P ≤ t^2 * M2 := by
      have h_le : ∫ ω in Aᶜ, X ω ^ 2 ∂P ≤ ∫ ω in Aᶜ, t^2 * M2 ∂P := by
        apply integral_mono_ae hX_int2.restrict ((integrable_const _).restrict)
        -- On Aᶜ, X^2 < t^2 * M2, so we can bound the function pointwise
        filter_upwards [ae_restrict_mem hA_meas.compl] with ω hω
        exact le_of_lt (not_le.mp hω)

      -- Calculate the upper bound using the measure of Aᶜ
      calc ∫ ω in Aᶜ, X ω ^ 2 ∂P
        _ ≤ ∫ ω in Aᶜ, t^2 * M2 ∂P := h_le
        _ = (P Aᶜ).toReal * (t^2 * M2) := by
          rw [integral_const, smul_eq_mul]
          congr 1
          dsimp [Measure.real]
          -- 2. Simplify (P.restrict Aᶜ Set.univ) into (P Aᶜ)
          rw [Measure.restrict_apply_univ]
        _ ≤ 1 * (t^2 * M2) := by
          gcongr
          -- The probability of any set is ≤ 1
          rw [← ENNReal.toReal_one]
          exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
        _ = t^2 * M2 := one_mul _

    -- 4. Use linear arithmetic to combine h_split_eq and h_compl_bound
    linarith [h_split_eq, h_compl_bound]
  sorry
