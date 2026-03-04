import TCSlib.BooleanAnalysis.Circuit
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov


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
  (hX_int : Integrable)


/- theorem b_reasonable_tail_bound -- the extended non negative reals make this annoying
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {B : ℝ} (hB : IsBReasonable X P B)
  (t : ℝ) (ht : 0 < t) (hX_pos : 0 < moment X 2 P) -- True if X isn't equivalent to 0
  (hX_int : Integrable (fun ω ↦ X ω ^ 4) P) : -- We need to ensure the 4th moment is finite
  -- Below I already applied the power of 4; might want to rewrite later
  (P {ω | X ω ^ 4 ≥ t ^ 4 * (moment X 2 P) ^ 2}).toReal ≤ B / t ^ 4 := by -/
