import TCSlib.BooleanAnalysis.Circuit
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace Hypercontractivity

section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal
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
      simp only [moment, Pi.pow_apply]
      rfl
    _ ≤ (B * (moment X 2 P) ^ 2) / (t ^ 4 * (moment X 2 P) ^ 2) := by
      gcongr
      exact hB
    _ = B / t^4 := by
      rw [mul_div_mul_right B (t ^ 4) (_)]
      · exact ne_of_gt (by positivity)

lemma min_prob_b_reasonable
  {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω] [DiscreteMeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {π : PMF Ω} (hP : P = π.toMeasure)
  {μ : ℝ} (hμ_pos : 0 < μ) (hμ_min : ∀ ω, μ ≤ (π ω).toReal) :
  IsBReasonable X P (1 / μ) := by

  -- Unfold the definition of IsBReasonable
  rw [IsBReasonable]

  -- Step 1: Establish that the integrals equal finite sums
  -- (We state these as claims to be proven using Mathlib's integral_fintype)
  have h_mom4 : moment X 4 P = ∑ ω, X ω ^ 4 * (π ω).toReal := by
    rw [moment]
    simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]
    rw [hP]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only [Measure.real]
    rw [PMF.toMeasure_apply_singleton]; ring
    simp only [MeasurableSet.singleton]

  have h_mom2 : moment X 2 P = ∑ ω, X ω ^ 2 * (π ω).toReal := by
    rw [moment];
    simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]
    rw [hP]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only [Measure.real]
    rw [PMF.toMeasure_apply_singleton]; ring; simp only [MeasurableSet.singleton]

  rw [h_mom4, h_mom2]
  -- Step 2: Set up the algebraic calculation
  calc
    ∑ ω, X ω ^ 4 * (π ω).toReal
      = ∑ ω, (X ω ^ 2 * (π ω).toReal) ^ 2 / (π ω).toReal := by
        apply Finset.sum_congr rfl
        intro ω hω
        have h_pi_pos : 0 < (π ω).toReal := lt_of_lt_of_le hμ_pos (hμ_min ω)
        have h_pi_ne_zero : (π ω).toReal ≠ 0 := ne_of_gt h_pi_pos
        -- Algebraic rearrangement: a^4 * p = (a^2 * p)^2 / p
        ring_nf
        calc
          X ω ^ 4 * (π ω).toReal
            = X ω ^ 4 * (π ω).toReal * 1 := by rw [mul_one]
            _ = X ω ^ 4 * (π ω).toReal * ((π ω).toReal * (π ω).toReal⁻¹) := by rw [mul_inv_cancel₀ h_pi_ne_zero]
            _ = X ω ^ 4 * (π ω).toReal ^ 2 * (π ω).toReal⁻¹ := by ring

      _ ≤ ∑ ω, (X ω ^ 2 * (π ω).toReal) ^ 2 / μ := by
        -- Use the fact that λ ≤ π ω, so 1 / π ω ≤ 1 / λ
        apply Finset.sum_le_sum
        intro ω hω
        have h_pi_pos : 0 < (π ω).toReal := lt_of_lt_of_le hμ_pos (hμ_min ω)
        -- 3. Use gcongr or direct multiplication to apply the inequality
        rw [div_eq_mul_inv, div_eq_mul_inv]
        gcongr
        -- 4. Apply the reciprocal inequality: 1 / (π ω).toReal ≤ 1 / μ
        simp only [hμ_min]

      _ = (1 / μ) * ∑ ω, (X ω ^ 2 * (π ω).toReal) ^ 2 := by
        -- Factor out the (1 / λ)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ (1 / μ) * (∑ ω, X ω ^ 2 * (π ω).toReal) ^ 2 := by
        -- Apply the inequality: ∑ (y_i)^2 ≤ (∑ y_i)^2 for non-negative terms
        gcongr
        let y := fun ω => X ω ^ 2 * (π ω).toReal
        -- Prove that y_i is non-negative for all ω
        have hy_nonneg : ∀ ω, 0 ≤ y ω := by
          intro ω
          unfold y
          positivity

        -- Apply the sum-of-squares inequality
        calc
          ∑ ω, (y ω)^2 ≤ (∑ ω, y ω)^2 := by
            apply Finset.sum_sq_le_sq_sum_of_nonneg
            intro ω _
            exact hy_nonneg ω

         -- Prove `∑ (y_i)^2 ≤ (∑ y_i)^2` here
end

open MeasureTheory Set Filter ProbabilityTheory
open scoped Real
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
-- MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg is used for Cauchy-Schwarz
lemma paley_zygmund_ineq
  {Z : Ω → ℝ}
  (h_meas : Measurable Z)
  (h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
  (h_int : Integrable Z μ)
  (h_int_sq : Integrable (fun ω ↦ Z ω ^ 2) μ)
  {θ : ℝ} (hθ_pos : 0 ≤ θ) (hθ_le_one : θ ≤ 1)
  (hZ_pos : 0 < moment Z 1 μ) :
  (1 - θ)^2 * (moment Z 1 μ)^2 / moment Z 2 μ ≤ (μ {ω | θ * moment Z 1 μ < Z ω}).toReal := by
  -- Step 1: Unfold the definition of `moment` and simplify `Z ω ^ 1` to `Z ω`
  simp_rw [moment, pow_one] at hZ_pos ⊢

  -- Step 2: Define our set A and prove it is measurable
  set A := {ω | θ * ∫ ω, Z ω ∂μ < Z ω}
  have hA_meas : MeasurableSet A :=
    measurableSet_lt measurable_const h_meas

  -- Step 3: Split the expectation into A and Aᶜ
  have h_split : ∫ ω, Z ω ∂μ = (∫ ω in A, Z ω ∂μ) + (∫ ω in Aᶜ, Z ω ∂μ) :=
    (integral_add_compl hA_meas h_int).symm
  -- Step 4: Bound the integral over Aᶜ
  have h_Ac_bound : ∫ ω in Aᶜ, Z ω ∂μ ≤ θ * ∫ ω, Z ω ∂μ := by
    calc ∫ ω in Aᶜ, Z ω ∂μ
      _ ≤ ∫ ω in Aᶜ, (θ * ∫ x, Z x ∂μ) ∂μ := by
        -- Use standard integral_mono_ae on the restricted measure
        apply integral_mono_ae h_int.integrableOn
        · -- The constant is integrable because the measure is finite
          exact integrable_const _
        · -- ae_restrict_iff' translates "almost everywhere on Aᶜ" to an implication
          rw [EventuallyLE, ae_restrict_iff' hA_meas.compl]
          -- Now we just provide the standard logical bound
          exact Eventually.of_forall (fun ω hω ↦ not_lt.mp hω)

      -- The integral of a constant gives the constant times the measure
      _ = (θ * ∫ ω, Z ω ∂μ) * (μ Aᶜ).toReal := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          smul_eq_mul, mul_comm, mul_eq_mul_left_iff, mul_eq_zero]
        left
        rfl

      -- μ(Aᶜ) ≤ 1, so we can bound the product
      _ ≤ (θ * ∫ ω, Z ω ∂μ) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · -- Get the standard probability bound: μ(Aᶜ) ≤ 1
          have h_prob : μ Aᶜ ≤ 1 := prob_le_one
          -- Apply the monotonicity of .toReal (requires proving 1 ≠ ∞)
          have h_mono := ENNReal.toReal_mono ENNReal.one_ne_top h_prob
          -- Simplify (1 : ℝ≥0∞).toReal down to 1 and close the goal
          rwa [ENNReal.toReal_one] at h_mono
        · positivity

      -- x * 1 = x
      _ = θ * ∫ ω, Z ω ∂μ := mul_one _
  -- Step 5: Isolate and bound the integral over A
  have h_A_lower_bound : (1 - θ) * ∫ ω, Z ω ∂μ ≤ ∫ ω in A, Z ω ∂μ := by
    calc (1 - θ) * ∫ ω, Z ω ∂μ
      -- 5a: Expand the multiplication so linarith can read it
      _ = ∫ ω, Z ω ∂μ - θ * ∫ ω, Z ω ∂μ := by ring

      -- 5b: Now linarith can easily substitute h_Ac_bound into h_split
      _ ≤ ∫ ω in A, Z ω ∂μ := by linarith [h_split, h_Ac_bound]
 -- Step 6: Apply Hölder's Inequality for p=2, q=2 (Cauchy-Schwarz)
  -- Step 6: Apply Hölder's Inequality for p=2, q=2 (Cauchy-Schwarz)
  have h_CS : (∫ ω in A, Z ω ∂μ) ^ 2 ≤ (∫ ω in A, (Z ω) ^ 2 ∂μ) * (μ A).toReal := by
    -- 6a: First, isolate the non-squared Hölder bound
    have h_Holder : ∫ ω in A, Z ω * 1 ∂μ ≤
        (∫ ω in A, (Z ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ ω in A, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
      -- Rewrite integer squares `^ 2` to real powers `^ (2 : ℝ)` to perfectly match the lemma
      simp_rw [← Real.rpow_two]
      have h_two : ENNReal.ofReal 2 = 2 := by norm_num
      apply MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg ⟨by norm_num, by norm_num, by norm_num⟩                -- 1 is measurable
      · exact ae_restrict_of_ae h_nonneg
      · exact Filter.Eventually.of_forall (fun _ ↦ zero_le_one)
      · apply MemLp.restrict
        rw [h_two]
        rw [memLp_two_iff_integrable_sq (h_int.aestronglyMeasurable)]
        exact h_int_sq
      rw [h_two]
      exact memLp_const (1 : ℝ)

    -- 6b: Square both sides and algebraically clean up the exponents
    calc (∫ ω in A, Z ω ∂μ) ^ 2
      _ = (∫ ω in A, Z ω * 1 ∂μ) ^ 2 := by
        congr 2
        ext ω
        exact (mul_one (Z ω)).symm

      _ ≤ ((∫ ω in A, (Z ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ ω in A, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        · apply MeasureTheory.integral_nonneg_of_ae
          filter_upwards [ae_restrict_of_ae h_nonneg] with ω hω
          exact mul_nonneg hω zero_le_one

      _ = (∫ ω in A, (Z ω) ^ 2 ∂μ) * (∫ ω in A, (1 : ℝ) ^ 2 ∂μ) := by
        rw [mul_pow]
        congr 1
        · -- Cancel the exponent for Z^2: ((Z^2)^(1/2))^2 -> (Z^2)^((1/2)*2) -> Z^2
          rw [← Real.rpow_two, ← Real.rpow_mul (MeasureTheory.integral_nonneg (fun ω ↦ sq_nonneg (Z ω)))]
          have h_half_two : (1 / 2 : ℝ) * 2 = 1 := by norm_num
          rw [h_half_two, Real.rpow_one]
        · -- Cancel the exponent for 1^2 identically
          simp_rw [one_pow]
          rw [← Real.rpow_two]
          rw [← Real.rpow_mul (MeasureTheory.integral_nonneg (fun _ ↦ zero_le_one))]
          have h_half_two : (1 / 2 : ℝ) * 2 = 1 := by norm_num
          rw [h_half_two, Real.rpow_one]

      _ = (∫ ω in A, (Z ω) ^ 2 ∂μ) * (μ A).toReal := by
        -- 1. Strip away the identical '(∫ Z^2)' from both sides
        congr 1
        simp_rw [one_pow]
        simp [MeasureTheory.integral_const]
        exact rfl
-- 1. Split into two cases based on whether the denominator is zero
  by_cases h_zero : ∫ (x : Ω), (Z ^ 2) x ∂μ = 0

  · -- Case 1: The denominator is zero.
    -- Lean evaluates X / 0 as 0, so the LHS is 0.
    -- The RHS is a measure, which is always ≥ 0.
    rw [h_zero, div_zero]
    exact ENNReal.toReal_nonneg

  · -- Case 2: The denominator is not zero.
    -- Since integrals of squares are ≥ 0, it must be strictly positive.
    have h_pos : 0 < ∫ (x : Ω), (Z ^ 2) x ∂μ :=
      lt_of_le_of_ne (MeasureTheory.integral_nonneg (fun _ ↦ sq_nonneg _)) (Ne.symm h_zero)

    -- Now Lean will allow us to multiply both sides by the denominator!
    rw [div_le_iff₀ h_pos]
    calc
        (1 - θ) ^ 2 * (∫ x, Z x ∂μ) ^ 2
          = ((1 - θ) * ∫ x, Z x ∂μ) ^ 2 := by
            -- Step 1: Group the squares. `ring` handles this instantly.
            ring

        _ ≤ (∫ (ω : Ω) in A, Z ω ∂μ) ^ 2 := by
            -- Step 2: Square both sides of your Markov inequality.
            -- Now that the algebra is out of the way, nlinarith can easily
            -- see that A ≤ B implies A^2 ≤ B^2 (as long as things are positive).
            -- You may need to feed it the non-negativity of the integral here!
            sorry

        _ ≤ (μ A).toReal * ∫ x, (Z ^ 2) x ∂μ := by
            -- Step 3: Plug in your Cauchy-Schwarz / Hölder block!
            sorry
  /- {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} (hB : IsBReasonable X P B)
  (t : ℝ) (htg : 0 ≤ t) (htl : t ≤ 1) (hX_pos : 0 < moment X 2 P)
  (hX_int2 : Integrable (fun ω ↦ X ω ^ 2) P)
  (hX_int4 : Integrable (fun ω ↦ X ω ^ 4) P) (hX_meas : Measurable X) :
  (P {ω | |X ω| ≥ t * Real.sqrt (moment X 2 P)}).toReal ≥ ((1 - t ^ 2) ^ 2) / B := by -/
