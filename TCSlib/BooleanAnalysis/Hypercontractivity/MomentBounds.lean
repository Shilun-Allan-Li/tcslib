import TCSlib.BooleanAnalysis.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Distributions.Uniform

/-!
# Moment bounds and anticoncentration

This file develops consequences of fourth-moment (`B`-reasonability) bounds for real-valued random
variables.  The results provide tail, support, and anticoncentration estimates used with Boolean
functions.

## Main definitions

* `IsBReasonable`: the assertion that the fourth moment is at most `B` times the square of the
  second moment.

## Main results

* `b_reasonable_tail_bound`: a fourth-moment tail bound.
* `min_prob_b_reasonable`: a lower bound on the probability of nonzero values.
* `paley_zygmund_ineq` and `b_reasonable_anticon_zero`: Paley--Zygmund-style anticoncentration
  estimates.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §9.1.
-/

namespace Bonami
open BooleanAnalysis

section
open MeasureTheory ProbabilityTheory Filter BooleanAnalysis

/-! ## B-Reasonability Bounds -/

/-- Defines `B`-reasonability by bounding a fourth moment by `B` times the squared second moment.

**Source:** [OD14, Def. 9.1]. -/
def IsBReasonable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) (B : ℝ) : Prop :=
  moment X 4 P ≤ B * (moment X 2 P) ^ 2

/-- Bounds the fourth-moment tail of a `B`-reasonable random variable.

**Source:** [OD14, Prop. 9.3]. -/
lemma b_reasonable_tail_bound
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

/-- Shows that a discrete random variable is `(1 / μ)`-reasonable when every atom has mass at
least `μ`.

**Source:** [OD14, Prop. 9.5]. -/
lemma min_prob_b_reasonable
  {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω] [DiscreteMeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {π : PMF Ω} (hP : P = π.toMeasure)
  {μ : ℝ} (hμ_pos : 0 < μ) (hμ_min : ∀ ω, μ ≤ (π ω).toReal) :
  IsBReasonable X P (1 / μ) := by

  -- Unfold the definition of IsBReasonable
  rw [IsBReasonable]

  -- Establish that the integrals equal finite sums
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
    rw [moment]; simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]
    rw [hP]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only [Measure.real]
    rw [PMF.toMeasure_apply_singleton]; ring; simp only [MeasurableSet.singleton]

  rw [h_mom4, h_mom2]

  -- Set up the algebraic calculation
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
        rw [div_eq_mul_inv, div_eq_mul_inv]
        gcongr
        -- Apply the reciprocal inequality: 1 / (π ω).toReal ≤ 1 / μ
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
end

section
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Gives the Paley--Zygmund lower bound for a nonnegative integrable random variable.

**Source:** [OD14, Prop. 9.4]. -/
lemma paley_zygmund_ineq
  {Z : Ω → ℝ}
  (h_meas : Measurable Z)
  (h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
  (h_int : Integrable Z μ)
  (h_int_sq : Integrable (fun ω ↦ Z ω ^ 2) μ)
  {θ : ℝ} (hθ_pos : 0 ≤ θ) (hθ_le_one : θ ≤ 1)
  (hZ_pos : 0 < moment Z 1 μ) :
  (1 - θ)^2 * (moment Z 1 μ)^2 / moment Z 2 μ ≤ (μ {ω | θ * moment Z 1 μ < Z ω}).toReal := by
  simp_rw [moment, pow_one] at hZ_pos ⊢
  set A := {ω | θ * ∫ ω, Z ω ∂μ < Z ω}
  have hA_meas : MeasurableSet A :=
    measurableSet_lt measurable_const h_meas
  -- Split the expectation into A and Aᶜ
  have h_split : ∫ ω, Z ω ∂μ = (∫ ω in A, Z ω ∂μ) + (∫ ω in Aᶜ, Z ω ∂μ) :=
    (integral_add_compl hA_meas h_int).symm
  -- Bound the integral over Aᶜ
  have h_Ac_bound : ∫ ω in Aᶜ, Z ω ∂μ ≤ θ * ∫ ω, Z ω ∂μ := by
    calc ∫ ω in Aᶜ, Z ω ∂μ
      _ ≤ ∫ ω in Aᶜ, (θ * ∫ x, Z x ∂μ) ∂μ := by
        apply integral_mono_ae h_int.integrableOn
        · exact integrable_const _
        · rw [EventuallyLE, ae_restrict_iff' hA_meas.compl]
          exact Eventually.of_forall (fun ω hω ↦ not_lt.mp hω)
      _ = (θ * ∫ ω, Z ω ∂μ) * (μ Aᶜ).toReal := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
           smul_eq_mul, mul_comm, mul_eq_mul_left_iff, mul_eq_zero]
        left; rfl

      -- μ(Aᶜ) ≤ 1, so we can bound the product
      _ ≤ (θ * ∫ ω, Z ω ∂μ) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · -- Get the standard probability bound: μ(Aᶜ) ≤ 1
          have h_prob : μ Aᶜ ≤ 1 := prob_le_one
          -- Apply the monotonicity of .toReal
          have h_mono := ENNReal.toReal_mono ENNReal.one_ne_top h_prob
          rwa [ENNReal.toReal_one] at h_mono
        · positivity
      _ = θ * ∫ ω, Z ω ∂μ := mul_one _

  -- Isolate and bound the integral over A
  have h_A_lower_bound : (1 - θ) * ∫ ω, Z ω ∂μ ≤ ∫ ω in A, Z ω ∂μ := by
    calc (1 - θ) * ∫ ω, Z ω ∂μ
      -- Expand the multiplication so linarith can read it
      _ = ∫ ω, Z ω ∂μ - θ * ∫ ω, Z ω ∂μ := by ring
      -- Now linarith can easily substitute h_Ac_bound into h_split
      _ ≤ ∫ ω in A, Z ω ∂μ := by linarith [h_split, h_Ac_bound]

  -- Apply Hölder's Inequality for p=2, q=2 (Cauchy-Schwarz)
  have h_CS : (∫ ω in A, Z ω ∂μ) ^ 2 ≤ (∫ ω in A, (Z ω) ^ 2 ∂μ) * (μ A).toReal := by
    -- 6a: First, isolate the non-squared Hölder bound
    have h_Holder : ∫ ω in A, Z ω * 1 ∂μ ≤
        (∫ ω in A, (Z ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ ω in A, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
      -- Rewrite integer squares `^ 2` to real powers `^ (2 : ℝ)` to perfectly match the lemma
      simp_rw [← Real.rpow_two]
      have h_two : ENNReal.ofReal 2 = 2 := by norm_num
      apply MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg ⟨by norm_num, by norm_num, by norm_num⟩
      · exact ae_restrict_of_ae h_nonneg
      · exact Filter.Eventually.of_forall (fun _ ↦ zero_le_one)
      · apply MemLp.restrict
        rw [h_two]
        rw [memLp_two_iff_integrable_sq (h_int.aestronglyMeasurable)]
        exact h_int_sq
      rw [h_two]
      exact memLp_const (1 : ℝ)
    -- Square both sides and algebraically clean up the exponents
    calc (∫ ω in A, Z ω ∂μ) ^ 2
      _ = (∫ ω in A, Z ω * 1 ∂μ) ^ 2 := by
        congr 2
        ext ω
        exact (mul_one (Z ω)).symm
      _ ≤ ((∫ ω in A, (Z ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ ω in A, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr -- Reduces to 0 ≤ ∫ (ω : Ω) in A, Z ω * 1 ∂μ
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
        congr 1
        simp_rw [one_pow]
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          smul_eq_mul, mul_one]
        exact rfl
  -- Split into two cases based on whether the denominator is zero
  by_cases h_zero : ∫ (x : Ω), (Z ^ 2) x ∂μ = 0
  · -- Case 1: The denominator is zero.
    rw [h_zero, div_zero]
    exact ENNReal.toReal_nonneg
  · -- Case 2: The denominator is not zero.
    have h_pos : 0 < ∫ (x : Ω), (Z ^ 2) x ∂μ :=
      lt_of_le_of_ne (MeasureTheory.integral_nonneg (fun _ ↦ sq_nonneg _)) (Ne.symm h_zero)
    rw [div_le_iff₀ h_pos]
    calc
        (1 - θ) ^ 2 * (∫ x, Z x ∂μ) ^ 2
          = ((1 - θ) * ∫ x, Z x ∂μ) ^ 2 := by
            ring

        _ ≤ (∫ (ω : Ω) in A, Z ω ∂μ) ^ 2 := by
          have h_lhs_nonneg : 0 ≤ (1 - θ) * ∫ x, Z x ∂μ := by
            apply mul_nonneg
            · -- Prove 0 ≤ 1 - θ
              linarith [hθ_pos]
            · -- Prove 0 ≤ ∫ Z
              exact MeasureTheory.integral_nonneg_of_ae h_nonneg
          nlinarith [h_CS, h_lhs_nonneg]

        _ ≤ (μ A).toReal * ∫ x, (Z ^ 2) x ∂μ := by
            -- Plug in Cauchy-Schwarz
            have h_Holder_comm : (∫ (ω : Ω) in A, Z ω ∂μ) ^ 2 ≤ (μ A).toReal * ∫ (ω : Ω) in A, Z ω ^ 2 ∂μ := by
              calc (∫ (ω : Ω) in A, Z ω ∂μ) ^ 2
                _ ≤ (∫ (ω : Ω) in A, Z ω ^ 2 ∂μ) * (μ A).toReal := h_CS
                _ = (μ A).toReal * ∫ (ω : Ω) in A, Z ω ^ 2 ∂μ := mul_comm _ _
            refine le_trans h_Holder_comm ?_
            -- Prove P(A) * ∫_A Z^2 ≤ P(A) * ∫_Ω Z^2
            apply mul_le_mul_of_nonneg_left
            · -- Prove ∫_A Z^2 ≤ ∫_Ω Z^2
              apply MeasureTheory.integral_mono_measure MeasureTheory.Measure.restrict_le_self
              · -- 1. Prove the function is non-negative almost everywhere
                exact Eventually.of_forall (fun _ ↦ sq_nonneg _)
              · -- 2. Prove the function is integrable over the whole space
                exact h_int_sq
            · -- Prove 0 ≤ P(A)
               exact ENNReal.toReal_nonneg

/-- Gives the Paley--Zygmund anticoncentration bound for a `B`-reasonable random variable.

**Source:** [OD14, Prop. 9.4]. -/
lemma b_reasonable_anticon_zero -- anticoncentration bound with theta = 0; general result after
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {B : ℝ} (hB : IsBReasonable X P B)
  (hX_meas : Measurable X)
  (hX_int_sq : Integrable (fun ω ↦ X ω ^ 2) P)
  (hX_int_4 : Integrable (fun ω ↦ X ω ^ 4) P)
  (hX_pos_2 : 0 < moment X 2 P)/-  -/
  {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
  (1 - t^2)^2 / B ≤ (P {ω | t^2 * moment X 2 P < X ω ^ 2}).toReal := by
  let Z := fun ω ↦ X ω ^ 2
  let θ := t^2
  -- Verify hypotheses for paley_zygmund_ineq
  have hZ_meas : Measurable Z := hX_meas.pow_const 2
  have hZ_nonneg : ∀ᵐ ω ∂P, 0 ≤ Z ω :=
    Filter.Eventually.of_forall (fun ω ↦ sq_nonneg (X ω))
  have hθ_pos : 0 ≤ θ := sq_nonneg t
  have hθ_le_one : θ ≤ 1 := by nlinarith [ht_nonneg, ht_le_one]
  have h_mom1 : moment Z 1 P = moment X 2 P := by
    simp_rw [moment, pow_one]
    rfl
  have h_mom2 : moment Z 2 P = moment X 4 P := by
    simp_rw [moment]
    congr 1
    ext ω
    show (X ω ^ 2) ^ 2 = X ω ^ 4
    ring
  have hZ_pos : 0 < moment Z 1 P := by
    rw [h_mom1]
    exact hX_pos_2
  have hZ_int : Integrable Z P := hX_int_sq
  have hZ_int_sq : Integrable (fun ω ↦ Z ω ^ 2) P := by
    have h_eq : (fun ω ↦ Z ω ^ 2) = (fun ω ↦ X ω ^ 4) := by
      ext ω
      show (X ω ^ 2) ^ 2 = X ω ^ 4
      ring
    rw [h_eq]
    exact hX_int_4
  have h_pz := paley_zygmund_ineq hZ_meas hZ_nonneg hZ_int hZ_int_sq hθ_pos hθ_le_one hZ_pos
  -- Moment is positive
  have hX_pos : 0 < moment X 4 P := by
    apply lt_of_le_of_ne
    · -- 1. Prove 0 ≤ moment X 4 P
      unfold moment
      have h_nonneg_4 : ∀ ω, 0 ≤ X ω ^ 4 := by
        intro ω
        positivity
      exact MeasureTheory.integral_nonneg h_nonneg_4
    · -- 2. Prove moment X 4 P ≠ 0 by contradiction
      intro h_eq
      have h_ae_zero : (fun ω ↦ X ω ^ 4) =ᵐ[P] 0 := by
        have h_nonneg : 0 ≤ fun ω ↦ X ω ^ 4 := by
          intro ω
          positivity
        have h_eq' : ∫ ω, X ω ^ 4 ∂P = 0 := h_eq.symm
        exact (MeasureTheory.integral_eq_zero_iff_of_nonneg h_nonneg hX_int_4).mp h_eq'
      have h_ae_zero_sq : (fun ω ↦ X ω ^ 2) =ᵐ[P] 0 := by
        filter_upwards [h_ae_zero] with ω hω
        change X ω ^ 4 = 0 at hω
        have h_sq : (X ω ^ 2) ^ 2 = 0 := by
          calc (X ω ^ 2) ^ 2 = X ω ^ 4 := by ring
            _ = 0 := hω
        exact sq_eq_zero_iff.mp h_sq
      have h_mom2_zero : moment X 2 P = 0 := by
        unfold moment
        simp_rw [Pi.pow_apply] -- Converts (X ^ 2) ω to X ω ^ 2
        rw [MeasureTheory.integral_congr_ae h_ae_zero_sq]
        simp only [Pi.zero_apply, integral_zero]
      exact hX_pos_2.ne' h_mom2_zero

  have h_pz_mapped : (1 - t^2)^2 * (moment X 2 P)^2 / moment X 4 P ≤ (P {ω | t^2 * moment X 2 P < X ω ^ 2}).toReal := by
    have h_pz' := h_pz
    rw [h_mom1, h_mom2] at h_pz'
    exact h_pz'
  have h_bound : (1 - t^2)^2 / B ≤ (1 - t^2)^2 * (moment X 2 P)^2 / moment X 4 P := by
    have h_mom2_sq_pos : 0 < (moment X 2 P)^2 := by
      simp only [hX_pos_2, pow_succ_pos]
    calc (1 - t^2)^2 / B
      _ = ((1 - t^2)^2 * (moment X 2 P)^2) / (B * (moment X 2 P)^2) := by
        rw [mul_div_mul_right _ _ h_mom2_sq_pos.ne']
      _ ≤ ((1 - t^2)^2 * (moment X 2 P)^2) / moment X 4 P := by
        gcongr
        exact hB
  exact le_trans h_bound h_pz_mapped

end
end Bonami
