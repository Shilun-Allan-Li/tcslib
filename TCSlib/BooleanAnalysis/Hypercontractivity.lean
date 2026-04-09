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
import Mathlib.Analysis.MeanInequalities

namespace Hypercontractivity
open BooleanAnalysis

section
open MeasureTheory ProbabilityTheory Filter

/-! ## B-Reasonability Bounds -/

def IsBReasonable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) (B : ℝ) : Prop :=
  moment X 4 P ≤ B * (moment X 2 P) ^ 2

/-- `If X not equivalent to 0 is B-reasonable, Pr[|X| ≥ t ||X||₂] ≤ B/t⁴ for all t > 0` -/
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

/- `Let X be discrete random variable with PMF π. For μ = min(π), X is (1/μ) reasonable`-/
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

/- `Suppose finite variance. If Z ≥ 0 random, 0 ≤ θ ≤ 1, then P(Z > θE[Z]) ≥ (1 - θ)²(E[Z]²)/(E[Z²])` -/
lemma paley_zygmund_ineq
  {Z : Ω → ℝ}
  (h_meas : Measurable Z)
  (h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
  (h_int : Integrable Z μ)
  (h_int_sq : Integrable (fun ω ↦ Z ω ^ 2) μ)
  {θ : ℝ} (hθ_pos : 0 ≤ θ) (hθ_le_one : θ ≤ 1)
  (hZ_pos : 0 < moment Z 1 μ) :
  (1 - θ)^2 * (moment Z 1 μ)^2 / moment Z 2 μ ≤ (μ {ω | θ * moment Z 1 μ < Z ω}).toReal := by

  -- Unfold the definition of `moment` and simplify `Z ω ^ 1` to `Z ω`
  simp_rw [moment, pow_one] at hZ_pos ⊢
  -- Define our set A and prove it is measurable
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
        -- Strip away the identical '(∫ Z^2)' from both sides
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

/-`X not equivalent to 0 is B-reasonable. Then Pr[|X| > t||X||₂] ≥ (1 - t²)²/B for all t ∈ [0, 1]`-/
lemma b_reasonable_anticon_zero -- anticoncentration bound with theta = 0; general result after
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {B : ℝ} (hB : IsBReasonable X P B)
  (hX_meas : Measurable X)
  (hX_int_sq : Integrable (fun ω ↦ X ω ^ 2) P)
  (hX_int_4 : Integrable (fun ω ↦ X ω ^ 4) P)
  (hX_pos_2 : 0 < moment X 2 P)/-  -/
  {t : ℝ} (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) :
  (1 - t^2)^2 / B ≤ (P {ω | t^2 * moment X 2 P < X ω ^ 2}).toReal := by

  -- 1. Define Z = X^2 and θ = t^2 to map to Paley-Zygmund
  let Z := fun ω ↦ X ω ^ 2
  let θ := t^2

  -- 2. Verify hypotheses for paley_zygmund_ineq
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

  -- 3. Apply Paley-Zygmund
  have h_pz := paley_zygmund_ineq hZ_meas hZ_nonneg hZ_int hZ_int_sq hθ_pos hθ_le_one hZ_pos

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
      -- If moment X 4 P = 0, then X^4 = 0 almost everywhere
      have h_ae_zero : (fun ω ↦ X ω ^ 4) =ᵐ[P] 0 := by
        -- Change to strict pointwise non-negativity to match the lemma
        have h_nonneg : 0 ≤ fun ω ↦ X ω ^ 4 := by
          intro ω
          positivity
        have h_eq' : ∫ ω, X ω ^ 4 ∂P = 0 := h_eq.symm
        -- Using hX_int_4.1 for AEStronglyMeasurable
        exact (MeasureTheory.integral_eq_zero_iff_of_nonneg h_nonneg hX_int_4).mp h_eq'

      -- If X^4 = 0 a.e., then X^2 = 0 a.e.
      have h_ae_zero_sq : (fun ω ↦ X ω ^ 2) =ᵐ[P] 0 := by
        filter_upwards [h_ae_zero] with ω hω
        change X ω ^ 4 = 0 at hω
        have h_sq : (X ω ^ 2) ^ 2 = 0 := by
          calc (X ω ^ 2) ^ 2 = X ω ^ 4 := by ring
            _ = 0 := hω
        exact sq_eq_zero_iff.mp h_sq

      -- If X^2 = 0 a.e., then moment X 2 P = 0, which contradicts hX_pos
      have h_mom2_zero : moment X 2 P = 0 := by
        unfold moment
        simp_rw [Pi.pow_apply] -- Converts (X ^ 2) ω to X ω ^ 2
        rw [MeasureTheory.integral_congr_ae h_ae_zero_sq]
        simp only [Pi.zero_apply, integral_zero]
      exact hX_pos_2.ne' h_mom2_zero

  -- 4. Substitute the mapped moments into the Paley-Zygmund inequality
  have h_pz_mapped : (1 - t^2)^2 * (moment X 2 P)^2 / moment X 4 P ≤ (P {ω | t^2 * moment X 2 P < X ω ^ 2}).toReal := by
    -- Replace Z and θ in the Paley-Zygmund result with their X and t equivalents
    have h_pz' := h_pz
    rw [h_mom1, h_mom2] at h_pz'
    exact h_pz'

  -- 5. Apply the B-reasonableness bound (moment X 4 P ≤ B * (moment X 2 P)^2)
  have h_bound : (1 - t^2)^2 / B ≤ (1 - t^2)^2 * (moment X 2 P)^2 / moment X 4 P := by
    have h_mom2_sq_pos : 0 < (moment X 2 P)^2 := by
      simp only [hX_pos_2, pow_succ_pos]
    calc (1 - t^2)^2 / B
      -- Multiply numerator and denominator by (moment X 2 P)^2
      _ = ((1 - t^2)^2 * (moment X 2 P)^2) / (B * (moment X 2 P)^2) := by
        rw [mul_div_mul_right _ _ h_mom2_sq_pos.ne']
      -- Apply IsBReasonable: moment X 4 P ≤ B * (moment X 2 P)^2
      _ ≤ ((1 - t^2)^2 * (moment X 2 P)^2) / moment X 4 P := by
        gcongr
        exact hB

  -- 6. Conclude by transitivity
  exact le_trans h_bound h_pz_mapped

/-! ## Helper definitions and lemmas for the Bonami lemma -/

/-- Restrict a Boolean function on n+1 variables by fixing the last coordinate. -/
noncomputable def restrictLast {n : ℕ} (f : BooleanFunc (n + 1)) (b : Bool) : BooleanFunc n :=
  fun x => f (Fin.snoc x b)

/-- The average of f over the last coordinate. -/
noncomputable def avgLast {n : ℕ} (f : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x => (restrictLast f false x + restrictLast f true x) / 2

/-- The half-difference of f over the last coordinate. -/
noncomputable def diffLast {n : ℕ} (f : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x => (restrictLast f false x - restrictLast f true x) / 2

/-- restrictLast false = avgLast + diffLast -/
lemma restrictLast_false_eq {n : ℕ} (f : BooleanFunc (n + 1)) (x : BoolCube n) :
    restrictLast f false x = avgLast f x + diffLast f x := by
  simp [restrictLast, avgLast, diffLast]; ring

/-- restrictLast true = avgLast - diffLast -/
lemma restrictLast_true_eq {n : ℕ} (f : BooleanFunc (n + 1)) (x : BoolCube n) :
    restrictLast f true x = avgLast f x - diffLast f x := by
  simp [restrictLast, avgLast, diffLast]; ring

/- The sum over BoolCube (n+1) decomposes as sum over BoolCube n for each Bool value. -/
lemma sum_boolCube_succ {n : ℕ} (φ : BoolCube (n + 1) → ℝ) :
    ∑ x : BoolCube (n + 1), φ x =
    ∑ x : BoolCube n, φ (Fin.snoc x false) + ∑ x : BoolCube n, φ (Fin.snoc x true) := by
  -- We can split the sum over BoolCube (n + 1) into a sum over BoolCube n × Bool.
  have h_split : ∑ x : BoolCube (n + 1), φ x = ∑ x : BoolCube n × Bool, φ (Fin.snoc x.1 x.2) := by
    apply Finset.sum_bij (fun x _ => (Fin.init x, x (Fin.last n)));
    · simp +zetaDelta at *;
    · simp +contextual [funext_iff];
      exact fun a₁ a₂ h₁ h₂ x => by cases x using Fin.lastCases <;> simp_all +decide [ Fin.init ] ;
    · intro b hb; use Fin.snoc b.1 b.2; aesop;
    · aesop;
  simp_all +decide [ ← Finset.sum_add_distrib ];
  erw [ Finset.sum_product ];
  exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_eq_add ] <;> aesop;

/-- uniformWeight (n+1) = uniformWeight n / 2 -/
lemma uniformWeight_succ (n : ℕ) :
    uniformWeight (n + 1) = uniformWeight n / 2 := by
  simp [uniformWeight, pow_succ]
  ring

/- Expectation on BoolCube (n+1) decomposes as average of expectations on the two restrictions. -/
lemma expect_succ_eq {n : ℕ} (φ : BooleanFunc (n + 1)) :
    expect φ = (expect (restrictLast φ false) + expect (restrictLast φ true)) / 2 := by
  unfold expect restrictLast;
  rw [ sum_boolCube_succ ] ; rw [ uniformWeight_succ ] ; ring;

/-- The algebraic identity: (a+b)^4 + (a-b)^4 = 2*(a^4 + 6*a^2*b^2 + b^4) -/
lemma fourth_pow_sum (a b : ℝ) :
    (a + b) ^ 4 + (a - b) ^ 4 = 2 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4) := by ring

/-- The algebraic identity: (a+b)^2 + (a-b)^2 = 2*(a^2 + b^2) -/
lemma second_pow_sum (a b : ℝ) :
    (a + b) ^ 2 + (a - b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by ring

/- Fourth moment decomposition: E[f^4] = E[g^4] + 6*E[g²h²] + E[h^4] -/
lemma fourth_moment_decomp {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ 4) =
    expect (fun x => (avgLast f x) ^ 4) +
    6 * expect (fun x => (avgLast f x) ^ 2 * (diffLast f x) ^ 2) +
    expect (fun x => (diffLast f x) ^ 4) := by
  -- Apply the decomposition to rewrite the expectation.
  have h_decomp : expect (fun x => f x ^ 4) = expect (fun x => ((avgLast f x) + (diffLast f x)) ^ 4) / 2 + expect (fun x => ((avgLast f x) - (diffLast f x)) ^ 4) / 2 := by
    convert expect_succ_eq ( fun x => f x ^ 4 ) using 1;
    unfold expect restrictLast avgLast diffLast; ring_nf;
    rfl;
  rw [ h_decomp ] ; ring_nf ;
  norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring_nf;
  (
  unfold expect; norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring_nf;
  simpa only [ mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using by ring;);

/- Second moment decomposition: E[f^2] = E[g^2] + E[h^2] -/
lemma second_moment_decomp {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ 2) =
    expect (fun x => (avgLast f x) ^ 2) +
    expect (fun x => (diffLast f x) ^ 2) := by
  unfold expect;
  ring_nf;
  -- By definition of $avgLast$ and $diffLast$, we can expand the sums.
  have h_expand : ∑ x : BoolCube (n + 1), f x ^ 2 = ∑ x : BoolCube n, (avgLast f x + diffLast f x) ^ 2 + ∑ x : BoolCube n, (avgLast f x - diffLast f x) ^ 2 := by
    convert sum_boolCube_succ ( fun x => f x ^ 2 ) using 1;
    congr! 2;
    · exact congr_arg ( · ^ 2 ) ( by unfold avgLast diffLast; unfold restrictLast; ring );
    · rw [ ← restrictLast_true_eq ] ; ring!;
  simp_all +decide [ add_sq, sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ]; ring_nf;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, uniformWeight ] ; ring;

/- Cauchy-Schwarz for expect: E[g²h²]² ≤ E[g⁴]·E[h⁴] -/
lemma expect_cs_sq {n : ℕ} (g h : BooleanFunc n) :
    expect (fun x => g x ^ 2 * h x ^ 2) ^ 2 ≤
    expect (fun x => g x ^ 4) * expect (fun x => h x ^ 4) := by
  norm_num [ expect ] at *;
  -- Apply the Cauchy-Schwarz inequality on the sums.
  have h_cauchy_schwarz : (∑ x, g x ^ 2 * h x ^ 2) ^ 2 ≤ (∑ x, g x ^ 4) * (∑ x, h x ^ 4) := by
    have h_cauchy_schwarz : ∀ (u v : BoolCube n → ℝ), (∑ x, u x * v x) ^ 2 ≤ (∑ x, u x ^ 2) * (∑ x, v x ^ 2) := by
      exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    convert h_cauchy_schwarz ( fun x => g x ^ 2 ) ( fun x => h x ^ 2 ) using 3 <;> ring;
  nlinarith [ show 0 ≤ uniformWeight n ^ 2 by positivity ]

/- Non-negativity of expect of squares -/
lemma expect_sq_nonneg {n : ℕ} (f : BooleanFunc n) :
    0 ≤ expect (fun x => f x ^ 2) := by
  exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )

/- Non-negativity of expect of products of squares -/
lemma expect_sq_nonneg_prod {n : ℕ} (g h : BooleanFunc n) :
    0 ≤ expect (fun x => g x ^ 2 * h x ^ 2) := by
  exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity )

/- Non-negativity of expect of fourth powers -/
lemma expect_fourth_nonneg {n : ℕ} (f : BooleanFunc n) :
    0 ≤ expect (fun x => f x ^ 4) := by
  convert expect_sq_nonneg_prod ( fun x => f x ^ 2 ) ( fun x => 1 ) using 1 ;
  norm_num [ sq ] ; ring_nf;

/- Degree bound for avgLast: if f has degree ≤ k, then avgLast f has degree ≤ k -/
lemma degree_avgLast {n : ℕ} (f : BooleanFunc (n + 1)) (k : ℕ)
    (hf : has_degree_at_most f k) :
    has_degree_at_most (avgLast f) k := by
  intro S hS_nonzero
  have h_fourier_coeff : fourierCoeff (avgLast f) S = fourierCoeff f (S.image Fin.castSucc) := by
    unfold fourierCoeff avgLast;
    unfold innerProduct restrictLast;
    unfold expect;
    -- By definition of $f$, we can expand the sum.
    have h_expand : ∑ x : BoolCube (n + 1), f x * chiS (Finset.image Fin.castSucc S) x = ∑ x : BoolCube n, (f (Fin.snoc x false) * chiS (Finset.image Fin.castSucc S) (Fin.snoc x false) + f (Fin.snoc x true) * chiS (Finset.image Fin.castSucc S) (Fin.snoc x true)) := by
      convert sum_boolCube_succ _;
      rw [ Finset.sum_add_distrib ];
    simp_all +decide [ Finset.sum_add_distrib, add_mul, mul_add, div_mul_eq_mul_div, Finset.mul_sum _ _ _];
    rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; unfold uniformWeight ; ring_nf;
    unfold chiS; simp +decide [ Finset.prod_image] ; ring;
  have := hf ( Finset.image Fin.castSucc S ) ;
  simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;

/-
Degree bound for diffLast: if f has degree ≤ k, then diffLast f has degree ≤ k-1
-/
lemma degree_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (k : ℕ)
    (hf : has_degree_at_most f k) :
    has_degree_at_most (diffLast f) (k - 1) := by
  have h_fourier_coeff : ∀ S : Finset (Fin n), fourierCoeff (diffLast f) S = fourierCoeff f (Finset.image (Fin.castSucc) S ∪ {Fin.last n}) := by
    intro S
    unfold diffLast fourierCoeff innerProduct
    simp [chiS];
    unfold restrictLast expect;
    rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Bool ) ) = Finset.image ( fun x : Fin n → Bool => Fin.snoc x false ) Finset.univ ∪ Finset.image ( fun x : Fin n → Bool => Fin.snoc x true ) Finset.univ from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_image, Finset.prod_mul_distrib ] ;
    ring_nf;
    · norm_num [ Fin.snoc ] ; ring_nf;
      ·
        norm_num [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf!;
        · norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, add_comm 1 n, uniformWeight_succ ];
          ring;
    · norm_num [ Finset.disjoint_left ];
    · ext x; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff];
      by_cases hx : x (Fin.last n) = false <;> [left; right] <;> use fun i => x (Fin.castSucc i) <;> ext i <;> cases i using Fin.lastCases <;> aesop;
  intro S hS_nonzero
  have h_card : S.card + 1 ≤ k := by
    have := hf ( Finset.image Fin.castSucc S ∪ { Fin.last n } ) ;
    simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
  exact Nat.le_sub_one_of_lt h_card

/- A degree-0 function is constant -/
lemma degree_zero_const {n : ℕ} (f : BooleanFunc n) (hf : has_degree_at_most f 0) :
    ∀ x, f x = f default := by
  intro x;
  -- By definition of $f$, we can write it as a sum of its Fourier coefficients.
  have h_fourier : f = fun x => ∑ S : Finset (Fin n), fourierCoeff f S * chiS S x := by
    exact funext fun x => walsh_expansion f x;
  rw [ h_fourier ];
  refine' Finset.sum_congr rfl fun S hS => _;
  by_cases h : fourierCoeff f S = 0 <;> simp +decide [ h ];
  specialize hf S h;
  simp_all +singlePass [ Finset.card_eq_zero ] ;

/- For a degree-0 (constant) function, E[f^4] = (E[f^2])^2 -/
lemma degree_zero_fourth_moment {n : ℕ} (f : BooleanFunc n) (hf : has_degree_at_most f 0) :
    expect (fun x => f x ^ 4) = (expect (fun x => f x ^ 2)) ^ 2 := by
  -- Since $f$ is constant, we have $f(x) = f(default)$ for all $x$.
  have h_const : ∀ x : BoolCube n, f x = f default := by
    exact fun x => degree_zero_const f hf x;
  unfold expect; simp +decide [ h_const ] ; ring_nf;
  unfold uniformWeight; norm_num [ pow_mul ] ; ring_nf;
  simp [ pow_mul' ]

/-
  Key algebraic inequality for the Bonami lemma inductive step.
  If A ≤ 9^(m+1) a², B ≤ 9^m b², C² ≤ A·B, and all are non-negative,
  then A + 6C + B ≤ 9^(m+1) (a+b)² -/
lemma bonami_algebra {m : ℕ} {a b A B C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hA_bound : A ≤ 9 ^ (m + 1) * a ^ 2)
    (hB_bound : B ≤ 9 ^ m * b ^ 2)
    (hC_bound : C ^ 2 ≤ A * B) :
    A + 6 * C + B ≤ 9 ^ (m + 1) * (a + b) ^ 2 := by
  -- By combining terms, we can factor out common factors and simplify the expression.
  ring_nf at *;
  nlinarith [ show 0 ≤ 9 ^ m by positivity, show 0 ≤ a * b * 9 ^ m by positivity, sq_nonneg ( C - a * b * 9 ^ m * 3 ), mul_le_mul_of_nonneg_left hB_bound ( show 0 ≤ 9 ^ m by positivity ) ]

/- The main Bonami lemma, proved without the k ≥ 1 assumption, in terms of expectation -/
lemma bonami_expect {n : ℕ} (k : ℕ) (f : BooleanFunc n)
    (hf : has_degree_at_most f k) :
    expect (fun x ↦ f x ^ 4) ≤ (9 : ℝ) ^ k * (expect (fun x ↦ f x ^ 2)) ^ 2 := by
  induction n generalizing k with
  | zero =>
    -- BoolCube 0 has one element, everything reduces to f(default)
    unfold expect;
    norm_num [ Finset.card_univ ] ; ring_nf ; norm_cast; norm_num;
    unfold uniformWeight; norm_num; ring_nf; norm_cast; norm_num;
    exact le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( by norm_num ) )
  | succ n ih =>
    by_cases hk : k = 0
    · -- k = 0: f is constant
      subst hk
      simp only [pow_zero, one_mul]
      exact le_of_eq (degree_zero_fourth_moment f hf)
    · -- k ≥ 1: write k = m + 1
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk
      -- Define g = avgLast f, h = diffLast f
      set g := avgLast f
      set hh := diffLast f
      -- Apply the decompositions
      rw [fourth_moment_decomp f, second_moment_decomp f]
      -- Get degree bounds
      have hg_deg : has_degree_at_most g (m + 1) := degree_avgLast f (m + 1) hf
      have hh_deg : has_degree_at_most hh m := by
        have := degree_diffLast f (m + 1) hf
        simp at this
        exact this
      -- Apply IH
      have hg_bound := ih (m + 1) g hg_deg
      have hh_bound := ih m hh hh_deg
      -- Get non-negativity
      have ha := expect_sq_nonneg g
      have hb := expect_sq_nonneg hh
      have hA := expect_fourth_nonneg g
      have hB := expect_fourth_nonneg hh
      -- Get Cauchy-Schwarz
      have hCS := expect_cs_sq g hh
      -- Apply the algebraic lemma
      set a := expect (fun x => g x ^ 2)
      set b := expect (fun x => hh x ^ 2)
      set A := expect (fun x => g x ^ 4)
      set B := expect (fun x => hh x ^ 4)
      set C := expect (fun x => g x ^ 2 * hh x ^ 2)
      have hC_nn : 0 ≤ C := expect_sq_nonneg_prod g hh
      exact bonami_algebra ha hb hB hC_nn hg_bound hh_bound hCS

lemma moment_eq_expect {n : ℕ} (f : BooleanFunc n) (p : ℕ)
    (P : Measure (BoolCube n)) [IsProbabilityMeasure P]
    (hP_unif : ∀ x, (P {x}).toReal = uniformWeight n) :
    moment f p P = expect (fun x ↦ f x ^ p) := by
  -- Expand the definition of moment
  rw [moment]

  -- Convert the discrete integral to a finite sum.
  -- With [IsProbabilityMeasure P] added, integral_fintype now perfectly matches!
  simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]

  -- Expand expect and push the constant uniform weight into the sum
  unfold expect
  rw [Finset.mul_sum]

  -- Show the inner terms are exactly equal
  apply Finset.sum_congr rfl
  intro x _
  have h_meas_x : (P.real {x}) = uniformWeight n := hP_unif x

  -- Substitute the uniform weight and rearrange
  rw [h_meas_x]

/-- The canonical uniform probability measure on the Boolean Hypercube. -/
noncomputable def uniformMeasure (n : ℕ) : Measure (BoolCube n) :=
  (PMF.uniformOfFintype (BoolCube n)).toMeasure

instance (n : ℕ) : IsProbabilityMeasure (uniformMeasure n) := by
  -- Unfold the definition so Lean sees the underlying `PMF.toMeasure`
  unfold uniformMeasure
  -- Now Lean can automatically find the PMF probability measure instance!
  infer_instance

/-- Prove that our canonical measure matches the combinatorial uniformWeight. -/
lemma uniformMeasure_apply {n : ℕ} (x : BoolCube n) :
    ((uniformMeasure n) {x}).toReal = uniformWeight n := by
  -- Unfold the definitions
  dsimp [uniformMeasure]
  rw [PMF.toMeasure_apply_singleton]

  -- Evaluate the PMF application.
  -- This creates the `if` statement, which we immediately simplify
  -- because `x ∈ Finset.univ` is always true.
  simp only [PMF.uniformOfFintype_apply]

  -- Now we have an inverse `⁻¹`, so we use `toReal_inv` instead of `toReal_div`
  rw [ENNReal.toReal_inv]

  -- Calculate the cardinality of `BoolCube n` (which is `Fin n → Bool`).
  -- Fintype.card automatically turns this into 2^n.
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

  -- At this point, the goal is `( (2^n : ℕ) : ℝ )⁻¹ = uniformWeight n`.
  -- We unfold uniformWeight and use basic algebra/simp to close the goal.
  unfold uniformWeight
  rw[ENNReal.toReal_natCast]
  simp only [Nat.cast_pow, Nat.cast_ofNat, inv_pow]
  exact MeasurableSet.singleton x

/--
`The Bonami Lemma:`
`A Boolean function of degree at most k is 9^k-reasonable under the uniform measure.`
-/
lemma bonami_lemma {n : ℕ} (k : ℕ) (f : BooleanFunc n)
    (hf : has_degree_at_most f k) :
    IsBReasonable f (uniformMeasure n) ((9 : ℝ) ^ k) := by

  -- 1. Unfold your B-reasonability definition
  rw [IsBReasonable]

  -- 2. Use the bridge lemma specifically on the uniformMeasure
  rw [moment_eq_expect f 4 (uniformMeasure n) uniformMeasure_apply]
  rw [moment_eq_expect f 2 (uniformMeasure n) uniformMeasure_apply]

  -- 3. Apply the purely algebraic expectation bound
  exact bonami_expect k f hf

/-! ## (2,4)-Hypercontractivity Theorem -/

/-
Fourier coefficient of avgLast:
  `(avgLast f)^(S) = f̂(S.image castSucc)`.
-/
lemma fourierCoeff_avgLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (avgLast f) S = fourierCoeff f (S.image Fin.castSucc) := by
  unfold avgLast; simp +decide only [fourierCoeff] ; ring_nf;
  unfold innerProduct; simp +decide only [one_div, mul_comm] ; ring_nf;
  unfold expect; simp +decide only [chiS, restrictLast, one_div, mul_comm, Finset.sum_add_distrib,
    Fin.castSucc_inj, implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Finset.mul_sum _ _ _,
    mul_left_comm] ; ring_nf;
  rw [ add_comm 1 n, uniformWeight_succ ] ; rw [ ← mul_add ] ; rw [ sum_boolCube_succ ] ; ring_nf;
  simp +decide [mul_comm, mul_left_comm, Finset.mul_sum _ _ _]

/-
Fourier coefficient of diffLast:
  `(diffLast f)^(S) = f̂(S.image castSucc ∪ {last n})`.
-/
lemma fourierCoeff_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (diffLast f) S = fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n}) := by
  -- By definition of `diffLast`, we have that `diffLast f(x) = (f(snoc x false) - f(snoc x true)) / 2`.
  unfold diffLast;
  unfold fourierCoeff innerProduct expect chiS;
  rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Bool ) ) = Finset.image ( fun x : Fin n → Bool => Fin.snoc x false ) Finset.univ ∪ Finset.image ( fun x : Fin n → Bool => Fin.snoc x true ) Finset.univ from ?_, Finset.sum_union ] <;> norm_num;
  ·
    · norm_num [ Finset.sum_add_distrib, sub_mul, div_mul_eq_mul_div, Finset.mul_sum _ _ _, Finset.sum_div, uniformWeight_succ ] ; ring_nf;
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, restrictLast ];
  · norm_num [ Finset.disjoint_left ];
  · ext x; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff];
    by_cases hx : x ( Fin.last n ) = Bool.false <;> [ left; right ] <;> use fun i => x i.castSucc <;> ext i <;> cases i using Fin.lastCases <;> aesop

/-
`χ_{S.image castSucc}(Fin.snoc x b) = χ_S(x)`: the character of a "lifted" set
  ignores the last coordinate.
-/
lemma chiS_snoc_castSucc {n : ℕ} (S : Finset (Fin n)) (x : BoolCube n) (b : Bool) :
    chiS (S.image Fin.castSucc) (Fin.snoc x b) = chiS S x := by
  unfold chiS; aesop;

/-
`χ_{S.image castSucc ∪ {last n}}(Fin.snoc x b) = boolToSign b * χ_S(x)`.
-/
lemma chiS_snoc_with_last {n : ℕ} (S : Finset (Fin n)) (x : BoolCube n) (b : Bool) :
    chiS (S.image Fin.castSucc ∪ {Fin.last n}) (Fin.snoc x b) = boolToSign b * chiS S x := by
  unfold chiS; simp +decide only [Finset.union_singleton, Finset.mem_image, Fin.castSucc_ne_last,
    and_false, exists_false, not_false_eq_true, Finset.prod_insert, Fin.snoc_last, Fin.castSucc_inj,
    implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Fin.snoc_castSucc] ;

/-
Partition of `∑ S : Finset (Fin (n+1))` by membership of `Fin.last n`:
  every subset of `[n+1]` either avoids or contains the last element.
-/
lemma finset_fin_succ_sum_partition {n : ℕ} (φ : Finset (Fin (n + 1)) → ℝ) :
    ∑ S : Finset (Fin (n + 1)), φ S =
    ∑ T : Finset (Fin n), φ (T.image Fin.castSucc) +
    ∑ T : Finset (Fin n), φ (T.image Fin.castSucc ∪ {Fin.last n}) := by
  -- We partition Finset (Fin (n+1)) by whether Fin.last n is in the set.
  have h_partition : Finset.univ = Finset.image (fun T : Finset (Fin n) => T.image Fin.castSucc) (Finset.univ : Finset (Finset (Fin n))) ∪ Finset.image (fun T : Finset (Fin n) => T.image Fin.castSucc ∪ {Fin.last n}) (Finset.univ : Finset (Finset (Fin n))) := by
    ext S;
    by_cases h : Fin.last n ∈ S <;> simp +decide only [Finset.mem_univ, Finset.union_singleton,
      Finset.mem_union, Finset.mem_image, true_and, true_iff];
    · refine Or.inr ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ S, ?_ ⟩;
      ext i; simp [Finset.mem_insert, Finset.mem_image];
      exact ⟨ fun hi => hi.elim ( fun hi => hi.symm ▸ h ) fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁, fun hi => if hi' : i = Fin.last n then Or.inl hi' else Or.inr ⟨ ⟨ i.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hi' ) ⟩, by simpa [ Fin.ext_iff ] using hi, rfl ⟩ ⟩;
    · refine' Or.inl ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ S, _ ⟩;
      ext i; simp [Finset.mem_image];
      exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁, fun hi => by cases i using Fin.lastCases <;> aesop ⟩;
  rw [ h_partition, Finset.sum_union ] <;> norm_num [ Finset.disjoint_right ];
  · rw [ Finset.sum_image, Finset.sum_image ];
    · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_eq ( Fin.castSucc a ) ; aesop;
    · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_eq ( Fin.castSucc a ) ; aesop;
  · intro a x H; replace H := Finset.ext_iff.mp H ( Fin.last n ) ; simp +decide at H;

/-- Cardinality of a lifted set: `|S.image castSucc| = |S|`. -/
lemma card_image_castSucc {n : ℕ} (S : Finset (Fin n)) :
    (S.image Fin.castSucc).card = S.card := by
  exact Finset.card_image_of_injective S (Fin.castSucc_injective n)

/-
Cardinality: `|S.image castSucc ∪ {last n}| = |S| + 1`.
-/
lemma card_image_castSucc_union_last {n : ℕ} (S : Finset (Fin n)) :
    (S.image Fin.castSucc ∪ {Fin.last n}).card = S.card + 1 := by
  rw [ Finset.card_union, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]

/-
The noise operator decomposes along the last coordinate:
  `T_ρ f(snoc x b) = T_ρ(avgLast f)(x) + boolToSign(b) · ρ · T_ρ(diffLast f)(x)`.
-/
lemma noiseOp_snoc {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) (x : BoolCube n) (b : Bool) :
    noiseOp ρ f (Fin.snoc x b) =
    noiseOp ρ (avgLast f) x + boolToSign b * ρ * noiseOp ρ (diffLast f) x := by
  convert finset_fin_succ_sum_partition ( fun S ↦ ρ ^ S.card * fourierCoeff f S * chiS S ( Fin.snoc x b ) ) using 1;
  congr! 1;
  · refine' Finset.sum_congr rfl fun T _ => _;
    rw [ ← fourierCoeff_avgLast ];
    rw [ card_image_castSucc, chiS_snoc_castSucc ];
  · rw [ show noiseOp ρ ( diffLast f ) x = ∑ T : Finset ( Fin n ), ρ ^ T.card * fourierCoeff ( diffLast f ) T * chiS T x from rfl ];
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun T hT => _ ; rw [ fourierCoeff_diffLast ] ; rw [ card_image_castSucc_union_last ] ; ring_nf;
    rw [ chiS_snoc_with_last ] ; ring

/-
Fourth moment decomposition with the noise operator.
-/
lemma fourth_moment_noise_decomp {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) :
    expect (fun x => (noiseOp ρ f x) ^ 4) =
    expect (fun x => (noiseOp ρ (avgLast f) x) ^ 4) +
    6 * ρ ^ 2 * expect (fun x => (noiseOp ρ (avgLast f) x) ^ 2 * (noiseOp ρ (diffLast f) x) ^ 2) +
    ρ ^ 4 * expect (fun x => (noiseOp ρ (diffLast f) x) ^ 4) := by
  field_simp;
  convert fourth_moment_decomp ( fun x => noiseOp ρ f x ) using 2;
  · unfold avgLast diffLast; ring_nf;
    unfold restrictLast; norm_num [ noiseOp_snoc ] ; ring_nf;
    unfold avgLast diffLast; norm_num [ mul_assoc ] ;
    unfold restrictLast; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
    unfold expect; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  · unfold diffLast;
    unfold restrictLast; norm_num [ noiseOp_snoc ] ; ring_nf;
    unfold diffLast; norm_num [ expect ] ; ring_nf;
    unfold restrictLast; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;

/-
Helper: C² ≤ a²b² and C ≥ 0 implies C ≤ ab (for a,b ≥ 0).
-/
lemma sq_le_sq_mul_of_nonneg {C a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : C ^ 2 ≤ a ^ 2 * b ^ 2) : C ≤ a * b := by
  nlinarith [ mul_nonneg ha hb ]

/-
Helper: a² + 6ρ²ab + ρ⁴b² ≤ (a+b)² when ρ² ≤ 1/3 and a,b ≥ 0.
-/
lemma hypercontractivity_algebra_simple {a b ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : ρ ^ 2 ≤ 1 / 3) :
    a ^ 2 + 6 * ρ ^ 2 * (a * b) + ρ ^ 4 * b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [ sq_nonneg ( a - b ), mul_nonneg ha hb, mul_le_mul_of_nonneg_left hρ ( sq_nonneg a ), mul_le_mul_of_nonneg_left hρ ( sq_nonneg b ) ]

/-- Key algebraic inequality: under `ρ² ≤ 1/3`, the recurrence closes. -/
lemma hypercontractivity_algebra' {a b A B C ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA_nn : 0 ≤ A) (hB_nn : 0 ≤ B) (hC : 0 ≤ C)
    (hA_bound : A ≤ a ^ 2) (hB_bound : B ≤ b ^ 2)
    (hC_bound : C ^ 2 ≤ A * B) (hρ : ρ ^ 2 ≤ 1 / 3) :
    A + 6 * ρ ^ 2 * C + ρ ^ 4 * B ≤ (a + b) ^ 2 := by
  have hC_le : C ≤ a * b := by
    apply sq_le_sq_mul_of_nonneg ha hb
    calc C ^ 2 ≤ A * B := hC_bound
      _ ≤ a ^ 2 * b ^ 2 := mul_le_mul hA_bound hB_bound hB_nn (sq_nonneg a)
  calc A + 6 * ρ ^ 2 * C + ρ ^ 4 * B
      ≤ a ^ 2 + 6 * ρ ^ 2 * (a * b) + ρ ^ 4 * b ^ 2 := by
        have h2 : 6 * ρ ^ 2 * C ≤ 6 * ρ ^ 2 * (a * b) :=
          mul_le_mul_of_nonneg_left hC_le (by positivity)
        have h3 : ρ ^ 4 * B ≤ ρ ^ 4 * b ^ 2 :=
          mul_le_mul_of_nonneg_left hB_bound (by positivity)
        linarith
    _ ≤ (a + b) ^ 2 := hypercontractivity_algebra_simple ha hb hρ

/--
**The (2,4)-Hypercontractivity Theorem** (Bonami–Beckner):
For any Boolean function `f : {0,1}ⁿ → ℝ` and noise parameter `ρ` with `ρ² ≤ 1/3`
(i.e., `|ρ| ≤ 1/√3`),
  `𝔼[(T_ρ f)⁴] ≤ (𝔼[f²])²`,
or equivalently `‖T_ρ f‖₄ ≤ ‖f‖₂`.
-/
theorem hypercontractivity_2_4 {n : ℕ} (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 4) ≤ (expect (fun x => f x ^ 2)) ^ 2 := by
  induction n with
  | zero =>
  unfold expect;
  unfold uniformWeight; norm_num;
  unfold noiseOp; ring_nf;
  erw [ Finset.sum_eq_single ∅ ] <;> norm_num;
  · unfold fourierCoeff;
    unfold innerProduct expect; norm_num [ Fin.eq_zero ] ;
    unfold uniformWeight; norm_num;
  · exact fun h => False.elim <| h rfl;
  · exact fun h => False.elim <| h rfl
  | succ n ih =>
    rw [fourth_moment_noise_decomp, second_moment_decomp]
    exact hypercontractivity_algebra'
      (expect_sq_nonneg (avgLast f))
      (expect_sq_nonneg (diffLast f))
      (expect_fourth_nonneg (noiseOp ρ (avgLast f)))
      (expect_fourth_nonneg (noiseOp ρ (diffLast f)))
      (expect_sq_nonneg_prod (noiseOp ρ (avgLast f)) (noiseOp ρ (diffLast f)))
      (ih (avgLast f))
      (ih (diffLast f))
      (expect_cs_sq (noiseOp ρ (avgLast f)) (noiseOp ρ (diffLast f)))
      hρ

/- **The (4 / 3, 2)-Hypercontractivity Theorem** :-/

/-- Hölder's inequality for p = 4/3 and q = 4. -/
lemma innerProduct_le_L43_L4 (f g : BooleanFunc n) :
  innerProduct f g ≤
  (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) *
  (expect (fun x => |g x| ^ 4)) ^ (1/4 : ℝ) := by
    -- Step 1: Expand definitions
  unfold innerProduct expect uniformWeight

  -- Step 2: Push the absolute value inside to bound the sum
  -- f * g ≤ |f * g| = |f| * |g|
  have h_abs : ∑ x : BoolCube n, f x * g x ≤ ∑ x : BoolCube n, |f x| * |g x| := by
    apply Finset.sum_le_sum
    intro x _
    calc
      f x * g x ≤ |f x * g x| := le_abs_self _
      _ = |f x| * |g x| := abs_mul _ _

  -- Step 3: Multiply by the uniform weight (2⁻ⁿ)
  have h_weight_abs :
      (2⁻¹ : ℝ) ^ n * ∑ x : BoolCube n, f x * g x ≤
      (2⁻¹ : ℝ) ^ n * ∑ x : BoolCube n, |f x| * |g x| := by
    apply mul_le_mul_of_nonneg_left h_abs
    positivity

  -- Step 4: Setup conjugate exponents for Hölder's inequality
  let p : ℝ := 4/3
  let q : ℝ := 4
  have hpq : HolderConjugate p q := by
    constructor
    · norm_num -- Proves 1 < p (since 4/3 > 1)
    · norm_num
    · norm_num

  -- Step 5: Apply Hölder's Inequality for sums
  -- Mathlib has theorems like `Real.inner_le_Lp_Lq_of_nonneg` or `Real.sum_mul_le_rpow_mul_rpow`
  -- We will bound the sum of |f| * |g|.
  have holder_sum : ∑ x : BoolCube n, |f x| * |g x| ≤
      (∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q) := by
    -- You may need to adapt this exact lemma name depending on your Mathlib version.
    -- If using NNReal, you would map `|f x|` to NNReal first.
    refine inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq ?_ ?_
    · exact fun i a => abs_nonneg (f i)
    · exact fun i a => abs_nonneg (g i)

  -- Step 6: Distribute the uniform weight into the powers
  have weight_split : (2⁻¹ : ℝ) ^ n = ((2⁻¹ : ℝ) ^ n) ^ (1/p) * ((2⁻¹ : ℝ) ^ n) ^ (1/q) := by
    have hpq_sum : (1/p : ℝ) + (1/q : ℝ) = 1 := by norm_num
    rw [← Real.rpow_add (by positivity), hpq_sum, Real.rpow_one]

  -- Now string it all together
  calc
    (2⁻¹ : ℝ) ^ n * ∑ x, f x * g x
      ≤ (2⁻¹ : ℝ) ^ n * ∑ x, |f x| * |g x| := h_weight_abs
    _ ≤ (2⁻¹ : ℝ) ^ n * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q)) := by
      apply mul_le_mul_of_nonneg_left holder_sum (by positivity)
    _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by
      -- Use nth_rw to ONLY rewrite the very first instance of 2⁻¹ ^ n
      calc
        (2⁻¹ : ℝ) ^ n * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q))
          = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * ((2⁻¹ : ℝ) ^ n) ^ (1/q)) * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q)) := by nth_rw 1 [weight_split]
        _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by ring
        _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by ring
    _ = ((2⁻¹ : ℝ) ^ n * ∑ x, |f x| ^ p) ^ (1/p) * ((2⁻¹ : ℝ) ^ n * ∑ x, |g x| ^ q) ^ (1/q) := by
      -- Real.mul_rpow requires proofs that the inner sums are non-negative
      have hfp : 0 ≤ ∑ x : BoolCube n, |f x| ^ p := Finset.sum_nonneg (fun x _ => by positivity)
      have hgq : 0 ≤ ∑ x : BoolCube n, |g x| ^ q := Finset.sum_nonneg (fun x _ => by positivity)
      rw [← Real.mul_rpow (by positivity) hfp]
      rw [← Real.mul_rpow (by positivity) hgq]
    _ = (2⁻¹ ^ n * ∑ x, (fun x => |f x| ^ (4 / 3 : ℝ)) x) ^ (3 / 4 : ℝ) * (2⁻¹ ^ n * ∑ x, (fun x => |g x| ^ 4) x) ^ (1 / 4 : ℝ) := by
     -- 1. Prove the outer fraction arithmetic
      have hp_exp : (1 / p : ℝ) = 3 / 4 := by norm_num
      have hq_exp : (1 / q : ℝ) = 1 / 4 := by norm_num
      rw [hp_exp, hq_exp]
      -- 2. Fix the invisible rpow vs npow mismatch for q = 4
      have hq_pow : ∀ x, |g x| ^ q = |g x| ^ 4 := by
        intro x
        -- Reveal that q is (4 : ℝ) and the target is (4 : ℕ)
        change |g x| ^ (4 : ℝ) = |g x| ^ (4 : ℕ)
        -- Apply the Mathlib lemma that links Real powers to Nat powers
        exact Real.rpow_natCast (|g x|) 4
      -- 3. Rewrite the power inside the sum
      simp_rw [hq_pow]
      -- 4. Now rfl perfectly matches everything structurally!
      rfl

/-**The (4 / 3, 2)-Hypercontractivity Theorem** :
For any Boolean function `f : {0,1}ⁿ → ℝ` and noise parameter `ρ` with `ρ² ≤ 1/3`
(i.e., `|ρ| ≤ 1/√3`),
  `𝔼[(T_ρ f)⁴] ≤ (𝔼[f²])²`,
or equivalently `‖T_ρ f‖₄ ≤ ‖f‖₂`. -/
theorem hypercontractivity_4_div_3_2 {n : ℕ} (f : BooleanFunc n) :
    (expect (fun x => (noiseOp (1 / Real.sqrt 3) f x) ^ 2)) ^ (1/2 : ℝ)
    ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) := by

  -- 1. Setup the constant ρ
  set ρ := 1 / Real.sqrt 3
  have hρ : ρ ^ 2 ≤ 1 / 3 := by
    dsimp [ρ]
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]
    simp only [one_div, le_refl]

  -- 2. Define E_2 as the squared L2 norm for cleaner reading
  set E_2 := expect (fun x => (noiseOp ρ f x) ^ 2)
  have hE2_nonneg : 0 ≤ E_2 := by
    unfold E_2 expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  -- 3. Handle the trivial case where T_ρ f is 0 to avoid dividing by zero later
  by_cases h_zero : E_2 = 0
  · rw [h_zero]
    have h_zero_pow : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 := by norm_num
    rw [h_zero_pow]
    -- The right side is a non-negative expectation
    apply Real.rpow_nonneg
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  -- 4. Establish that E_2 is strictly positive for division later
  have hE2_pos : 0 < E_2 := lt_of_le_of_ne hE2_nonneg (Ne.symm h_zero)

  -- 5. Helper lemmas for the calc block
  have h_inner_eq : innerProduct (noiseOp ρ f) (noiseOp ρ f) = E_2 := by
    unfold innerProduct E_2 expect
    simp_rw [sq]

  have h_abs_four : expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ 4) = expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4) := by
    apply congr_arg
    ext x
    -- Prove |y|^4 = y^4 using squares
    calc |noiseOp ρ (noiseOp ρ f) x| ^ 4
      _ = (|noiseOp ρ (noiseOp ρ f) x| ^ 2) ^ 2 := by ring
      _ = (noiseOp ρ (noiseOp ρ f) x ^ 2) ^ 2 := by rw [sq_abs]
      _ = noiseOp ρ (noiseOp ρ f) x ^ 4 := by ring

  -- 6. Bring in the (2,4) hypercontractivity bound
  have hc_2_4 := hypercontractivity_2_4 ρ hρ (noiseOp ρ f)

-- 7. The Core Duality Argument

  -- Helper 1: The L4/3 norm expectation is non-negative
  have h_f_L43_nonneg : 0 ≤ expect (fun x => |f x| ^ (4 / 3 : ℝ)) := by
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  -- Helper 2: The L4 norm expectation of the noiseOp is non-negative
  have h_hc_lhs_nonneg : 0 ≤ expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4) := by
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  have main_bound : E_2 ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1/2 : ℝ) := by
    calc
      E_2 = innerProduct (noiseOp ρ f) (noiseOp ρ f) := h_inner_eq.symm
      _ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := by
        rw [noiseOp_self_adjoint]
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ 4)) ^ (1/4 : ℝ) := by
        apply innerProduct_le_L43_L4
      _ = (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4)) ^ (1/4 : ℝ) := by
        rw [h_abs_four]
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (E_2 ^ 2) ^ (1/4 : ℝ) := by
        -- Use our explicit proofs instead of relying on `by positivity`
        apply mul_le_mul_of_nonneg_left
        · apply Real.rpow_le_rpow h_hc_lhs_nonneg hc_2_4 (by norm_num)
        · exact Real.rpow_nonneg h_f_L43_nonneg (3 / 4 : ℝ)
      _ = (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1/2 : ℝ) := by
        congr 1
        -- Convert the inner Nat power to a Real power
        have h_nat_real : E_2 ^ (2 : ℕ) = E_2 ^ (2 : ℝ) := (Real.rpow_natCast E_2 2).symm
        rw [h_nat_real]
        -- Now both powers are Real, so we can multiply them
        rw [← Real.rpow_mul hE2_nonneg]
        norm_num

-- 8. Extract the final result by dividing out E_2^(1/2)
  -- Prove that E_2^(1/2) * E_2^(1/2) = E_2
  have h_split : E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) = E_2 := by
    rw [← Real.rpow_add hE2_pos]
    norm_num

  -- Securely attach the split left side to our main bound without touching the right side
  have main_bound_split : E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1 / 2 : ℝ) := by
    calc
      E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) = E_2 := h_split
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1 / 2 : ℝ) := main_bound

  -- Since A * C ≤ B * C and C > 0, then A ≤ B
  have hE2_half_pos : 0 < E_2 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hE2_pos (1 / 2 : ℝ)
  exact le_of_mul_le_mul_right main_bound_split hE2_half_pos
end

/-! ## Contractivity of the noise operator (q = 2 case) -/

/-- The L² norm of `T_ρ f` in Fourier space:
`𝔼[(T_ρ f)²] = ∑_S ρ^{2|S|} f̂(S)²`. -/
lemma noise_l2_fourier (ρ : ℝ) (f : BooleanFunc n) :
    innerProduct (noiseOp ρ f) (noiseOp ρ f) =
    ∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * fourierCoeff f S ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro S _
  rw [noiseOp_fourier]
  ring

/-- **Contractivity**: `𝔼[(T_ρ f)²] ≤ 𝔼[f²]` for `ρ² ≤ 1`.
This is the `q = 2` case of hypercontractivity. -/
theorem contractivity (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 2) ≤ expect (fun x => f x ^ 2) := by
  have lhs : expect (fun x => (noiseOp ρ f x) ^ 2) =
      innerProduct (noiseOp ρ f) (noiseOp ρ f) := by
    simp [innerProduct, sq]
  have rhs : expect (fun x => f x ^ 2) = innerProduct f f := by
    simp [innerProduct, sq]
  rw [lhs, rhs, noise_l2_fourier, parseval]
  apply Finset.sum_le_sum
  intro S _
  have h1 : (ρ ^ S.card) ^ 2 = (ρ ^ 2) ^ S.card := by ring
  rw [h1]
  apply mul_le_of_le_one_left (sq_nonneg _)
  exact pow_le_one₀ (sq_nonneg ρ) hρ

/-! ## Combinatorial inequality -/

/-
**Key combinatorial bound**: `C(2k, 2j) ≤ C(k, j) · (2k - 1)^j`.

This is proved by induction on `j`. The induction step shows
`C(2k, 2j) / C(2k, 2(j-1)) · 1/((2k-1) · C(k,j)/C(k,j-1))` ≤ 1,
which reduces to `(2k - 2j + 1) ≤ (2k - 1)(2j - 1)` for `j ≥ 1`.
-/
lemma binom_coeff_ineq (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) :
    Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
  induction j with
  | zero =>
    norm_num;
  | succ j ih => -- By the induction hypothesis, we have `C(2k, 2j) ≤ C(k, j) · (2k-1)^j`.
    have h_ind : Nat.choose (2 * k) (2 * j + 2) ≤ Nat.choose (2 * k) (2 * j) * ((2 * k - 2 * j) * (2 * k - 2 * j - 1)) / ((2 * j + 2) * (2 * j + 1)) := by
      rw [ Nat.le_div_iff_mul_le ];
      · have := Nat.choose_succ_right_eq ( 2 * k ) ( 2 * j );
        have := Nat.choose_succ_right_eq ( 2 * k ) ( 2 * j + 1 );
        rw [ show 2 * k - 2 * j - 1 = 2 * k - ( 2 * j + 1 ) by omega ];
        nlinarith [ Nat.sub_add_cancel ( by linarith : 2 * j ≤ 2 * k ), Nat.sub_add_cancel ( by linarith : 2 * j + 1 ≤ 2 * k ) ];
      · positivity;
    have h_ind_step : Nat.choose (2 * k) (2 * j) * ((2 * k - 2 * j) * (2 * k - 2 * j - 1)) ≤ Nat.choose k j * (2 * k - 1) ^ j * (k - j) * (2 * k - 1) * (2 * j + 2) := by
      have h_ind_step : (2 * k - 2 * j) * (2 * k - 2 * j - 1) ≤ (k - j) * (2 * k - 1) * (2 * j + 2) := by
        zify [ ← mul_tsub ];
        repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat linarith;
        · nlinarith [ sq ( k - j : ℤ ), sq ( j : ℤ ) ];
        · omega;
      simpa only [ mul_assoc ] using Nat.mul_le_mul ( ih ( Nat.le_of_succ_le hj ) ) h_ind_step;
    have h_final : Nat.choose k j * (k - j) * (2 * k - 1) * (2 * j + 2) ≤ Nat.choose k (j + 1) * (2 * k - 1) * (2 * j + 2) * (2 * j + 1) := by
      have h_final : Nat.choose k j * (k - j) ≤ Nat.choose k (j + 1) * (2 * j + 1) := by
        rw [← Nat.choose_succ_right_eq k j]
        apply Nat.mul_le_mul_left
        omega
      nlinarith only [ h_final, show 0 ≤ ( 2 * k - 1 ) * ( 2 * j + 2 ) by positivity ];
    refine le_trans h_ind ?_;
    refine Nat.div_le_of_le_mul ?_;
    refine le_trans h_ind_step ?_;
    convert Nat.mul_le_mul_right ( ( 2 * k - 1 ) ^ j ) h_final using 1 <;> ring

/-! ## Two-point inequality for even powers -/

/-
**Two-point inequality**: for `ρ² ≤ 1/(2k − 1)`:
`(α + ρβ)^{2k} + (α − ρβ)^{2k} ≤ 2 · (α² + β²)^k`.

The proof compares the binomial expansions term by term, using `binom_coeff_ineq`.
-/
lemma two_point_ineq (k : ℕ) (hk : 1 ≤ k)
    (α β ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) :
    (α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k) ≤
    2 * (α ^ 2 + β ^ 2) ^ k := by
  -- By the binomial theorem, we expand both sides.
  have h_expand : (α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k) = 2 * ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * α ^ (2 * k - 2 * j) * (ρ ^ 2 * β ^ 2) ^ j := by
    have h_expand : (α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (ρ * β) ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (-ρ * β) ^ j := by
      exact congrArg₂ ( · + · ) ( by rw [ add_comm, add_pow ] ; congr; ext; ring ) ( by rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr; ext; ring );
    -- Combine like terms in the binomial expansion.
    have h_combine : ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (ρ * β) ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (-ρ * β) ^ j = ∑ j ∈ Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * k + 1)), Nat.choose (2 * k) j * α ^ (2 * k - j) * (ρ ^ 2 * β ^ 2) ^ (j / 2) * 2 := by
      rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_filter ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] ; ring;
    -- Notice that Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * k + 1)) is equivalent to Finset.image (fun j => 2 * j) (Finset.range (k + 1)).
    have h_filter : Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * k + 1)) = Finset.image (fun j => 2 * j) (Finset.range (k + 1)) := by
      ext j
      simp [Finset.mem_filter, Finset.mem_image];
      exact ⟨ fun h => ⟨ j / 2, by linarith [ Nat.mod_add_div j 2 ], by linarith [ Nat.mod_add_div j 2 ] ⟩, by rintro ⟨ a, ha, rfl ⟩ ; exact ⟨ by linarith, by norm_num ⟩ ⟩;
    simp_all +decide [ mul_assoc, mul_comm, Finset.mul_sum _ _ _ ];
  have h_expand_rhs : (α ^ 2 + β ^ 2) ^ k = ∑ j ∈ Finset.range (k + 1), Nat.choose k j * α ^ (2 * k - 2 * j) * β ^ (2 * j) := by
    rw [ add_comm, add_pow ] ; congr ; ext ; ring_nf;
    rw [ tsub_mul ];
  -- Apply the inequality term by term to the sums.
  have h_term_by_term : ∀ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * (ρ ^ 2) ^ j ≤ Nat.choose k j := by
    intros j hj
    have h_term : Nat.choose (2 * k) (2 * j) * (ρ ^ 2) ^ j ≤ Nat.choose k j * (2 * k - 1) ^ j * (ρ ^ 2) ^ j := by
      have h_term : Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
        convert binom_coeff_ineq k hk j ( Finset.mem_range_succ_iff.mp hj ) using 1;
      exact mul_le_mul_of_nonneg_right ( by rw [ ← @Nat.cast_le ℝ ] at *; cases k <;> norm_num at * ; linarith ) ( by positivity );
    refine le_trans h_term ?_;
    rw [ mul_assoc ];
    exact mul_le_of_le_one_right ( Nat.cast_nonneg _ ) ( by rw [ ← mul_pow ] ; exact pow_le_one₀ ( by exact mul_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( sq_nonneg _ ) ) ( by rw [ le_div_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) );
  rw [ h_expand, h_expand_rhs ];
  refine' mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun j hj => _ ) zero_le_two;
  convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( h_term_by_term j hj ) ( show 0 ≤ α ^ ( 2 * k - 2 * j ) by rw [ show α ^ ( 2 * k - 2 * j ) = ( α ^ 2 ) ^ ( k - j ) by rw [ ← pow_mul, Nat.mul_sub_left_distrib ] ] ; positivity ) ) ( show 0 ≤ β ^ ( 2 * j ) by rw [ pow_mul ] ; positivity ) using 1 ; ring

/-- Two-point inequality, averaged form (dividing by 2). -/
lemma two_point_ineq_avg (k : ℕ) (hk : 1 ≤ k)
    (α β ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) :
    ((α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k)) / 2 ≤
    (α ^ 2 + β ^ 2) ^ k := by
  have h := two_point_ineq k hk α β ρ hρ
  linarith

/-! ## Moment decomposition for even powers -/

/-- For even q, the q-th moment decomposes using avgLast and diffLast. -/
lemma qth_moment_decomp (q : ℕ) (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ q) =
    expect (fun x' => ((avgLast f x' + diffLast f x') ^ q +
                       (avgLast f x' - diffLast f x') ^ q) / 2) := by
  unfold expect; rw [uniformWeight_succ];
  rw [show (∑ x : BoolCube (n + 1), f x ^ q) = ∑ x : BoolCube n, f (Fin.snoc x Bool.false) ^ q + ∑ x : BoolCube n, f (Fin.snoc x Bool.true) ^ q from ?_];
  · unfold avgLast diffLast; norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div]; ring_nf;
    norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]; ring_nf; rfl;
  · exact sum_boolCube_succ fun x => f x ^ q

/-- The noise operator decomposes on (n+1)-cubes for q-th moments. -/
lemma noise_qth_moment_decomp (q : ℕ) (ρ : ℝ) (f : BooleanFunc (n + 1)) :
    expect (fun x => (noiseOp ρ f x) ^ q) =
    expect (fun x' => ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ q +
                       (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ q) / 2) := by
  convert (qth_moment_decomp q (noiseOp ρ f)) using 3;
  rw [show avgLast (noiseOp ρ f) = noiseOp ρ (avgLast f) from ?_,
      show diffLast (noiseOp ρ f) = ρ • noiseOp ρ (diffLast f) from ?_]; ring_nf!;
  · norm_num [Algebra.smul_def];
  · ext x; exact (by
    convert congr_arg (fun y => (y - (noiseOp ρ f (Fin.snoc x true))) / 2)
      (noiseOp_snoc ρ f x false) using 1; norm_num; ring_nf!;
    rw [show noiseOp ρ f (Fin.snoc x true) =
      noiseOp ρ (avgLast f) x + boolToSign true * ρ * noiseOp ρ (diffLast f) x
      from noiseOp_snoc ρ f x true]; norm_num; ring!;);
  · funext x; simp [avgLast, noiseOp]; unfold restrictLast; ring_nf;
    rw [noiseOp_snoc, noiseOp_snoc]; norm_num; ring!;

/-! ## The main (2, 2k)-Hypercontractivity Theorem -/

/-
**The (2, 2k)-Hypercontractivity Theorem** (Bonami–Beckner):

For any Boolean function `f : {0,1}ⁿ → ℝ`, integer `k ≥ 1`,
and noise parameter `ρ` with `ρ² ≤ 1/(2k − 1)`:

`𝔼[(T_ρ f)^{2k}] ≤ (𝔼[f²])^k`.

Equivalently, `‖T_ρ f‖_{2k} ≤ ‖f‖₂`.

The proof is by induction on the dimension `n` of the Boolean cube.

**Induction step** (sketch):
1. Decompose using `noise_qth_moment_decomp` into terms involving `T_ρ(avgLast f)` and
   `T_ρ(diffLast f)`.
2. Apply the `two_point_ineq` pointwise: each summand is bounded by
   `(T_ρg(x')² + T_ρh(x')²)^k`.
3. Expand `(T_ρg² + T_ρh²)^k` via the binomial theorem.
4. Bound each mixed moment `𝔼[T_ρg^{2i} · T_ρh^{2(k−i)}]` using
   generalized Hölder + the induction hypothesis.
5. Reassemble using `binom_coeff_ineq` and `second_moment_decomp`.
-/
theorem hypercontractivity_2_2k (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ (2 * k)) ≤ (expect (fun x => f x ^ 2)) ^ k := by
  revert f;
  induction n with
  | zero =>
    intro f
    have h_base : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) = (expect (fun x => f x ^ (2 * k))) := by
      convert rfl using 3;
      convert rfl using 2;
      convert walsh_expansion f ‹_› |> Eq.symm using 1;
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_eq_zero.mpr ( Finset.eq_empty_of_forall_notMem fun y hy => by fin_cases y ) ] ; ring;
    simp_all +decide [ pow_mul ];
    unfold expect; norm_num [ Finset.card_univ ] ;
    norm_num [ uniformWeight ];
  | succ n ih =>
    intro f
    have h_decomp : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) = ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) * expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) := by
      have h_decomp : ∀ x' : BoolCube n, ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) / 2 = ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) * (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j) := by
        intro x'
        have h_expand : ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * ρ ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j * (if j % 2 = 0 then 2 else 0) := by
          have h_expand : ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * ρ ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * (-ρ) ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j := by
            congr 1;
            · rw [ add_comm, add_pow ] ; congr ; ext ; ring;
            · rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr ; ext ; ring;
          rw [ h_expand, ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun j hj => _ ; rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] ; ring;
        rw [ h_expand, div_eq_iff ] <;> norm_num [ Finset.sum_ite ];
        rw [ Finset.sum_mul _ _ _ ];
        rw [ show Finset.filter ( fun x => x % 2 = 0 ) ( Finset.range ( 2 * k + 1 ) ) = Finset.image ( fun x => 2 * x ) ( Finset.range ( k + 1 ) ) from ?_, Finset.sum_image <| by norm_num ];
        ext ( _ | x ) <;> simp +arith +decide [ Nat.add_mod];
        exact ⟨ fun h => ⟨ ( x + 1 ) / 2, by omega, by omega ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ by omega, by omega ⟩ ⟩;
      rw [ noise_qth_moment_decomp ];
      simp +decide only [expect, h_decomp, mul_assoc, Finset.mul_sum _ _ _];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    -- By the induction hypothesis, we have:
    have h_ind : ∀ j ∈ Finset.range (k + 1), expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) ≤ (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j := by
      intro j hj
      have h_ind_step : expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) ≤ (expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k))) ^ ((k - j) / k : ℝ) * (expect (fun x' => (noiseOp ρ (diffLast f) x') ^ (2 * k))) ^ (j / k : ℝ) := by
        have h_ind_step : ∀ (g h : BooleanFunc n), 0 ≤ expect (fun x' => g x' ^ (2 * k)) → 0 ≤ expect (fun x' => h x' ^ (2 * k)) → expect (fun x' => g x' ^ (2 * k - 2 * j) * h x' ^ (2 * j)) ≤ (expect (fun x' => g x' ^ (2 * k))) ^ ((k - j) / k : ℝ) * (expect (fun x' => h x' ^ (2 * k))) ^ (j / k : ℝ) := by
          intros g h hg hh
          have h_holder : ∀ (p q : ℝ), 1 < p → 1 < q → p⁻¹ + q⁻¹ = 1 → ∀ (f g : BoolCube n → ℝ), (∀ x', 0 ≤ f x') → (∀ x', 0 ≤ g x') → (∑ x', f x' * g x') ≤ (∑ x', f x' ^ p) ^ (1 / p : ℝ) * (∑ x', g x' ^ q) ^ (1 / q : ℝ) := by
            intros p q hp hq hpq f g hf hg;
            have := @Real.inner_le_Lp_mul_Lq;
            simpa only [ abs_of_nonneg ( hf _ ), abs_of_nonneg ( hg _ ) ] using this Finset.univ f g ( by constructor <;> ring_nf <;> nlinarith [ inv_pos.2 ( zero_lt_one.trans hp ), inv_pos.2 ( zero_lt_one.trans hq ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hp ) ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hq ) ) ] );
          by_cases hj : j = 0 ∨ j = k;
          · cases hj <;> simp +decide [ *, ne_of_gt ( zero_lt_one.trans_le hk ) ];
          · have h_holder : (∑ x', |g x'| ^ (2 * k - 2 * j) * |h x'| ^ (2 * j)) ≤ (∑ x', |g x'| ^ (2 * k)) ^ ((k - j) / k : ℝ) * (∑ x', |h x'| ^ (2 * k)) ^ (j / k : ℝ) := by
              convert h_holder ( k / ( k - j ) ) ( k / j ) _ _ _ ( fun x' => |g x'| ^ ( 2 * k - 2 * j ) ) ( fun x' => |h x'| ^ ( 2 * j ) ) _ _ using 1 <;> norm_num;
              · congr! 2;
                · refine' Finset.sum_congr rfl fun x' _ => _;
                  rw [ ← Real.rpow_natCast _ ( 2 * k - 2 * j ), ← Real.rpow_mul ( abs_nonneg _ ) ] ; norm_num [ Nat.cast_sub ( show 2 * j ≤ 2 * k from by linarith [ Finset.mem_range.mp ‹_› ] ) ];
                  rw [ show ( 2 * k - 2 * j : ℝ ) * ( k / ( k - j ) ) = 2 * k by rw [ mul_div, div_eq_iff ] <;> nlinarith [ show ( j : ℝ ) < k from mod_cast lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ‹_› ) ( by tauto ) ] ] ; norm_cast;
                · refine' Finset.sum_congr rfl fun x' _ => _;
                  rw [ ← Real.rpow_natCast _ ( 2 * j ), ← Real.rpow_mul ( abs_nonneg _ ) ] ; ring_nf ; norm_num [ show j ≠ 0 by tauto ];
                  norm_num [ mul_assoc, mul_comm, mul_left_comm, show j ≠ 0 by tauto ];
                  norm_cast;
              · rw [ lt_div_iff₀ ] <;> norm_num;
                · exact Nat.pos_of_ne_zero fun h => hj <| Or.inl h;
                · exact lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ‹_› ) ( by tauto );
              · rw [ lt_div_iff₀ ] <;> norm_cast <;> cases lt_or_gt_of_ne ( mt Or.inl hj ) <;> cases lt_or_gt_of_ne ( mt Or.inr hj ) <;> linarith [ Finset.mem_range.mp ‹_› ];
              · rw [ ← add_div, div_eq_iff ] <;> norm_num ; linarith;
            convert mul_le_mul_of_nonneg_left h_holder ( show 0 ≤ uniformWeight n by exact pow_nonneg ( by norm_num ) _ ) using 1 <;> norm_num [ expect ];
            · norm_num [ pow_mul ];
              exact Or.inl ( Finset.sum_congr rfl fun _ _ => by rw [ abs_eq_max_neg, max_def ] ; split_ifs <;> simp +decide [ *, Nat.even_sub ( show 2 * j ≤ 2 * k from by linarith [ Finset.mem_range.mp ‹_› ] ) ] );
            · norm_num [ pow_mul, abs_mul, abs_pow ];
              rw [ Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ), Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ) ] ; ring_nf;
              norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hk ) ];
              rw [ ← mul_assoc, ← Real.rpow_add ( by exact pow_pos ( by norm_num ) _ ) ] ; norm_num [ show k ≠ 0 by linarith ];
        apply h_ind_step;
        · exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( avgLast f ) _ ) 2 k ▸ by positivity );
        · exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( diffLast f ) _ ) 2 k ▸ by positivity );
      refine le_trans h_ind_step ?_;
      gcongr;
      · refine' Real.rpow_nonneg _ _;
        exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( diffLast f ) _ ) 2 k ▸ by positivity );
      · exact pow_nonneg (expect_sq_nonneg (avgLast f)) _;
      · refine' le_trans ( Real.rpow_le_rpow ( _ ) ( ih _ ) ( _ ) ) _;
        · exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( avgLast f ) _ ) 2 k ▸ by positivity );
        · exact div_nonneg ( sub_nonneg_of_le ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp hj ) ) ) ( Nat.cast_nonneg _ );
        · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( expect_sq_nonneg _ ), mul_comm ];
          rw [ div_mul_cancel₀ _ ( by positivity ), ← Nat.cast_sub ( Finset.mem_range_succ_iff.mp hj ) ] ; norm_cast;
      · convert Real.rpow_le_rpow ( ?_ ) ( ih ( diffLast f ) ) ( show ( 0 : ℝ ) ≤ j / k by positivity ) using 1;
        · rw [ ← Real.rpow_natCast _ k, ← Real.rpow_mul (expect_sq_nonneg (diffLast f)), mul_div_cancel₀ _ ( by positivity ), Real.rpow_natCast ];
        · exact le_of_not_gt fun h => by have := expect_sq_nonneg ( fun x => noiseOp ρ ( diffLast f ) x ^ k ) ; norm_num [ pow_mul' ] at * ; linarith;
    -- By the binomial coefficient inequality, we have:
    have h_binom : ∀ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) ≤ Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j := by
      intros j hj
      have h_binom_coeff : Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
        apply binom_coeff_ineq k hk j (Finset.mem_range_succ_iff.mp hj);
      convert mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_binom_coeff ) ( pow_mul ρ 2 j ▸ by positivity : 0 ≤ ρ ^ ( 2 * j ) ) using 1 ; ring_nf;
      rw [ Nat.cast_mul, Nat.cast_pow, Nat.cast_sub ( by linarith ) ] ; push_cast ; ring_nf;
      rw [ show ( -ρ ^ 2 + ρ ^ 2 * k * 2 : ℝ ) = ρ ^ 2 * ( -1 + k * 2 ) by ring ] ; rw [ mul_pow ] ; ring;
    -- By combining the results from the decomposition, induction hypothesis, and binomial coefficient inequality, we get:
    have h_combined : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j * (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j := by
      rw [h_decomp];
      refine Finset.sum_le_sum fun j hj => ?_;
      refine le_trans ( mul_le_mul_of_nonneg_left ( h_ind j hj ) ?_ ) ?_;
      · exact mul_nonneg ( Nat.cast_nonneg _ ) ( pow_mul ρ 2 j ▸ by positivity );
      · simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( h_binom j hj ) ( mul_nonneg ( pow_nonneg ( expect_sq_nonneg _ ) _ ) ( pow_nonneg ( expect_sq_nonneg _ ) _ ) );
    -- By the binomial theorem, we have:
    have h_binom_theorem : ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j * (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j = (expect (fun x' => (avgLast f x') ^ 2) + ρ ^ 2 * (2 * k - 1) * expect (fun x' => (diffLast f x') ^ 2)) ^ k := by
      rw [ add_comm, add_pow ];
      rw [ add_comm, ← Finset.sum_flip ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ; ring_nf;
      rw [ show ( -ρ ^ 2 + ρ ^ 2 * k * 2 : ℝ ) = ( ρ ^ 2 * k * 2 - ρ ^ 2 ) by ring ] ; rw [ show ( ρ ^ 2 * k * expect ( fun x' => diffLast f x' ^ 2 ) * 2 - ρ ^ 2 * expect ( fun x' => diffLast f x' ^ 2 ) ) = ( ρ ^ 2 * k * 2 - ρ ^ 2 ) * expect ( fun x' => diffLast f x' ^ 2 ) by ring ] ; rw [ mul_pow ] ; ring;
    refine le_trans h_combined <| h_binom_theorem.le.trans ?_;
    gcongr;
    · exact add_nonneg ( expect_sq_nonneg _ ) ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ) ( expect_sq_nonneg _ ) );
    · rw [ second_moment_decomp ];
      rw [ le_div_iff₀ ] at hρ <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( expect fun x' => diffLast f x' ^ 2 ) ≥ 0 by exact expect_sq_nonneg _ ]

/-! ## Equivalent formulation with q -/

/-- The (2, q)-Hypercontractivity restated with even `q`. -/
theorem hypercontractivity_2_q (q : ℕ) (hq : 2 ≤ q) (hq_even : Even q)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((q : ℝ) - 1)) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ q) ≤ (expect (fun x => f x ^ 2)) ^ (q / 2) := by
  obtain ⟨k, rfl⟩ := hq_even
  have hk : 1 ≤ k := by omega
  simp only [show k + k = 2 * k from by ring, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  apply hypercontractivity_2_2k k hk ρ _ f
  convert hρ using 1
  push_cast; ring

/-! ## Corollaries and specific cases -/

/-- The (2, 2)-hypercontractivity is just contractivity. -/
theorem hypercontractivity_2_2 (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 2) ≤ (expect (fun x => f x ^ 2)) ^ 1 := by
  rw [pow_one]
  exact contractivity ρ hρ f

/-- The (2, 4)-hypercontractivity instantiation. -/
theorem hypercontractivity_2_4_inst (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 4) ≤ (expect (fun x => f x ^ 2)) ^ 2 :=
  hypercontractivity_2_4 ρ hρ f

/-- The (2, 6)-hypercontractivity. -/
theorem hypercontractivity_2_6 (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 5) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 6) ≤ (expect (fun x => f x ^ 2)) ^ 3 := by
  exact hypercontractivity_2_q 6 (by norm_num) ⟨3, by ring⟩ ρ (by linarith) f

/-! ## Real-power formulation -/

/-
The (2, 2k)-hypercontractivity in `‖·‖_{2k} ≤ ‖·‖_2` form.
-/
theorem hypercontractivity_2_2k_rpow (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) (f : BooleanFunc n) :
    (expect (fun x => (noiseOp ρ f x) ^ (2 * k))) ^ (1 / (2 * k : ℝ)) ≤
    (expect (fun x => f x ^ 2)) ^ (1 / 2 : ℝ) := by
  convert Real.rpow_le_rpow ( ?_ ) ( hypercontractivity_2_2k k ( by linarith ) ( ρ ) ?_ ( f ) ) ?_ using 1;
  · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( expect_sq_nonneg _ ) ] ; ring_nf ; norm_num [ show k ≠ 0 by linarith ];
  · convert Hypercontractivity.expect_sq_nonneg ( fun x => noiseOp ρ f x ^ k ) using 1;
    exact congr_arg _ ( funext fun x => by ring );
  · exact hρ;
  · positivity

/-! ## (p, 2)-Hypercontractivity via Duality -/

section Duality

lemma innerProduct_eq_expect_sq (f : BooleanFunc n) :
    innerProduct f f = BooleanAnalysis.expect (fun x => f x ^ 2) := by
  unfold innerProduct BooleanAnalysis.expect uniformWeight
  congr 1
  apply Finset.sum_congr rfl
  intro x _; ring

lemma expect_sq_noiseOp_nonneg (ρ : ℝ) (f : BooleanFunc n) :
    0 ≤ BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2) := by
  unfold BooleanAnalysis.expect uniformWeight
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply Finset.sum_nonneg
  intro x _; positivity

lemma expect_rpow_abs_nonneg (p : ℝ) (f : BooleanFunc n) :
    0 ≤ BooleanAnalysis.expect (fun x => |f x| ^ p) := by
  unfold BooleanAnalysis.expect uniformWeight
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply Finset.sum_nonneg
  intro x _; positivity

lemma noiseOp_compose (ρ σ : ℝ) (f : BooleanFunc n) :
    noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f := by
  ext x
  simp only [noiseOp]
  congr 1; ext S
  rw [noiseOp_fourier]; ring

/--
**The (p, 2)-Hypercontractivity Theorem** (general duality framework):

Given a (2, q)-hypercontractivity bound and Hölder's inequality for `(p, q)`,
we conclude `(𝔼[(T_ρ f)²])^{1/2} ≤ (𝔼[|f|^p])^{1/p}`.

The proof:
1. `‖T_ρ f‖₂² = ⟨T_ρ f, T_ρ f⟩ = ⟨f, T_ρ(T_ρ f)⟩` by self-adjointness
2. `⟨f, T_ρ(T_ρ f)⟩ ≤ ‖f‖_p · ‖T_ρ(T_ρ f)‖_q` by Hölder
3. `‖T_ρ(T_ρ f)‖_q ≤ ‖T_ρ f‖₂` by (2,q)-hypercontractivity
4. Divide both sides by `‖T_ρ f‖₂`. -/
theorem hypercontractivity_p_2_general
    {ρ : ℝ} {p q : ℝ}
    (hp : 1 < p) (hq : 2 ≤ q)
    (hpq : 1/p + 1/q = 1)
    (f : BooleanFunc n)
    (holder : ∀ (u v : BooleanFunc n),
      innerProduct u v ≤
      (BooleanAnalysis.expect (fun x => |u x| ^ p)) ^ (1/p) *
      (BooleanAnalysis.expect (fun x => |v x| ^ q)) ^ (1/q))
    (hyp_2_q : ∀ (g : BooleanFunc n),
      BooleanAnalysis.expect (fun x => |noiseOp ρ g x| ^ q) ≤
      (BooleanAnalysis.expect (fun x => g x ^ 2)) ^ (q/2)) :
    (BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (1/2 : ℝ) ≤
    (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) := by
  set E₂ := BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)
  have hE₂_nn : 0 ≤ E₂ := expect_sq_noiseOp_nonneg ρ f
  by_cases hE₂_zero : E₂ = 0
  · rw [hE₂_zero]
    simp only [Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0)]
    exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _
  have hE₂_pos : 0 < E₂ := lt_of_le_of_ne hE₂_nn (Ne.symm hE₂_zero)
  have h_inner : innerProduct (noiseOp ρ f) (noiseOp ρ f) = E₂ := by
    rw [innerProduct_eq_expect_sq]
  have h_self_adj : E₂ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := by
    rw [← h_inner, noiseOp_self_adjoint]
  have h_holder := holder f (noiseOp ρ (noiseOp ρ f))
  have hq_pos : 0 < q := by linarith
  have h_Lq_bound :
      (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) ≤
      E₂ ^ (1/2 : ℝ) := by
    have step1 : (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) ≤
        ((BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (q/2)) ^ (1/q) := by
      apply Real.rpow_le_rpow
        (expect_rpow_abs_nonneg q (noiseOp ρ (noiseOp ρ f)))
        (hyp_2_q (noiseOp ρ f))
        (by positivity)
    have step2 : ((BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (q/2)) ^ (1/q) =
        E₂ ^ (1/2 : ℝ) := by
      rw [← Real.rpow_mul hE₂_nn]
      congr 1; field_simp
    linarith
  have main_bound : E₂ ≤
      (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
    calc E₂ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := h_self_adj
      _ ≤ (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) *
          (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) :=
        h_holder
      _ ≤ (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left h_Lq_bound
          exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _
  have h_half_pos : 0 < E₂ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hE₂_pos _
  have h_split : E₂ ^ (1/2 : ℝ) * E₂ ^ (1/2 : ℝ) = E₂ := by
    rw [← Real.rpow_add hE₂_pos]; norm_num
  have step3 : E₂ ^ (1/2 : ℝ) * E₂ ^ (1/2 : ℝ) ≤
      (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
    rw [h_split]; exact main_bound
  exact le_of_mul_le_mul_right step3 h_half_pos

/-- (4/3, 2)-hypercontractivity via the existing theorem. -/
theorem hypercontractivity_p_2_at_4_div_3 (f : BooleanFunc n) :
    (BooleanAnalysis.expect (fun x => (noiseOp (1 / Real.sqrt 3) f x) ^ 2)) ^ (1/2 : ℝ) ≤
    (BooleanAnalysis.expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) :=
  hypercontractivity_4_div_3_2 f
