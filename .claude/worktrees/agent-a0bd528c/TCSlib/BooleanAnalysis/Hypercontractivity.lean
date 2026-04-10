import TCSlib.BooleanAnalysis.Basic
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
import Mathlib.Probability.Distributions.Uniform

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
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis
open scoped Real
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

/-
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

end
