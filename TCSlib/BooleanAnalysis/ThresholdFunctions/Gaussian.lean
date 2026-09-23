import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianPolar
import TCSlib.BooleanAnalysis.ThresholdFunctions.Majority
import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianTail

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian tools and regular threshold functions

This file states the Gaussian and central-limit results used in Chapter 5, together with their
applications to regular linear threshold functions and majority.

## Main definitions

* `standardGaussianCDF`, `standardGaussianTail`, and `gaussianIsoperimetric`.
* `kolmogorovDistance` for one-dimensional probability measures.
* `gaussianQuadrantProbability` for a correlated standard Gaussian pair.

## Main results

* `berryEsseen`: the quantitative central limit theorem used in the chapter.
* `rademacher_abs_expectation`: Theorem 5.16 for regular Rademacher sums.
* `sheppard_formula`: the quadrant probability of correlated Gaussians.
* `regular_ltf_stability` and `majority_stability_limit`.
* `majority_is_stablest`: the epsilon-delta form of Majority Is Stablest.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapter 5.
* [Ber41] A. C. Berry, The accuracy of the Gaussian approximation to the sum of independent
  variates, 1941.
* [Ess42] C.-G. Esseen, On the Liapunoff limit of error in the theory of probability, 1942.
* [She99] W. F. Sheppard, On the application of the theory of error to cases of normal
  distribution and normal correlation, 1899.
* [KKMO07] S. Khot, G. Kindler, E. Mossel, and R. O'Donnell, Optimal inapproximability results for
  MAX-CUT and other 2-variable CSPs?, 2007.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace BooleanAnalysis
namespace ThresholdFunctions

variable {n : ℕ}

/-! ## Quantitative central limit statements -/

/-- The Kolmogorov distance between two real-valued probability measures.

[OD14, §5.2] -/
noncomputable def kolmogorovDistance (μ ν : Measure ℝ) : ℝ :=
  sSup (Set.range fun t : ℝ ↦ |(μ (Set.Iic t)).toReal - (ν (Set.Iic t)).toReal|)

/-- The Berry-Esseen theorem bounds the Kolmogorov distance from a normalized sum of independent,
mean-zero variables to the standard Gaussian by a universal constant times the sum of third
absolute moments. [OD14, §5.2, Berry-Esseen Theorem; Ber41; Ess42]

**Proof sketch.** This is the quantitative central limit theorem used as an external analytic input
in Chapter 5. Its classical proof compares characteristic functions, smooths the indicator of a
half-line, and controls the accumulated Taylor remainder by the third absolute moments. -/
theorem berryEsseen :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ),
      iIndepFun X μ → (∀ i, Measurable (X i)) →
      (∀ i, Integrable (fun ω ↦ |X i ω| ^ 3) μ) →
      (∀ i, ∫ ω, X i ω ∂μ = 0) →
      (∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ = 1) →
      kolmogorovDistance (μ.map fun ω ↦ ∑ i : Fin n, X i ω) standardGaussianMeasure ≤
        c * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂μ := sorry

/-- A normalized Rademacher sum with all coefficients at most `ε` in magnitude has expected
absolute value within `Cε` of `sqrt (2/π)`, for a universal constant `C`.
[OD14, Thm. 5.16]

**Proof sketch.** Berry-Esseen controls the distribution functions of the Rademacher sum and the
standard Gaussian. Integrate their two-sided tail probabilities; the nonuniform Berry-Esseen bound
controls the tails without a logarithmic loss. -/
theorem rademacher_abs_expectation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (a : Fin n → ℝ) {ε : ℝ},
      (∑ i : Fin n, a i ^ 2 = 1) → (∀ i, |a i| ≤ ε) →
      |expect (fun x ↦ |∑ i : Fin n, a i * boolToSign (x i)|) -
          Real.sqrt (2 / Real.pi)| ≤ C * ε := sorry

/-! ## Correlated Gaussians and noise stability -/

/-- The lower-left quadrant probability for a standard Gaussian pair of correlation `ρ`.
The pair is realized from independent standard Gaussians as
`(z₁, ρ z₁ + sqrt (1-ρ²) z₂)`.

[OD14, §5.2, Sheppard's Formula] -/
noncomputable def gaussianQuadrantProbability (ρ : ℝ) : ℝ :=
  (((standardGaussianMeasure.prod standardGaussianMeasure)
      {z : ℝ × ℝ | z.1 ≤ 0 ∧ ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ 0}).toReal)

/-- Sheppard's formula evaluates the same-sign quadrant probability of two correlated standard
Gaussians. [OD14, §5.2, Sheppard's Formula; She99]

**Proof sketch.** Express the correlated pair as a linear image of two independent Gaussians.
Rotational invariance makes its direction uniform, and the relevant planar wedge has angle
`π - arccos ρ`; dividing by `2π` gives the quadrant probability. -/
theorem sheppard_formula {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianQuadrantProbability ρ = 1 / 2 - Real.arccos ρ / (2 * Real.pi) := by
  obtain ⟨hρ1, hρ2⟩ := hρ
  have hpipos := Real.pi_pos
  set α : ℝ := Real.arccos ρ with hα
  have hcos : Real.cos α = ρ := Real.cos_arccos hρ1 hρ2
  have hsin : Real.sin α = Real.sqrt (1 - ρ ^ 2) := by rw [hα, Real.sin_arccos]
  have h0 : 0 ≤ α := Real.arccos_nonneg ρ
  have hpi : α ≤ Real.pi := Real.arccos_le_pi ρ
  set A : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | z.1 ≤ 0 ∧ ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2 ≤ 0} with hAdef
  have hAmeas : MeasurableSet A := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_fst measurable_const
    · exact measurableSet_le
        ((measurable_fst.const_mul ρ).add (measurable_snd.const_mul _)) measurable_const
  have hcone : ∀ r θ : ℝ, 0 < r →
      ((r * Real.cos θ, r * Real.sin θ) ∈ A ↔
        θ ∈ {θ : ℝ | Real.cos θ ≤ 0 ∧ Real.cos (θ - α) ≤ 0}) := by
    intro r θ hr
    have hcs : Real.cos (θ - α) = ρ * Real.cos θ + Real.sqrt (1 - ρ ^ 2) * Real.sin θ := by
      rw [Real.cos_sub, hcos, hsin]; ring
    simp only [hAdef, Set.mem_setOf_eq, hcs]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hmass : (standardGaussianMeasure.prod standardGaussianMeasure) A
      = ENNReal.ofReal ((2 * Real.pi)⁻¹ * (Real.pi - α)) := by
    rw [standardGaussianMeasure, gaussian_prod_apply hAmeas,
      gaussian_cone_lintegral hAmeas (measurableSet_twoHalfplaneAngles α) hcone,
      angular_measure_two_halfplanes h0 hpi,
      ← ENNReal.ofReal_mul (p := (2 * Real.pi)⁻¹) (by positivity)]
  rw [gaussianQuadrantProbability, hmass,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (by linarith))]
  field_simp

/-- A regular unbiased LTF has noise stability close to the Gaussian value
`(2/π) * arcsin ρ`. The displayed denominator makes the chapter's `ρ`-dependence explicit.
[OD14, Thm. 5.17]

**Proof sketch.** Apply the two-dimensional Berry-Esseen theorem to the pair of correlated weighted
Rademacher sums. The disagreement region is a union of convex quadrants; Sheppard's formula gives
its Gaussian probability, and regularity controls the approximation error. -/
theorem regular_ltf_stability :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : ℕ} {f : BooleanFunc n} (a : Fin n → ℝ) {ε ρ : ℝ},
      IsHomogeneousLinearThresholdRepresentation f a →
      (∑ i : Fin n, a i ^ 2 = 1) → (∀ i, |a i| ≤ ε) → |ρ| < 1 →
      |noiseStability ρ f - (2 / Real.pi) * Real.arcsin ρ| ≤
        C * Real.sqrt ε / (1 - ρ) := sorry

/-- For nonnegative correlation, majority's stability decreases with odd input length and converges
to `(2/π) * arcsin ρ`, with the stated square-root error scale. [OD14, Thm. 5.18]

**Proof sketch.** Expand stability as the generating function of level weights. The monotonicity of
each odd level weight gives monotonicity in the dimension. A two-dimensional CLT and Sheppard's
formula identify the limit and quantify the error. -/
theorem majority_stability_limit :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ : ℝ}, ρ ∈ Set.Ico (0 : ℝ) 1 →
      (∀ k : ℕ, noiseStability ρ (majority (k + 1)) ≤ noiseStability ρ (majority k)) ∧
      Filter.Tendsto (fun k : ℕ ↦ noiseStability ρ (majority k)) Filter.atTop
        (nhds ((2 / Real.pi) * Real.arcsin ρ)) ∧
      ∀ k : ℕ,
        (2 / Real.pi) * Real.arcsin ρ ≤ noiseStability ρ (majority k) ∧
          noiseStability ρ (majority k) ≤ (2 / Real.pi) * Real.arcsin ρ +
            C / (Real.sqrt (1 - ρ ^ 2) * Real.sqrt (2 * k + 1)) := by
  -- The two analytic inputs of the theorem: the limiting value, obtained from the level-weight
  -- limits of `majority_weight_tendsto` together with the power series of `arcsin`, and the
  -- quantitative error bound coming from `majority_weight_asymptotics`.
  have key : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ : ℝ}, ρ ∈ Set.Ico (0 : ℝ) 1 →
      Filter.Tendsto (fun k : ℕ ↦ noiseStability ρ (majority k)) Filter.atTop
          (nhds ((2 / Real.pi) * Real.arcsin ρ)) ∧
        ∀ k : ℕ, noiseStability ρ (majority k) ≤ (2 / Real.pi) * Real.arcsin ρ +
          C / (Real.sqrt (1 - ρ ^ 2) * Real.sqrt (2 * k + 1)) := sorry
  obtain ⟨C, hC0, hkey⟩ := key
  refine ⟨C, hC0, fun {ρ} hρ ↦ ?_⟩
  obtain ⟨htend, hupper⟩ := hkey hρ
  have hanti : ∀ k : ℕ, noiseStability ρ (majority (k + 1)) ≤ noiseStability ρ (majority k) :=
    fun k ↦ majority_noiseStability_antitone hρ.1 (le_of_lt hρ.2) k
  refine ⟨hanti, htend, fun k ↦ ⟨?_, hupper k⟩⟩
  -- the stability sequence decreases to its limit, so every term is at least the limit
  exact (antitone_nat_of_succ_le hanti).le_of_tendsto htend k

/-- Among unbiased bounded functions whose individual influences are sufficiently small, majority
asymptotically maximizes noise stability. This is an epsilon-delta rendering of the chapter's
`o_τ(1)` term. [OD14, §5.2, Majority Is Stablest; KKMO07]

**Proof sketch.** Smooth the function by the noise operator, transfer it to Gaussian space using an
invariance principle, and apply Gaussian isoperimetry. The small-influence hypothesis controls the
invariance error; Sheppard's formula evaluates the extremal Gaussian halfspace. -/
theorem majority_is_stablest {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) → expect f = 0 → maxInfluence f ≤ τ →
        noiseStability ρ f ≤ (2 / Real.pi) * Real.arcsin ρ + ε := sorry

end ThresholdFunctions
end BooleanAnalysis
