/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ProfileDensity
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.LogConcave

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial small-ball bounds for localized profile weights

## Main definitions

No new definitions.

## Main results

* `profile_weight_smallBall_le_of_le_integral_sq`: the bounded
  log-concave density estimate in the unnormalized Bochner-integral
  interface supplied by concave localization.

## References

* [CW01] A. Carbery and J. Wright, *Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn*, Mathematical Research Letters
  8 (2001), 233–248, §4.
* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proof of Claim 2, pp.380–381.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- A real polynomial with squared moment at least `a²` times the mass
of a localized profile weight has weighted small-ball mass at most
`1024 * exp 6 * d * (ε/a)^(1/d)` times that same mass.

The weight is the natural power of a nonnegative concave profile,
multiplied by the exponential of a continuous concave exponent on the
unit interval. Its positive mass, bounded normalized density, and
integrability follow from the qualitative profile hypotheses; none is
an additional assumption. The profile need not be continuous at the
endpoints or measurable outside the open interval.

This is the raw weighted-integral specialization of the one-dimensional
estimate proved by the Remez method of [CW01, §4], adapted to the
concave-profile stage of [LS93, Lemma 2.5, Claim 2, pp.380–381].
The explicit coarse constant and Bochner-integral interface are ours.

**Proof sketch.** Zero-extend the profile weight and apply its
normalization theorem, obtaining a positive mass `Z` and a bounded
log-concave probability density `w=W/Z`. The assumed raw moment is
strictly positive, so it is integrable under the Bochner convention.
Divide its integral by `Z` and convert the resulting nonnegative
integral to the lower-lintegral hypothesis of the general log-concave
polynomial estimate. Apply that estimate. Convert its small-ball
lintegral back to the integral of the normalized weight, using the
integrability of the raw weight on the sublevel set, then multiply by
`Z>0`. Indicator identities restrict both raw integrals to the open
unit interval. -/
theorem profile_weight_smallBall_le_of_le_integral_sq
    (q : Polynomial ℝ) (d : ℕ) (hq : q.natDegree ≤ d) (hd : 1 ≤ d)
    (φ g : ℝ → ℝ)
    (hφ : ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ)
    (hφmid : φ (1 / 2 : ℝ) = 1)
    (hφbounds : ∀ t ∈ Set.Ioo (0 : ℝ) 1, φ t ∈ Set.Icc (0 : ℝ) 2)
    (hg : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g)
    (hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (m : ℕ) (a : ℝ) (ha : 0 < a)
    (hlower :
      a ^ 2 * (∫ t in Set.Ioo (0 : ℝ) 1, (φ t) ^ m * Real.exp (g t)) ≤
        ∫ t in Set.Ioo (0 : ℝ) 1,
          ((φ t) ^ m * Real.exp (g t)) * (q.eval t) ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ t in {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ ε},
      (φ t) ^ m * Real.exp (g t)) ≤
      (1024 * Real.exp 6 * (d : ℝ) * (ε / a) ^ (1 / (d : ℝ))) *
        (∫ t in Set.Ioo (0 : ℝ) 1, (φ t) ^ m * Real.exp (g t)) :=
  (by
    let V : ℝ → ℝ := fun t => (φ t) ^ m * Real.exp (g t)
    let W : ℝ → ℝ := (Set.Ioo (0 : ℝ) 1).indicator V
    let Z : ℝ := ∫ t : ℝ, W t
    let w : ℝ → ℝ := fun t => W t / Z
    obtain ⟨hW, hZ, hwnonneg, hwbounded, hwnorm, _, hwlog⟩ :=
      integrable_pos_normalized_log_concave_profile_weight φ g hφ hφmid hφbounds hg hgcont m
    change Integrable W volume at hW
    change 0 < Z at hZ
    change ∀ t, 0 ≤ w t at hwnonneg
    change BddAbove (Set.range w) at hwbounded
    change (∫ t, w t) = 1 at hwnorm
    change ConcaveOn ℝ (Function.support w) (fun t => Real.log (w t)) at hwlog
    have hZraw : Z = ∫ t in Set.Ioo (0 : ℝ) 1, V t := integral_indicator measurableSet_Ioo
    have hmoment : (∫ t : ℝ, W t * (q.eval t) ^ 2) =
        ∫ t in Set.Ioo (0 : ℝ) 1, V t * (q.eval t) ^ 2 := by
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t =>
        (Set.indicator_mul_left (Set.Ioo (0 : ℝ) 1) V (fun t => (q.eval t) ^ 2)).symm
    change a ^ 2 * (∫ t in Set.Ioo (0 : ℝ) 1, V t) ≤
      ∫ t in Set.Ioo (0 : ℝ) 1, V t * (q.eval t) ^ 2 at hlower
    rw [← hZraw, ← hmoment] at hlower
    have hmomentint : Integrable (fun t => W t * (q.eval t) ^ 2) volume :=
      Integrable.of_integral_ne_zero ((mul_pos (sq_pos_of_pos ha) hZ).trans_le hlower).ne'
    have hnormalized (t : ℝ) : (q.eval t) ^ 2 * w t = (W t * (q.eval t) ^ 2) / Z := by
      dsimp only [w]
      ring
    have hnormalizedint : Integrable (fun t => (q.eval t) ^ 2 * w t) volume := by
      simpa only [hnormalized] using hmomentint.div_const Z
    have hlowernorm : a ^ 2 ≤ ∫ t : ℝ, (q.eval t) ^ 2 * w t := by
      simp_rw [hnormalized]
      rw [integral_div]
      exact (le_div_iff₀ hZ).mpr hlower
    have hlowerlin : ENNReal.ofReal (a ^ 2) ≤
        ∫⁻ t : ℝ, ENNReal.ofReal ((q.eval t) ^ 2) * ENNReal.ofReal (w t) := by
      have hconvert := ofReal_integral_eq_lintegral_ofReal hnormalizedint
        (Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (hwnonneg t))
      simp_rw [ENNReal.ofReal_mul (sq_nonneg _)] at hconvert
      exact (ENNReal.ofReal_le_ofReal hlowernorm).trans_eq hconvert
    have hsmall := log_concave_mass_smallBall_le_of_le_lintegral_sq q d hq hd
      w hwnonneg hwbounded hwlog hwnorm a ha hlowerlin ε hε
    let E : Set ℝ := {t | |q.eval t| ≤ ε}
    have hE : MeasurableSet E := measurableSet_le q.continuous.abs.measurable measurable_const
    have hwint : Integrable w volume := hW.div_const Z
    have hsmallconvert := ofReal_integral_eq_lintegral_ofReal hwint.integrableOn
      (Filter.Eventually.of_forall hwnonneg : ∀ᵐ t ∂volume.restrict E, 0 ≤ w t)
    change (∫⁻ t in E, ENNReal.ofReal (w t)).toReal ≤ _ at hsmall
    rw [← hsmallconvert, ENNReal.toReal_ofReal (setIntegral_nonneg hE (fun t _ => hwnonneg t))] at hsmall
    have hsmallraw : (∫ t in E, w t) =
        (∫ t in {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ ε}, V t) / Z := by
      dsimp only [w]
      rw [integral_div]
      congr 1
      change (∫ t in E, (Set.Ioo (0 : ℝ) 1).indicator V t) = _
      rw [setIntegral_indicator measurableSet_Ioo,
        show E ∩ Set.Ioo (0 : ℝ) 1 =
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ ε} by
          ext t
          exact and_comm]
    rw [hsmallraw] at hsmall
    change (∫ t in {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ ε}, V t) ≤ _
    rw [← hZraw]
    exact (div_le_iff₀ hZ).mp hsmall

)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
