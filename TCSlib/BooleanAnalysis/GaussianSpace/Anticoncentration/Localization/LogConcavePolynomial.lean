/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ConcaveLocalization
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ProfileAnticoncentration
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.PolynomialRestriction
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.UrysohnsLemma

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial anticoncentration under positive log-concave densities

## Main definitions

No new definitions.

## Main results

* `log_concave_integral_smallBall_le_of_integral_sq_eq_one`: a
  normalized multivariate polynomial under a continuous positive
  log-concave probability density has a small-ball estimate independent
  of the ambient dimension.

## References

* [CW01] A. Carbery and J. Wright, *Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn*, Mathematical Research Letters
  8 (2001), 233–248, §4.
* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, pp.379–381.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- A multivariate real polynomial of total degree at most `k ≥ 1`,
with square integral one under a continuous everywhere-positive
log-concave probability density, has small-ball mass at most
`4096 * exp 6 * k * ε^(1/k)`.

The ambient coordinate dimension is `n+1`, with `n ≥ 1`.
Both normalizations and the conclusion use real Bochner integrals
against Lebesgue measure. No boundedness of the ambient density or
additional integrability hypotheses are imposed.

This is an explicit coarse-constant version of the localization and
Remez method in [CW01, §4], using the concave-profile stage of
[LS93, Lemma 2.5, pp.379–381] rather than assuming a further reduction
to exponential needles.

**Proof sketch.** For `ε ≥ 1/4`, total mass one gives the bound.
Otherwise suppose the small-ball mass exceeds the claimed bound and
choose a number `s` strictly between them. Urysohn's lemma supplies a
continuous cutoff between zero and one, equal to one on `|P|≤ε`
and zero on `|P|≥2ε`. The tests `(h-s)ρ` and
`(P²-1/4)ρ` have positive full integrals. Truncate both to one
compact convex set and apply point-or-segment concave localization.
The point alternative forces simultaneously `|P|≥1/2` and
`|P|<2ε<1/2`. In the segment alternative restrict the polynomial
to the line, preserving its degree, and use the concave exponent
`log ρ` restricted to that line. The localized moment inequality
gives lower norm `a=1/2`. The localized cutoff inequality bounds
`s` times the raw profile mass by its sublevel mass at `2ε`.
The profile-weight estimate bounds this by
`1024 * exp 6 * k * (4ε)^(1/k)` times the same positive mass.
Since `4^(1/k)≤4`, cancellation contradicts the choice of `s`. -/
theorem log_concave_integral_smallBall_le_of_integral_sq_eq_one
    {n : ℕ} (hn : 1 ≤ n)
    (ρ : (Fin (n + 1) → ℝ) → ℝ)
    (hρcont : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hρlog : ConcaveOn ℝ Set.univ (fun x => Real.log (ρ x)))
    (hρnorm : (∫ x : Fin (n + 1) → ℝ, ρ x) = 1)
    (p : MvPolynomial (Fin (n + 1)) ℝ)
    (k : ℕ) (hp : p.totalDegree ≤ k) (hk : 1 ≤ k)
    (hpnorm :
      (∫ x : Fin (n + 1) → ℝ,
        (MvPolynomial.eval x p) ^ 2 * ρ x) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ x in {x : Fin (n + 1) → ℝ | |MvPolynomial.eval x p| ≤ ε},
      ρ x) ≤
      4096 * Real.exp 6 * (k : ℝ) * ε ^ (1 / (k : ℝ)) :=
  (by
    classical
    -- Unit mass controls the range where the requested bound is already at least one.
    let P := fun x : Fin (n + 1) → ℝ => MvPolynomial.eval x p
    have hP : Continuous P := MvPolynomial.continuous_eval p
    have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρnorm]; norm_num)
    have hPi : Integrable (fun x => P x ^ 2 * ρ x) :=
      Integrable.of_integral_ne_zero (by change (∫ x, MvPolynomial.eval x p ^ 2 * ρ x) ≠ 0; rw [hpnorm]; norm_num)
    have hmass : (∫ x in {x | |P x| ≤ ε}, ρ x) ≤ 1 := by
      rw [← hρnorm]
      exact setIntegral_le_integral hρi (Filter.Eventually.of_forall fun x => (hρpos x).le)
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by positivity
    have hexp : (1 : ℝ) ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
    have hrpos : 0 < ε ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hε _
    change (∫ x in {x | |P x| ≤ ε}, ρ x) ≤ _
    by_cases hlarge : 1 / 4 ≤ ε
    · have hr : (1 / 4 : ℝ) ≤ ε ^ (1 / (k : ℝ)) := by
        by_cases he : 1 ≤ ε
        · exact (by norm_num : (1 / 4 : ℝ) ≤ 1).trans (Real.one_le_rpow he (by positivity))
        · have hh := Real.rpow_le_rpow_of_exponent_ge hε (le_of_not_ge he)
            (show 1 / (k : ℝ) ≤ 1 by exact (div_le_one hkpos).2 hkR)
          rw [Real.rpow_one] at hh
          exact hlarge.trans hh
      apply hmass.trans
      nlinarith [mul_le_mul hexp hkR (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos 6).le,
        mul_le_mul_of_nonneg_left hr (show 0 ≤ 4096 * Real.exp 6 * (k : ℝ) by positivity)]
    have hεsmall : ε < 1 / 4 := lt_of_not_ge hlarge
    by_contra hfail
    obtain ⟨s, hTs, hsS⟩ := exists_between (lt_of_not_ge hfail)
    have hspos : 0 < s := lt_trans (by positivity) hTs
    -- Separate the two closed polynomial level sets by a continuous cutoff.
    obtain ⟨h, hhzero, hhone, hhbounds⟩ :=
      exists_continuous_zero_one_of_isClosed
        (isClosed_le continuous_const hP.abs) (isClosed_le hP.abs continuous_const)
        (show Disjoint {x | 2 * ε ≤ |P x|} {x | |P x| ≤ ε} from by
          apply Set.disjoint_left.2
          intro x hx hy
          change 2 * ε ≤ |P x| at hx
          change |P x| ≤ ε at hy
          linarith)
    have hhi : Integrable (fun x => h x * ρ x) :=
      hρi.bdd_mul h.continuous.aestronglyMeasurable ⟨1, fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hhbounds x).1]
        exact (hhbounds x).2⟩
    have hcut : (∫ x in {x | |P x| ≤ ε}, ρ x) ≤ ∫ x, h x * ρ x := by
      calc
        _ = ∫ x in {x | |P x| ≤ ε}, h x * ρ x := by
          apply setIntegral_congr_fun (isClosed_le hP.abs continuous_const).measurableSet
          intro x hx
          change ρ x = h x * ρ x
          rw [hhone hx, Pi.one_apply, one_mul]
        _ ≤ ∫ x, h x * ρ x := setIntegral_le_integral hhi
          (Filter.Eventually.of_forall fun x => mul_nonneg (hhbounds x).1 (hρpos x).le)
    -- Both continuous signed tests have positive integrals on a common compact convex set.
    let F := fun x => (h x - s) * ρ x
    let G := fun x => (P x ^ 2 - 1 / 4) * ρ x
    have hF : Continuous F := (h.continuous.sub continuous_const).mul hρcont
    have hG : Continuous G := ((hP.pow 2).sub continuous_const).mul hρcont
    have hFpos : 0 < ∫ x, F x := by
      simp only [F, sub_mul]
      rw [integral_sub hhi (hρi.const_mul s), integral_const_mul, hρnorm, mul_one]
      exact sub_pos.2 (hsS.trans_le hcut)
    have hGpos : 0 < ∫ x, G x := by
      simp only [G, sub_mul]
      rw [integral_sub hPi (hρi.const_mul (1 / 4)), integral_const_mul, hρnorm]
      change 0 < (∫ x, MvPolynomial.eval x p ^ 2 * ρ x) - 1 / 4 * 1
      rw [hpnorm]
      norm_num
    obtain ⟨K, hKcompact, hKconvex, hKF, hKG⟩ :=
      exists_isCompact_convex_pos_integrals volume F G hFpos hGpos
    rcases exists_point_or_concave_profile_on_segment hn K hKcompact hKconvex F G hF hG hKF hKG with
      ⟨x, _, hxF, hxG⟩ | ⟨a, b, _, _, _, φ, hφ, hφmid, hφbounds, hφF, hφG⟩
    · -- A point with both tests nonnegative cannot lie in the cutoff support.
      have hxs : s ≤ h x := by
        have := nonneg_of_mul_nonneg_left hxF (hρpos x)
        linarith
      have hxP : 1 / 4 ≤ P x ^ 2 := by
        have := nonneg_of_mul_nonneg_left hxG (hρpos x)
        linarith
      have hxsmall : |P x| < 2 * ε := by
        by_contra hnot
        have hz := hhzero (show 2 * ε ≤ |P x| from le_of_not_gt hnot)
        change h x = 0 at hz
        linarith
      have hsquare := sq_abs (P x)
      nlinarith [abs_nonneg (P x)]
    · -- On the localized line, restrict the polynomial and retain the original density.
      let γ : ℝ →ᵃ[ℝ] (Fin (n + 1) → ℝ) := AffineMap.lineMap a b
      have hγ : Continuous γ := γ.continuous_of_finiteDimensional
      obtain ⟨q, hq, hqeval⟩ := exists_polynomial_eval_lineMap_natDegree_le p a b
      have hqP (t : ℝ) : q.eval t = P (γ t) := hqeval t
      let g := fun t => Real.log (ρ (γ t))
      have hg : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g :=
        (hρlog.comp_affineMap γ).subset (by intro t ht; trivial) (convex_Icc 0 1)
      have hgcont : Continuous g := (hρcont.comp hγ).log (fun t => (hρpos (γ t)).ne')
      let V := fun t => φ t ^ n * Real.exp (g t)
      let Z := ∫ t in Set.Ioo (0 : ℝ) 1, V t
      have hprofile := integrable_pos_normalized_log_concave_profile_weight φ g
        hφ hφmid hφbounds hg hgcont.continuousOn n
      have hVi : IntegrableOn V (Set.Ioo (0 : ℝ) 1) :=
        (integrable_indicator_iff measurableSet_Ioo).1 hprofile.1
      have hZpos : 0 < Z := by
        simpa only [integral_indicator measurableSet_Ioo] using hprofile.2.1
      have hVnonneg (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 ≤ V t :=
        mul_nonneg (pow_nonneg (hφbounds t ht).1 n) (Real.exp_pos _).le
      have hVeval (t : ℝ) : V t = φ t ^ n * ρ (γ t) := by
        dsimp only [V, g]
        rw [Real.exp_log (hρpos (γ t))]
      have hVhi : IntegrableOn (fun t => V t * h (γ t)) (Set.Ioo (0 : ℝ) 1) :=
        hVi.mul_continuousOn_of_subset (h.continuous.comp hγ).continuousOn
          measurableSet_Ioo isCompact_Icc Set.Ioo_subset_Icc_self
      have hVqi : IntegrableOn (fun t => V t * q.eval t ^ 2) (Set.Ioo (0 : ℝ) 1) :=
        hVi.mul_continuousOn_of_subset (q.continuous.pow 2).continuousOn
          measurableSet_Ioo isCompact_Icc Set.Ioo_subset_Icc_self
      -- Raw profile integrability justifies extracting the cutoff and moment inequalities.
      have hFeq : (fun t => φ t ^ n * F (AffineMap.lineMap a b t)) =
          (fun t => V t * h (γ t) - s * V t) := by
        funext t
        rw [hVeval]
        dsimp only [F, γ]
        ring
      have hGeq : (fun t => φ t ^ n * G (AffineMap.lineMap a b t)) =
          (fun t => V t * q.eval t ^ 2 - (1 / 4) * V t) := by
        funext t
        rw [hVeval, hqP]
        dsimp only [G, γ]
        ring
      rw [hFeq, integral_sub hVhi (hVi.const_mul s), integral_const_mul] at hφF
      rw [hGeq, integral_sub hVqi (hVi.const_mul (1 / 4)), integral_const_mul] at hφG
      have hlower : (1 / 2 : ℝ) ^ 2 * Z ≤
          ∫ t in Set.Ioo (0 : ℝ) 1, V t * q.eval t ^ 2 := by
        dsimp only [Z]
        nlinarith
      let B := {t : ℝ | |q.eval t| ≤ 2 * ε}
      have hB : MeasurableSet B := (isClosed_le q.continuous.abs continuous_const).measurableSet
      have hcutline : s * Z ≤ ∫ t in {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ 2 * ε}, V t := by
        calc
          _ ≤ ∫ t in Set.Ioo (0 : ℝ) 1, V t * h (γ t) := by
            dsimp only [Z]
            linarith
          _ ≤ ∫ t in Set.Ioo (0 : ℝ) 1, B.indicator V t := by
            apply setIntegral_mono_on hVhi (hVi.indicator hB) measurableSet_Ioo
            intro t ht
            by_cases htB : t ∈ B
            · rw [Set.indicator_of_mem htB]
              exact mul_le_of_le_one_right (hVnonneg t ht) (hhbounds (γ t)).2
            · rw [Set.indicator_of_notMem htB]
              have hzt : h (γ t) = 0 := by
                apply hhzero
                change 2 * ε ≤ |P (γ t)|
                rw [← hqP]
                exact (lt_of_not_ge htB).le
              rw [hzt, mul_zero]
          _ = _ := by
            rw [integral_indicator hB, Measure.restrict_restrict hB]
            have hset : B ∩ Set.Ioo (0 : ℝ) 1 =
                {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ 2 * ε} := by
              ext t
              exact and_comm
            rw [hset]
      -- Apply the quantitative profile theorem and absorb the factor from doubling the threshold.
      have hsmall := profile_weight_smallBall_le_of_le_integral_sq q k (hq.trans hp) hk
        φ g hφ hφmid hφbounds hg hgcont.continuousOn n (1 / 2) (by norm_num)
        hlower (2 * ε) (by positivity)
      change (∫ t in {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ |q.eval t| ≤ 2 * ε}, V t) ≤
        (1024 * Real.exp 6 * (k : ℝ) * (2 * ε / (1 / 2)) ^ (1 / (k : ℝ))) * Z at hsmall
      have hscaled : (2 * ε / (1 / 2)) ^ (1 / (k : ℝ)) ≤
          4 * ε ^ (1 / (k : ℝ)) := by
        rw [show 2 * ε / (1 / 2) = 4 * ε by ring, Real.mul_rpow (by norm_num) hε.le]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hε.le _)
        calc
          (4 : ℝ) ^ (1 / (k : ℝ)) ≤ 4 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ((div_le_one hkpos).2 hkR)
          _ = 4 := Real.rpow_one _
      have hcoeff : 1024 * Real.exp 6 * (k : ℝ) * (2 * ε / (1 / 2)) ^ (1 / (k : ℝ)) ≤
          4096 * Real.exp 6 * (k : ℝ) * ε ^ (1 / (k : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hscaled
          (show 0 ≤ 1024 * Real.exp 6 * (k : ℝ) by positivity)]
      have hsbound := hcutline.trans (hsmall.trans (mul_le_mul_of_nonneg_right hcoeff hZpos.le))
      exact (not_le_of_gt hTs) ((mul_le_mul_iff_left₀ hZpos).1 hsbound)

)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
