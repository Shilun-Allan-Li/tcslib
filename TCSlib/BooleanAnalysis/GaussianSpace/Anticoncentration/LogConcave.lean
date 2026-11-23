/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Laplace
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.LogConcaveEnvelope
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial small-ball bounds for bounded log-concave densities

## Main definitions

No new definitions.

## Main results

* `log_concave_mass_smallBall_le_of_le_lintegral_sq`: a squared-norm
  lower bound under a bounded log-concave probability density gives
  a dimension-free small-ball estimate linear in the polynomial degree.

## References

* [CW01] A. Carbery and J. Wright, *Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn*, Mathematical Research Letters
  8 (2001), 233–248, §4. We use an explicit coarse universal constant.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- A real polynomial of degree at most `d ≥ 1`, whose squared integral
under a bounded log-concave real probability density is at least
`a² > 0`, has small-ball probability at most
`1024 * exp 6 * d * (ε / a)^(1/d)` for `ε > 0`.

This is a one-dimensional, explicit coarse-constant version of the
Remez-based estimate in [CW01, §4]. Log-concavity is expressed by
concavity of the logarithm on the support. No separate finiteness
hypothesis on the polynomial's square integral is assumed.

**Proof sketch.** The density envelope bounds the original density
by `D = 8 * exp 2` times a shifted and scaled Laplace probability
density. This bounds small-ball mass above by `D` times Laplace
mass, and bounds the Laplace square moment below by the original
square-moment lower bound divided by `D`. Transport to the standard
Laplace variable by an invertible affine change and restrict the
polynomial by affine composition, preserving its degree bound.
Since `D ≤ (4 * exp 1)²`, apply the Laplace estimate with lower norm
`a / (4 * exp 1)`. Finally `(4 * exp 1)^(1/d) ≤ 4 * exp 1`
for `d ≥ 1`. Multiplying the three universal factors gives
`1024 * exp 6`. -/
theorem log_concave_mass_smallBall_le_of_le_lintegral_sq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (w : ℝ → ℝ) (hnonneg : ∀ x : ℝ, 0 ≤ w x)
    (hbounded : BddAbove (Set.range w))
    (hlog : ConcaveOn ℝ (Function.support w) (fun x : ℝ => Real.log (w x)))
    (hnorm : (∫ x : ℝ, w x ∂volume) = 1)
    (a : ℝ) (ha : 0 < a)
    (hlower :
      ENNReal.ofReal (a ^ 2) ≤
        ∫⁻ x : ℝ,
          ENNReal.ofReal ((p.eval x) ^ 2) * ENNReal.ofReal (w x) ∂volume)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in {x : ℝ | |p.eval x| ≤ ε},
      ENNReal.ofReal (w x) ∂volume).toReal ≤
      1024 * Real.exp 6 * (d : ℝ) * (ε / a) ^ (1 / (d : ℝ)) :=
  (by
    classical
    obtain ⟨c, k, hk, henv⟩ := exists_exp_abs_upper_bound_of_log_concave
      w hnonneg hbounded hlog hnorm
    let D : ℝ := 8 * Real.exp 2
    let B : ℝ := 4 * Real.exp 1
    have hD : 0 < D := by dsimp only [D]; positivity
    have hB : 0 < B := by dsimp only [B]; positivity
    have hDB : D ≤ B ^ 2 := by
      dsimp only [D, B]
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    let q : Polynomial ℝ := p.comp (Polynomial.C k⁻¹ * Polynomial.X + Polynomial.C c)
    have heval (t : ℝ) : q.eval t = p.eval (t / k + c) := by
      dsimp only [q]
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
      congr 1
      ring
    have hq : q.natDegree ≤ d := by
      have hlin : (Polynomial.C k⁻¹ * Polynomial.X + Polynomial.C c).natDegree ≤ 1 := by
        apply (Polynomial.natDegree_add_le _ _).trans
        rw [Polynomial.natDegree_C_mul_X _ (inv_ne_zero hk.ne'), Polynomial.natDegree_C]
        norm_num
      exact Polynomial.natDegree_comp_le.trans
        ((Nat.mul_le_mul hp hlin).trans (by omega))
    have hdom (f : ℝ → ENNReal) (hf : Measurable f) :
        (∫⁻ x : ℝ, f x * ENNReal.ofReal (w x)) ≤
          ENNReal.ofReal D * ∫⁻ t : ℝ, f (t / k + c) *
            ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|)) := by
      rw [← lintegral_mul_scaled_laplace_eq f hf c k hk,
        ← lintegral_const_mul _ (by fun_prop)]
      apply lintegral_mono
      intro x
      dsimp only
      rw [mul_left_comm (ENNReal.ofReal D) (f x)]
      apply mul_le_mul_left'
      rw [← ENNReal.ofReal_mul hD.le]
      apply ENNReal.ofReal_le_ofReal
      convert henv x using 1
      dsimp only [D]
      ring
    have hlowerq : ENNReal.ofReal ((a / B) ^ 2) ≤
        ∫⁻ t : ℝ, ENNReal.ofReal ((q.eval t) ^ 2) *
          ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|)) := by
      apply (ENNReal.mul_le_mul_left (ENNReal.ofReal_pos.mpr hD).ne' ENNReal.ofReal_ne_top).mp
      calc
        _ = ENNReal.ofReal (D * (a / B) ^ 2) := (ENNReal.ofReal_mul hD.le).symm
        _ ≤ ENNReal.ofReal (a ^ 2) := ENNReal.ofReal_le_ofReal (calc
          _ ≤ B ^ 2 * (a / B) ^ 2 := mul_le_mul_of_nonneg_right hDB (sq_nonneg _)
          _ = _ := by field_simp)
        _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal ((p.eval x) ^ 2) * ENNReal.ofReal (w x) := hlower
        _ ≤ _ := by simpa only [heval] using hdom (fun x => ENNReal.ofReal ((p.eval x) ^ 2)) (by fun_prop)
    let E : Set ℝ := {x | |p.eval x| ≤ ε}
    let F : Set ℝ := {t | |q.eval t| ≤ ε}
    have hE : MeasurableSet E := measurableSet_le p.continuous.abs.measurable measurable_const
    have hF : MeasurableSet F := measurableSet_le q.continuous.abs.measurable measurable_const
    have hmass : (∫⁻ x in E, ENNReal.ofReal (w x)) ≤
        ENNReal.ofReal D * ∫⁻ t in F, ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|)) := by
      have h := hdom (E.indicator (fun _ => 1)) (measurable_const.indicator hE)
      have hi : (fun t : ℝ => E.indicator (fun _ => (1 : ENNReal)) (t / k + c)) =
          F.indicator (fun _ => 1) := by
        have hpre : (fun t : ℝ => t / k + c) ⁻¹' E = F := by
          ext t
          change |p.eval (t / k + c)| ≤ ε ↔ |q.eval t| ≤ ε
          rw [heval]
        funext t
        simpa only [hpre] using (Set.indicator_comp_right (s := E) (g := fun _ => (1 : ENNReal))
          (x := t) (fun t : ℝ => t / k + c)).symm
      simp_rw [show ∀ t : ℝ, E.indicator (fun _ => (1 : ENNReal)) (t / k + c) =
        F.indicator (fun _ => 1) t from fun t => congrFun hi t] at h
      have hprod (U : Set ℝ) (g : ℝ → ENNReal) (x : ℝ) :
          U.indicator (fun _ => 1) x * g x = U.indicator g x := by
        simpa only [one_mul] using
          (Set.indicator_mul_left U (fun _ => (1 : ENNReal)) g (i := x)).symm
      simp_rw [hprod E (fun x => ENNReal.ofReal (w x)),
        hprod F (fun t => ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|)))] at h
      simpa only [lintegral_indicator hE, lintegral_indicator hF] using h
    have hfinite : (∫⁻ t in F, ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|t|))) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Measure.restrict_univ, lintegral_laplace_eq_one]; norm_num) (lintegral_mono_set (Set.subset_univ F))
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hmass
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] at hreal
    have hsmall := laplace_mass_smallBall_le_of_le_lintegral_sq q d hq hd
      (a / B) (div_pos ha hB) hlowerq ε hε
    have hBlarge : 1 ≤ B := by
      have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
      dsimp only [B]
      linarith
    have hrpow : (ε / (a / B)) ^ (1 / (d : ℝ)) ≤
        B * (ε / a) ^ (1 / (d : ℝ)) := by
      rw [show ε / (a / B) = B * (ε / a) by field_simp,
        Real.mul_rpow hB.le (div_pos hε ha).le]
      exact mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le hBlarge (by
          have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
          exact (div_le_one (by positivity : (0 : ℝ) < d)).mpr hdR)).trans_eq (Real.rpow_one B))
        (Real.rpow_nonneg (div_pos hε ha).le _)
    change (∫⁻ x in E, ENNReal.ofReal (w x)).toReal ≤ _
    calc
      _ ≤ D * (32 * Real.exp 3 * (d : ℝ) * (ε / (a / B)) ^ (1 / (d : ℝ))) :=
        hreal.trans (mul_le_mul_of_nonneg_left hsmall hD.le)
      _ ≤ D * (32 * Real.exp 3 * (d : ℝ) * (B * (ε / a) ^ (1 / (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow (by positivity)) hD.le
      _ = _ := by
        dsimp only [D, B]
        rw [show (6 : ℝ) = 2 + 3 + 1 by norm_num, Real.exp_add, Real.exp_add]
        ring


)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
