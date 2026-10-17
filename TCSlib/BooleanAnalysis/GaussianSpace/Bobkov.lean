/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.TwoPoint
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Cube
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.DiscreteApproximation
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Interpolation
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Tensorization
import TCSlib.BooleanAnalysis.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bobkov's inequalities on the Boolean cube

## Contents

* `Bobkov.TwoPoint`: Gaussian-profile calculus estimates and the scalar inequality.
* `Bobkov.Cube`: coordinate restrictions, derivative identities, and length inequalities.
* `Bobkov.DiscreteApproximation`: quadratic linearization and normalized-block derivative estimates.
* `Bobkov.Interpolation`: symmetric-pair contraction with extra Euclidean coordinates.
* `Bobkov.Noise`: interval preservation and noise/restriction identities.
* `Bobkov.Tensorization`: dimension induction for the extended noise functional.

## Main definitions

* `bobkovFunctional`: the expectation of `sqrt (U(f)² + ∑ᵢ (Dᵢf)²)`.
  The derivatives, expectation, and noise operator are the existing Boolean-analysis ones.

## Main results

* `bobkov_two_point`: the scalar two-point inequality.
* `bobkov_inequality`: the inequality in arbitrary dimension.
* `bobkovFunctional_noise_monotone`: the noise interpolation of Theorem 11.55.

The profile's zero endpoint values use `closedGaussianProfile`, whose interior formula
is reused from Chapter 5. The scalar calculus is factored into `Bobkov.TwoPoint`.
The smooth Gaussian analogue with bounded Lipschitz derivatives is proved separately
in `GaussianBobkov`, using these Boolean inequalities and normalized block convergence.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Bobkov's Inequality (11.15),
  Bobkov's Two-Point Inequality, and Theorem 11.55.
* [Bob97] S. G. Bobkov, *An isoperimetric inequality on the discrete cube, and an
  elementary proof of the isoperimetric inequality in Gauss space*, Annals of
  Probability 25 (1997), 206–214, Proposition 1 and Lemma 1.
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

/-- Bobkov's functional is the expected Euclidean length of the vector consisting
of the Gaussian profile of `f` and all its discrete derivatives.
[OD14, §11.4, equation (11.15)] -/
noncomputable def bobkovFunctional {n : ℕ} (f : BooleanFunc n) : ℝ :=
  expect fun x => Real.sqrt
    (closedGaussianProfile (f x) ^ 2 + ∑ i : Fin n, (derivative i f x) ^ 2)

/-- For `a ± b ∈ [0,1]`, the Gaussian profile at `a` is bounded by the average
of the two lengths `sqrt (U(a ± b)² + b²)`.
[OD14, §11.4, Bobkov's Two-Point Inequality, p. 348]

**Proof sketch.** Follow the elementary calculus argument of [Bob97, Prop. 1].
Convexity of the squared Gaussian quantile gives a lower bound on the symmetric
squared-profile deficit. Concavity of the symmetric squared-profile difference gives
the complementary upper bound. Combine these by squaring the desired inequality,
and include endpoint probabilities by continuity. At endpoint midpoints the
left-hand side is zero. -/
theorem bobkov_two_point (a b : ℝ)
    (hplus : a + b ∈ Set.Icc (0 : ℝ) 1) (hminus : a - b ∈ Set.Icc (0 : ℝ) 1) :
    closedGaussianProfile a ≤
      (Real.sqrt (closedGaussianProfile (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (closedGaussianProfile (a - b) ^ 2 + b ^ 2)) / 2 :=
  by
    have ha : a ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hplus.1, hminus.1], by linarith [hplus.2, hminus.2]⟩
    rcases eq_or_lt_of_le ha.1 with h0 | h0
    · subst a
      rw [closedGaussianProfile_zero]
      positivity
    rcases eq_or_lt_of_le ha.2 with h1 | h1
    · subst a
      rw [closedGaussianProfile_one]
      positivity
    exact closedGaussianProfile_two_point_of_mem_Ioo ⟨h0, h1⟩ hplus hminus

private lemma expect_mem_unitInterval {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : expect f ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simpa only [ThresholdFunctions.expect_const] using
      ThresholdFunctions.expect_mono (f := fun _ => 0) (g := f) (fun x => (hf x).1)
  · simpa only [ThresholdFunctions.expect_const] using
      ThresholdFunctions.expect_mono (f := f) (g := fun _ => 1) (fun x => (hf x).2)

private lemma bobkovFunctional_zero_dim (f : BooleanFunc 0) :
    bobkovFunctional f = closedGaussianProfile (expect f) := by
  simp [bobkovFunctional, expect, uniformWeight, Real.sqrt_sq,
    closedGaussianProfile_nonneg]

private lemma profile_mean_restrictions_le {n : ℕ} (f : BooleanFunc (n + 1))
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    closedGaussianProfile (expect f) ≤
      (Real.sqrt (closedGaussianProfile (expect (Hypercontractivity.restrictLast f false)) ^ 2 +
          expect (Hypercontractivity.diffLast f) ^ 2) +
        Real.sqrt (closedGaussianProfile (expect (Hypercontractivity.restrictLast f true)) ^ 2 +
          expect (Hypercontractivity.diffLast f) ^ 2)) / 2 := by
  let u := expect (Hypercontractivity.restrictLast f false)
  let v := expect (Hypercontractivity.restrictLast f true)
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := expect_mem_unitInterval _ (fun x => hf _)
  have hv : v ∈ Set.Icc (0 : ℝ) 1 := expect_mem_unitInterval _ (fun x => hf _)
  have hp : (u + v) / 2 + (u - v) / 2 = u := by ring
  have hm : (u + v) / 2 - (u - v) / 2 = v := by ring
  simpa only [hp, hm, Hypercontractivity.expect_succ_eq, expect_diffLast, u, v] using
    bobkov_two_point ((u + v) / 2) ((u - v) / 2) (by rwa [hp]) (by rwa [hm])

private lemma sqrt_profile_sq_le {n : ℕ} (f : BooleanFunc n) (d : ℝ)
    (h : closedGaussianProfile (expect f) ≤ bobkovFunctional f) :
    Real.sqrt (closedGaussianProfile (expect f) ^ 2 + d ^ 2) ≤
      Real.sqrt (bobkovFunctional f ^ 2 + d ^ 2) := by
  apply Real.sqrt_le_sqrt
  nlinarith [closedGaussianProfile_nonneg (expect f)]

private lemma restricted_length_identity {n : ℕ} (f : BooleanFunc (n + 1))
    (b : Bool) (x : BoolCube n) :
    Real.sqrt ((Real.sqrt
      (closedGaussianProfile (Hypercontractivity.restrictLast f b x) ^ 2 +
        ∑ i : Fin n, (derivative i (Hypercontractivity.restrictLast f b) x) ^ 2)) ^ 2 +
      (Hypercontractivity.diffLast f x) ^ 2) =
    Real.sqrt (closedGaussianProfile (f (Fin.snoc x b)) ^ 2 +
      ∑ i : Fin (n + 1), (derivative i f (Fin.snoc x b)) ^ 2) := by
  rw [Real.sq_sqrt (by positivity), sum_sq_derivative_snoc]
  simp only [Hypercontractivity.restrictLast, add_assoc]

/-- An induction bound for a restriction extends to its contribution to the
full functional by the triangle inequality for expected lengths. -/
private lemma restriction_contribution_le {n : ℕ} (f : BooleanFunc (n + 1)) (b : Bool)
    (h : closedGaussianProfile (expect (Hypercontractivity.restrictLast f b)) ≤
      bobkovFunctional (Hypercontractivity.restrictLast f b)) :
    Real.sqrt (closedGaussianProfile (expect (Hypercontractivity.restrictLast f b)) ^ 2 +
      expect (Hypercontractivity.diffLast f) ^ 2) ≤
    expect (fun x => Real.sqrt (closedGaussianProfile (f (Fin.snoc x b)) ^ 2 +
      ∑ i : Fin (n + 1), (derivative i f (Fin.snoc x b)) ^ 2)) := by
  refine (sqrt_profile_sq_le _ _ h).trans ?_
  convert sqrt_expect_sq_add_sq_le_expect_sqrt
      (fun x => Real.sqrt
        (closedGaussianProfile (Hypercontractivity.restrictLast f b x) ^ 2 +
          ∑ i : Fin n, (derivative i (Hypercontractivity.restrictLast f b) x) ^ 2))
      (Hypercontractivity.diffLast f) using 1
  congr 1
  funext x
  exact (restricted_length_identity f b x).symm

/-- The Gaussian profile of the mean of a `[0,1]`-valued Boolean-cube function
is at most its Bobkov functional. [OD14, §11.4, Bobkov's Inequality (11.15)]

**Proof sketch.** Induct on the dimension by restricting the last coordinate,
as in [Bob97, Lemma 1]. Apply the two-point inequality to the two restricted means.
The induction hypotheses bound their profiles by the restricted functionals.
The triangle inequality for expected Euclidean lengths incorporates the last
derivative. Average the two bounds; the zero-dimensional case is equality. -/
theorem bobkov_inequality {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    closedGaussianProfile (expect f) ≤ bobkovFunctional f :=
  by
    induction n with
    | zero => exact (bobkovFunctional_zero_dim f).ge
    | succ n ih =>
      refine (profile_mean_restrictions_le f hf).trans ?_
      have hfalse := restriction_contribution_le f false
        (ih (Hypercontractivity.restrictLast f false) (fun x => hf _))
      have htrue := restriction_contribution_le f true
        (ih (Hypercontractivity.restrictLast f true) (fun x => hf _))
      rw [bobkovFunctional, Hypercontractivity.expect_succ_eq]
      exact div_le_div_of_nonneg_right (add_le_add hfalse htrue) (by norm_num)

/-- Boolean noise with correlation in the unit interval decreases Bobkov's
functional. [OD14, Theorem 11.55]

**Proof sketch.** Specialize the extended-functional contraction to the closed
Gaussian profile and the empty vector of carried coordinates. -/
private lemma bobkovFunctional_noise_le {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bobkovFunctional (noiseOp ρ f) ≤ bobkovFunctional f := by
  simpa only [BobkovInterpolation.extendedFunctional, bobkovFunctional,
    Fin.sum_univ_zero, add_zero] using
    BobkovInterpolation.extendedFunctional_noise_le continuousOn_closedGaussianProfile
      (fun x _ => closedGaussianProfile_nonneg x) bobkov_two_point f
      (fun j : Fin 0 => Fin.elim0 j) hf hρ

/-- Bobkov's functional applied to `Tρ f` is increasing in `ρ ∈ [0,1]` for
every `[0,1]`-valued function. [OD14, Thm. 11.55]

**Proof sketch.** Extend the scalar two-point inequality to symmetric pairs
carrying arbitrary Euclidean coordinates. A bounded-supremum maximum principle
replaces the source's stopped-walk argument. Induct on dimension, carrying the
last derivative as an extra coordinate, to prove contraction under noise.
When the larger correlation is positive, use their ratio and the noise semigroup law;
when the larger correlation is zero, both are zero. -/
theorem bobkovFunctional_noise_monotone {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    MonotoneOn (fun ρ : ℝ => bobkovFunctional (noiseOp ρ f)) (Set.Icc (0 : ℝ) 1) := by
  intro ρ hρ σ hσ hle
  rcases eq_or_lt_of_le hσ.1 with rfl | hσpos
  · have hρzero : ρ = 0 := le_antisymm hle hρ.1
    subst ρ
    exact le_rfl
  · have hratio : ρ / σ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hρ.1 hσpos.le, (div_le_one hσpos).2 hle⟩
    have h := bobkovFunctional_noise_le (noiseOp σ f)
      (noiseOp_mem_unitInterval f hf hσ) hratio
    rwa [Hypercontractivity.noiseOp_compose,
      div_mul_cancel₀ ρ (ne_of_gt hσpos)] at h

end BooleanAnalysis.GaussianSpace
