/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite laws of random variables

This file expresses the integral of a function of a random variable with finite support as a
weighted sum over its possible values. It provides a technical bridge from finite weighted
expectations in [OD14, §8.1] to the random-variable arguments in [OD14, §10.2], including
Theorem 10.18 and Exercises 10.19–10.21.

The result extends the probability setting to any finite measure and requires no positive
lower bound on atom masses. An arbitrary real function is integrable against a finite measure
supported on a finite set, so the identity does not depend on the convention for integrals of
nonintegrable functions.

## Main definitions

No new definitions are introduced. This file uses the measure-theoretic setting of
`TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic`.

## Main results

* `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_integral`: computes an integral
  against a finite law as a sum weighted by the measures of the corresponding fibers.
* `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_affine_norm_sq`: computes squared
  affine norms from the same finite-law weights.
* `BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum`: derives
  almost-everywhere two-point support from the two fiber masses.
* `BooleanAnalysis.Hypercontractivity.FiniteLaw.two_point_affine_norm_sq`: specializes the
  affine norm formula to two prescribed probability masses.
* `BooleanAnalysis.Hypercontractivity.FiniteLaw.centered_two_point_moments`: computes
  the zero mean and variance of the centered two-point law.
* `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_probability_atom_weights`: computes
  normalized real fiber weights and transfers their atom lower bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
  §8.1 and §10.2.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity.FiniteLaw

/-- Let `μ` be a finite measure on a measurable space `Ω`, and let `X : Ω → ℝ` be measurable
and belong almost everywhere to a finite set `s`. For every function `f : ℝ → ℝ`, the
integral of `f ∘ X` is the sum of `f x` over `s`, weighted by the measure of each fiber
`{ω | X ω = x}`.

This is a technical reformulation of finite weighted expectation
[OD14, §8.1; Thm 10.18], extended from probability measures to arbitrary finite measures.
No positive atom lower bound is needed. No global measurability or integrability assumption
on `f` is needed either: the law of `X` is finite and supported on `s`, which makes every
real function integrable against that law.

**Proof sketch.** Push `μ` forward along `X`. The almost-everywhere support assumption shows
that restricting this law to `s` leaves it unchanged. Every real function is integrable
against a finite measure on this finite support, and its integral is the sum of its values
weighted by the masses of the atoms. Change of variables identifies this integral with that
of `f ∘ X` and identifies each atom's mass with the measure of the corresponding fiber. -/
theorem finite_law_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (s : Finset ℝ)
    (hX : Measurable X) (hs : ∀ᵐ ω ∂μ, X ω ∈ s) (f : ℝ → ℝ) :
    (∫ ω, f (X ω) ∂μ) = ∑ x ∈ s, (μ {ω | X ω = x}).toReal * f x := by
  have hsupport : ∀ᵐ x ∂μ.map X, x ∈ s :=
    (ae_map_iff hX.aemeasurable s.finite_toSet.measurableSet).2 hs
  have hlaw : (μ.map X).restrict (s : Set ℝ) = μ.map X :=
    Measure.restrict_eq_self_of_ae_mem hsupport
  have hf : Integrable f (μ.map X) := by
    rw [← hlaw]
    exact IntegrableOn.finset
  calc
    (∫ ω, f (X ω) ∂μ) = ∫ x, f x ∂μ.map X :=
      (integral_map hX.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x in (s : Set ℝ), f x ∂μ.map X := by rw [hlaw]
    _ = ∑ x ∈ s, (μ.map X).real {x} • f x :=
      integral_finset s f IntegrableOn.finset
    _ = ∑ x ∈ s, (μ {ω | X ω = x}).toReal * f x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [measureReal_def, Measure.map_apply hX (measurableSet_singleton x),
        smul_eq_mul]
      rfl


/-- For a measurable real random variable supported almost everywhere on a finite set, the
squared `q`-norm of an affine perturbation is the `2 / q` power of its finite weighted
`q`-moment, provided the measure is finite and `q > 0`.

This technical lemma extends the finite weighted-norm computations in
[OD14, §8.1, Definition 9.13, Theorem 10.18] from probability measures to finite measures.
No positive lower bound on atom masses is required; the lower bound may be zero.

**Proof sketch.** Finite support gives finite `q`-norms for the random variable and its affine
perturbation. Raise the norm-moment identity to the power `2 / q` and cancel the exponents
using nonnegativity of the norm. Express the resulting moment as a finite sum weighted by
the masses of the fibers. -/
theorem finite_law_affine_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (s : Finset ℝ)
    (hX : Measurable X) (hs : ∀ᵐ ω ∂μ, X ω ∈ s)
    (q : ℝ) (hq : 0 < q) (a b : ℝ) :
    rvLpNorm (fun ω => a + b * X ω) μ q ^ (2 : ℕ) =
      (∑ x ∈ s, (μ {ω | X ω = x}).toReal * |a + b * x| ^ q) ^ (2 / q) := by
  have hfinite : HasAtomLowerBound X μ 0 := ⟨s, hs, by simp⟩
  have hmem : MemLp (fun ω => a + b * X ω) (ENNReal.ofReal q) μ :=
    (memLp_const a).add ((hfinite.memLp hX (ENNReal.ofReal q)).const_mul b)
  have hmoment := rvLpNorm_rpow (fun ω => a + b * X ω) μ q hq hmem
  rw [finite_law_integral μ X s hX hs (fun x => |a + b * x| ^ q)] at hmoment
  have hnonneg : 0 ≤ rvLpNorm (fun ω => a + b * X ω) μ q :=
    ENNReal.toReal_nonneg
  rw [← Real.rpow_two, ← hmoment, ← Real.rpow_mul hnonneg]
  congr 1
  field_simp [ne_of_gt hq] <;> ring



/--
A measurable real random variable is almost surely supported on two distinct values when
the probabilities of their fibers sum to one.

[OD14, §8.1; Thm10.18, optimality]

Allowing either fiber to have zero mass is a technical extension for this support
computation, which therefore also covers degenerate two-point laws.

**Proof sketch.** The fibers are measurable and disjoint. Their union has probability
one by the assumed mass sum, so membership in that union holds almost everywhere.
-/
theorem ae_two_point_of_mass_sum (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (x y : ℝ)
    (hX : Measurable X) (hxy : x ≠ y)
    (hmass : μ {ω | X ω = x} + μ {ω | X ω = y} = 1) :
    ∀ᵐ ω ∂μ, X ω = x ∨ X ω = y := by
  have hx : MeasurableSet {ω | X ω = x} := measurableSet_eq_fun hX measurable_const
  have hy : MeasurableSet {ω | X ω = y} := measurableSet_eq_fun hX measurable_const
  change ({ω | X ω = x} ∪ {ω | X ω = y}) ∈ ae μ
  apply (mem_ae_iff_prob_eq_one (hx.union hy)).2
  rw [measure_union (Set.disjoint_left.mpr (fun ω hx hy => hxy (hx.symm.trans hy))) hy]
  exact hmass



/-- For a measurable real random variable `X` on a probability space, with masses
`lam` and `1 - lam` at distinct real points `x` and `y`, where `0 ≤ lam ≤ 1`,
this computes the squared `q`-norm of `a + b * X` for every real `q > 0` and
all real coefficients `a` and `b`.

This is a technical finite-law transfer of [OD14, §8.1; Thm10.18]. Endpoint
weights, including null atoms, are allowed only for this norm formula.

**Proof sketch.** The nonnegative weights sum to one, so the prescribed masses
give almost-everywhere support on `{x, y}`. Apply the finite-law affine norm
formula to these two points. Distinctness counts each point once, and the
prescribed masses give the two real weights. -/
theorem two_point_affine_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (x y lam : ℝ) (hX : Measurable X) (hxy : x ≠ y)
    (hlam_nonneg : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (hmass_x : μ {ω | X ω = x} = ENNReal.ofReal lam)
    (hmass_y : μ {ω | X ω = y} = ENNReal.ofReal (1 - lam))
    (q : ℝ) (hq : 0 < q) (a b : ℝ) :
    rvLpNorm (fun ω => a + b * X ω) μ q ^ (2 : ℕ) =
      (lam * |a + b * x| ^ q + (1 - lam) * |a + b * y| ^ q) ^ (2 / q) := by
  classical
  have hmass : μ {ω | X ω = x} + μ {ω | X ω = y} = 1 := by
    rw [hmass_x, hmass_y,
      ← ENNReal.ofReal_add hlam_nonneg (sub_nonneg.mpr hlam_le_one)]
    rw [show lam + (1 - lam) = 1 by ring, ENNReal.ofReal_one]
  have hs : ∀ᵐ ω ∂μ, X ω ∈ ({x, y} : Finset ℝ) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      ae_two_point_of_mass_sum Ω μ X x y hX hxy hmass
  rw [finite_law_affine_norm_sq μ X {x, y} hX hs q hq a b]
  simp [hxy, hmass_x, hmass_y, ENNReal.toReal_ofReal hlam_nonneg,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hlam_le_one)]

/-- For a measurable real random variable `X` on a probability space, with probabilities
`lam` and `1 - lam` at `1 - lam` and `-lam`, respectively, where `0 ≤ lam ≤ 1`,
the mean is zero and the squared `L²` norm is `lam * (1 - lam)`.

This finite-law specialization follows [OD14, §8.1; Thm 10.18, optimality].
The endpoint cases `lam = 0` and `lam = 1` are included as an extension only for
these moment identities.

**Proof sketch.** The two values are distinct and their prescribed probabilities sum
to one, giving almost-everywhere support on `{1 - lam, -lam}` and hence integrability.
The finite-law integral formula expresses the mean as
`lam * (1 - lam) + (1 - lam) * (-lam)`, which is zero. Specialize the two-point
affine norm formula to exponent two and coefficients zero and one. Its weighted
second moment is `lam * (1 - lam)^2 + (1 - lam) * lam^2`, which simplifies to
`lam * (1 - lam)`. -/
theorem centered_two_point_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (lam : ℝ) (hX : Measurable X)
    (hlam_nonneg : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (hmass_pos : μ {ω | X ω = 1 - lam} = ENNReal.ofReal lam)
    (hmass_neg : μ {ω | X ω = -lam} = ENNReal.ofReal (1 - lam)) :
    (∫ ω, X ω ∂μ) = 0 ∧ rvLpNorm X μ 2 ^ (2 : ℕ) = lam * (1 - lam) := by
  classical
  have hxy : 1 - lam ≠ -lam := by linarith
  have hmass : μ {ω | X ω = 1 - lam} + μ {ω | X ω = -lam} = 1 := by
    rw [hmass_pos, hmass_neg,
      ← ENNReal.ofReal_add hlam_nonneg (sub_nonneg.mpr hlam_le_one)]
    rw [show lam + (1 - lam) = 1 by ring, ENNReal.ofReal_one]
  have hs : ∀ᵐ ω ∂μ, X ω ∈ ({1 - lam, -lam} : Finset ℝ) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      ae_two_point_of_mass_sum Ω μ X (1 - lam) (-lam) hX hxy hmass
  constructor
  · calc
      (∫ ω, X ω ∂μ) = lam * (1 - lam) + (1 - lam) * (-lam) := by
        rw [finite_law_integral μ X {1 - lam, -lam} hX hs (fun x => x)]
        simp [hxy, hmass_pos, hmass_neg, ENNReal.toReal_ofReal hlam_nonneg,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hlam_le_one)]
      _ = 0 := by ring
  · have hnorm := two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
      hX hxy hlam_nonneg hlam_le_one hmass_pos hmass_neg 2 (by norm_num) 0 1
    norm_num only [zero_add, one_mul, Real.rpow_two, sq_abs, Real.rpow_one] at hnorm
    rw [hnorm]
    ring


/-- For a measurable real random variable on a probability space, supported
almost everywhere on a finite set `s`, the real fiber weights over `s` sum
to one. If every fiber over `s` has measure at least `ENNReal.ofReal lam`
for a nonnegative real `lam`, then every real fiber weight is at least `lam`.

This is technical finite-law glue for [OD14, §8.1; Proposition 10.17;
Theorem 10.18]. The weight computation includes a zero lower bound and
requires no separate nonempty-support assumption.

**Proof sketch.** Apply the finite-law integral identity to the constant-one
function. Its integral is one under a probability measure, yielding the
weight sum. Each fiber has finite measure, so conversion to a real number
preserves its lower-bound inequality. Nonnegativity of `lam` identifies the
real value of `ENNReal.ofReal lam` with `lam`. -/
theorem finite_probability_atom_weights {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (s : Finset ℝ)
    (hX : Measurable X) (hs : ∀ᵐ ω ∂μ, X ω ∈ s)
    (lam : ℝ) (hlam_nonneg : 0 ≤ lam)
    (hbound : ∀ x ∈ s, ENNReal.ofReal lam ≤ μ {ω | X ω = x}) :
    (∑ x ∈ s, (μ {ω | X ω = x}).toReal) = 1 ∧
      ∀ x ∈ s, lam ≤ (μ {ω | X ω = x}).toReal := by
  constructor
  · simpa using (finite_law_integral μ X s hX hs (fun _ => (1 : ℝ))).symm
  · intro x hx
    simpa only [ENNReal.toReal_ofReal hlam_nonneg] using
      ENNReal.toReal_mono (measure_ne_top μ {ω | X ω = x}) (hbound x hx)


end BooleanAnalysis.Hypercontractivity.FiniteLaw
