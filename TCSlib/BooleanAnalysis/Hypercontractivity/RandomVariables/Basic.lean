/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Definitions for hypercontractivity of general random variables

## Main definitions

* `IsHypercontractive`: affine norm contraction, including infinite exponents.
* `IsSymmetricRV`, `IsRademacherRV`: symmetry and the uniform sign law.
* `evalMultilinearRV`: evaluate existing multilinear polynomials on real random inputs.
* `HasAtomLowerBound`, `sharpDiscreteRadius`: discrete laws and their sharp noise radius.

## Main results

* `rvLpNorm_rpow`: the positive finite-exponent norm raised to its exponent is its absolute
  moment.
* `rvLpNorm_affine_sq`: the second norm of an affine perturbation of a centered variable.
* `IsRademacherRV.map_eq`: the uniform law on the two signs.
* `IsHypercontractive.conjugate`: affine contraction at conjugate exponents.
* `IsHypercontractive.const_mul`: preservation under scalar multiplication.
* `IsHypercontractive.mono_radius`: contraction at smaller radii for centered variables.
* `HasAtomLowerBound.memLp`: integrability at every exponent from finite support.
* `evalMultilinearRV_memLp`: finite fourth moments for independent multilinear inputs.
* `reasonable_moment_algebra`: the algebraic step for the generalized Bonami recurrence.
* `multilinear_sum_insert`: the finite-sum decomposition that splits off one input.
* `integrable_mul_pow_of_memLp`: integrability of mixed monomials up to the available order.
  The hypercontractivity theorems are in `RandomVariables`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Corollary 9.6, Definition 9.13, and §10.2.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random variable is `(p,q,ρ)`-hypercontractive when every affine perturbation contracts
from its finite `p`-norm to its `q`-norm after scaling the nonconstant part by `ρ`.
Extended nonnegative exponents include infinity. [OD14, Def. 9.13] -/
def IsHypercontractive (X : Ω → ℝ) (μ : Measure Ω) (p q : ℝ≥0∞) (ρ : ℝ) : Prop :=
  1 ≤ p ∧ p ≤ q ∧ 0 ≤ ρ ∧ ρ < 1 ∧ MemLp X q μ ∧
    ∀ a b : ℝ, eLpNorm (fun ω => a + ρ * b * X ω) q μ ≤
      eLpNorm (fun ω => a + b * X ω) p μ

/-- The real-valued `q`-norm is used with finite-norm hypotheses to avoid totalizing
an infinite norm to zero. [OD14, §10.2] -/
noncomputable def rvLpNorm (X : Ω → ℝ) (μ : Measure Ω) (q : ℝ) : ℝ :=
  (eLpNorm X (ENNReal.ofReal q) μ).toReal

/-- A symmetric variable has the same distribution as its negative.
[OD14, §10.2, preceding Prop. 10.12] -/
def IsSymmetricRV (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  IdentDistrib X (fun ω => -X ω) μ μ

/-- A Rademacher variable is a measurable uniform random sign.
[OD14, §10.2, randomization preceding Thm. 10.13] -/
def IsRademacherRV (r : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable r ∧ (∀ᵐ ω ∂μ, r ω = -1 ∨ r ω = 1) ∧
    μ {ω | r ω = 1} = (1 / 2 : ℝ≥0∞) ∧ μ {ω | r ω = -1} = (1 / 2 : ℝ≥0∞)

/-- Evaluate a multilinear polynomial using real random inputs; the sample space need
not be finite. [OD14, Cor. 9.6] -/
noncomputable def evalMultilinearRV {n : ℕ}
    (F : ThresholdFunctions.MultilinearPolynomial n) (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ S : Finset (Fin n), F S * ∏ i ∈ S, X i ω

/-- A discrete law has atom masses at least `lam` when a finite set supports it almost
surely and every listed atom has that minimum mass. For positive `lam` this captures the
source's positive minimum probability, without restricting the sample space.
[OD14, Prop. 10.17] -/
def HasAtomLowerBound (X : Ω → ℝ) (μ : Measure Ω) (lam : ℝ) : Prop :=
  ∃ s : Finset ℝ, (∀ᵐ ω ∂μ, X ω ∈ s) ∧
    ∀ x ∈ s, ENNReal.ofReal lam ≤ μ {ω | X ω = x}

/-- For positive `q`, the `q`-th power of the finite real-valued `q`-norm equals the
`q`-th absolute moment. [OD14, §10.2] This norm identity is stated for an arbitrary
measure space.

**Proof sketch.** Express the norm as the reciprocal power of the absolute moment
using the integral formula for the finite `Lp` norm. The moment is nonnegative,
and raising to `q` cancels the reciprocal exponent. -/
theorem rvLpNorm_rpow (X : Ω → ℝ) (μ : Measure Ω) (q : ℝ)
    (hq : 0 < q) (hX : MemLp X (ENNReal.ofReal q) μ) :
    rvLpNorm X μ q ^ q = ∫ ω, |X ω| ^ q ∂μ := by
  unfold rvLpNorm
  rw [MemLp.eLpNorm_eq_integral_rpow_norm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hX]
  simp only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs]
  have hI : 0 ≤ ∫ ω, |X ω| ^ q ∂μ :=
    integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),
    ← Real.rpow_mul hI, inv_mul_cancel₀ hq.ne', Real.rpow_one]

/-- For a mean-zero random variable with finite second norm, the squared second norm
of `a + b * X` is `a²` plus `b²` times the squared second norm of `X`.
[OD14, Prop. 10.8 (proof)]

**Proof sketch.** Express squared second norms as second moments and expand the
square. Integrate each term: the mixed term vanishes by centering, and the constant
term integrates to itself because the measure is a probability measure. -/
theorem rvLpNorm_affine_sq (X : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hmem : MemLp X 2 μ) (hmean : ∫ ω, X ω ∂μ = 0) (a b : ℝ) :
    rvLpNorm (fun ω => a + b * X ω) μ 2 ^ 2 =
      a ^ 2 + b ^ 2 * rvLpNorm X μ 2 ^ 2 := by
  have hA : MemLp (fun ω => a + b * X ω) 2 μ :=
    (memLp_const a).add (hmem.const_mul b)
  have hXint : Integrable X μ :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hmem
  have hXsecond : (∫ ω, X ω ^ 2 ∂μ) = rvLpNorm X μ 2 ^ 2 := by
    simpa only [Real.rpow_two, sq_abs] using
      (rvLpNorm_rpow X μ 2 (by norm_num) (by simpa using hmem)).symm
  have hm := rvLpNorm_rpow (fun ω => a + b * X ω) μ 2
    (by norm_num) (by simpa using hA)
  simp only [Real.rpow_two, sq_abs] at hm
  rw [hm]
  calc
    _ = ∫ ω, a ^ 2 + 2 * a * b * X ω + b ^ 2 * X ω ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    _ = (∫ ω, a ^ 2 + 2 * a * b * X ω ∂μ) +
        (∫ ω, b ^ 2 * X ω ^ 2 ∂μ) := by
      simpa only [Pi.add_apply] using
        integral_add
          ((integrable_const (a ^ 2)).add (hXint.const_mul (2 * a * b)))
          (hmem.integrable_sq.const_mul (b ^ 2))
    _ = ((∫ ω, a ^ 2 ∂μ) + (∫ ω, 2 * a * b * X ω ∂μ)) +
        (∫ ω, b ^ 2 * X ω ^ 2 ∂μ) := by
      simpa only [Pi.add_apply] using
        congrArg (fun z : ℝ => z + ∫ ω, b ^ 2 * X ω ^ 2 ∂μ)
          (integral_add (integrable_const (a ^ 2)) (hXint.const_mul (2 * a * b)))
    _ = a ^ 2 + b ^ 2 * rvLpNorm X μ 2 ^ 2 := by
      simp [integral_const_mul, hmean, hXsecond]

/-- A Rademacher random variable has the uniform probability law on the two signs
[OD14, §10.2, Lem. 10.15].

**Proof sketch.** For each measurable set, split its preimage according to the two
possible signs. The almost-everywhere sign condition removes the remaining part,
and each sign has measure one half. These are exactly the values of the stated
sum of Dirac measures. -/
theorem IsRademacherRV.map_eq {r : Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hr : IsRademacherRV r μ) :
    μ.map r =
      (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
        (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) := by
  let R : Measure ℝ :=
    (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)
  change μ.map r = R
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hr.1 hs]
  by_cases hp : (1 : ℝ) ∈ s
  · by_cases hm : (-1 : ℝ) ∈ s
    · have he : r ⁻¹' s =ᵐ[μ] Set.univ := by
        filter_upwards [hr.2.1] with ω hω
        apply propext
        change r ω ∈ s ↔ True
        rcases hω with hω | hω <;> norm_num [hω, hp, hm]
      rw [measure_congr he]
      norm_num [R, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply, hs, hp, hm]
      simpa only [one_div] using (ENNReal.add_halves (1 : ℝ≥0∞)).symm
    · have he : r ⁻¹' s =ᵐ[μ] {ω | r ω = 1} := by
        filter_upwards [hr.2.1] with ω hω
        apply propext
        change r ω ∈ s ↔ r ω = 1
        rcases hω with hω | hω <;> norm_num [hω, hp, hm]
      rw [measure_congr he, hr.2.2.1]
      simp [R, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply, hs, hp, hm]
  · by_cases hm : (-1 : ℝ) ∈ s
    · have he : r ⁻¹' s =ᵐ[μ] {ω | r ω = -1} := by
        filter_upwards [hr.2.1] with ω hω
        apply propext
        change r ω ∈ s ↔ r ω = -1
        rcases hω with hω | hω <;> norm_num [hω, hp, hm]
      rw [measure_congr he, hr.2.2.2]
      simp [R, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply, hs, hp, hm]
    · have he : r ⁻¹' s =ᵐ[μ] (∅ : Set Ω) := by
        filter_upwards [hr.2.1] with ω hω
        apply propext
        change r ω ∈ s ↔ False
        rcases hω with hω | hω <;> norm_num [hω, hp, hm]
      rw [measure_congr he]
      simp [R, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply, hs, hp, hm]

/-- For `q > 2`, centered `(2, q, ρ)`-hypercontractivity implies
`(q / (q - 1), 2, ρ)`-hypercontractivity [OD14, Prop. 10.8].
Centering is an explicit additional hypothesis here; the source derives it from
Fact 10.7(1).

**Proof sketch.** Given `f = a + bX`, set `Z = a + ρbX` and `g = a + ρ²bX`.
Centering gives `∫ f * g = ∫ Z²`. Hölder's inequality with conjugate exponents
`q / (q - 1)` and `q`, followed by the assumed contraction applied to `Z`, bounds
`‖Z‖₂²` by `‖f‖_{q/(q-1)} * ‖Z‖₂`. Cancel `‖Z‖₂` when it is positive and
handle the zero case separately. The exponent, parameter, and integrability
conditions follow from `q > 2` and the original hypercontractivity assumptions. -/
theorem IsHypercontractive.conjugate {X : Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {q ρ : ℝ} (hq : 2 < q)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (h : IsHypercontractive X μ 2 (ENNReal.ofReal q) ρ) :
    IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2 ρ := by
  rcases h with ⟨_, _, hρ0, hρ1, hXq, hcontract⟩
  let p : ℝ := q / (q - 1)
  have hden : 0 < q - 1 := by linarith
  have hp : 1 ≤ p ∧ p ≤ 2 := by
    dsimp [p]
    constructor
    · rw [le_div_iff₀ hden]
      linarith
    · rw [div_le_iff₀ hden]
      linarith
  have hpE : 1 ≤ ENNReal.ofReal p ∧ ENNReal.ofReal p ≤ 2 := by
    constructor
    · calc
        1 = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp.1
    · calc
        ENNReal.ofReal p ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hp.2
        _ = 2 := by norm_num
  have hX2 : MemLp X 2 μ := hXq.mono_exponent (by
    calc
      2 = ENNReal.ofReal 2 := by norm_num
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq.le)
  have hc : Real.HolderConjugate p q := by
    simpa [p, Real.conjExponent] using
      (Real.HolderConjugate.conjExponent (show 1 < q by linarith)).symm
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    hc.ennrealOfReal
  refine ⟨hpE.1, hpE.2, hρ0, hρ1, hX2, ?_⟩
  intro a b
  let f : Ω → ℝ := fun ω => a + b * X ω
  let Z : Ω → ℝ := fun ω => a + (ρ * b) * X ω
  let g : Ω → ℝ := fun ω => a + (ρ * (ρ * b)) * X ω
  have hf2 : MemLp f 2 μ := (memLp_const a).add (hX2.const_mul b)
  have hZ2 : MemLp Z 2 μ := (memLp_const a).add (hX2.const_mul (ρ * b))
  have hgq : MemLp g (ENNReal.ofReal q) μ :=
    (memLp_const a).add (hXq.const_mul (ρ * (ρ * b)))
  have hfp : MemLp f (ENNReal.ofReal p) μ := hf2.mono_exponent hpE.2
  have hXint : Integrable X μ :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hX2
  have hZsq : Integrable (fun ω => |Z ω| ^ (2 : ℕ)) μ := by
    simpa only [sq_abs] using hZ2.integrable_sq
  have hproduct : (∫ ω, f ω * g ω ∂μ) = rvLpNorm Z μ 2 ^ 2 := by
    have hsq := rvLpNorm_rpow Z μ 2 (by norm_num) (by simpa using hZ2)
    simp only [Real.rpow_two] at hsq
    calc
      _ = ∫ ω, |Z ω| ^ 2 + (a * b * (1 - ρ) ^ 2) * X ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [f, Z, g]
        rw [sq_abs]
        ring
      _ = (∫ ω, |Z ω| ^ 2 ∂μ) +
          (a * b * (1 - ρ) ^ 2) * (∫ ω, X ω ∂μ) := by
        rw [integral_add hZsq (hXint.const_mul _), integral_const_mul]
      _ = rvLpNorm Z μ 2 ^ 2 := by
        rw [hmean]
        simpa using hsq.symm
  have hcontract' : eLpNorm g (ENNReal.ofReal q) μ ≤ eLpNorm Z 2 μ :=
    hcontract a (ρ * b)
  have hbound : ENNReal.ofReal (rvLpNorm Z μ 2 ^ 2) ≤
      eLpNorm f (ENNReal.ofReal p) μ * eLpNorm Z 2 μ := by
    calc
      _ = ‖∫ ω, f ω * g ω ∂μ‖ₑ := by
        rw [hproduct, Real.enorm_eq_ofReal (sq_nonneg _)]
      _ ≤ eLpNorm (fun ω => f ω * g ω) 1 μ := by
        simpa only [eLpNorm_one_eq_lintegral_enorm] using
          (enorm_integral_le_lintegral_enorm (fun ω => f ω * g ω))
      _ ≤ eLpNorm f (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          (eLpNorm_smul_le_mul_eLpNorm
            (p := ENNReal.ofReal p) (q := ENNReal.ofReal q) (r := 1) hgq.1 hfp.1)
      _ ≤ eLpNorm f (ENNReal.ofReal p) μ * eLpNorm Z 2 μ :=
        mul_le_mul_left' hcontract' _
  have hreal : rvLpNorm Z μ 2 ^ 2 ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal * rvLpNorm Z μ 2 := by
    have ht := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hfp.2.ne hZ2.2.ne)).mpr hbound
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
      rvLpNorm, ENNReal.ofReal_ofNat] using ht
  change eLpNorm Z 2 μ ≤ eLpNorm f (ENNReal.ofReal p) μ
  apply (ENNReal.toReal_le_toReal hZ2.2.ne hfp.2.ne).mp
  suffices hfinal : rvLpNorm Z μ 2 ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal by
    simpa only [rvLpNorm, ENNReal.ofReal_ofNat] using hfinal
  by_cases hz : rvLpNorm Z μ 2 = 0
  · rw [hz]
    exact ENNReal.toReal_nonneg
  · have hzpos : 0 < rvLpNorm Z μ 2 :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
    exact (mul_le_mul_right hzpos).mp (by simpa only [pow_two] using hreal)

/--
Scalar multiplication preserves hypercontractivity [OD14, Fact 10.7(2)].

This statement allows an arbitrary measure because the argument does not use
the probability-measure assumption.

**Proof sketch.** Scalar multiplication preserves `MemLp`. Apply the norm
inequality for `X` with coefficients `a` and `b * c`, then reassociate the
products.
-/
theorem IsHypercontractive.const_mul
    {X : Ω → ℝ} {μ : Measure Ω} {p q : ENNReal} {ρ : ℝ}
    (h : IsHypercontractive X μ p q ρ) (c : ℝ) :
    IsHypercontractive (fun ω => c * X ω) μ p q ρ := by
  rcases h with ⟨hp, hpq, hρ, hρ1, hX, hbound⟩
  refine ⟨hp, hpq, hρ, hρ1, hX.const_mul c, ?_⟩
  intro a b
  simpa only [mul_assoc] using hbound a (b * c)

/-- Hypercontractivity is monotone in the radius [OD14, Fact 10.7(3)].

Centeredness is supplied explicitly as `hmean`, rather than derived using
[OD14, Fact 10.7(1)].

**Proof sketch.** If `ρ = 0`, the radius inequalities force `σ = 0`, so the
original hypothesis applies. Otherwise, put `θ = σ / ρ`, which lies in `[0, 1]`.
Write the affine function at radius `σ` as the convex combination, with weights
`θ` and `1 - θ`, of the affine function at radius `ρ` and the constant `a`.
Minkowski's inequality and the original hypercontractive inequality control
the first term. Centeredness identifies `a` with the mean of the uncontracted
affine function, so its absolute value is bounded by that function's `p`-norm.
This bounds the second term and proves the desired inequality. These bounds
also hold when either exponent is infinity. -/
theorem IsHypercontractive.mono_radius
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ENNReal} {ρ σ : ℝ}
    (h : IsHypercontractive X μ p q ρ)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hσ0 : 0 ≤ σ) (hσρ : σ ≤ ρ) :
    IsHypercontractive X μ p q σ := by
  by_cases hρzero : ρ = 0
  · have hσzero : σ = 0 := le_antisymm (hρzero ▸ hσρ) hσ0
    simpa [hσzero, hρzero] using h
  rcases h with ⟨hp1, hpq, hρ0, hρlt, hmem, hcontract⟩
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρzero)
  have hq1 : (1 : ENNReal) ≤ q := hp1.trans hpq
  have hq_ne : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq1)
  let θ : ℝ := σ / ρ
  have hθ0 : 0 ≤ θ := div_nonneg hσ0 hρ0
  have hθ1 : θ ≤ 1 := (div_le_one hρpos).2 hσρ
  have h1θ0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  refine ⟨hp1, hpq, hσ0, hσρ.trans_lt hρlt, hmem, ?_⟩
  intro a b
  have hconst : MemLp (fun _ : Ω => a) q μ := memLp_const a
  have hinput : MemLp (fun ω => a + b * X ω) q μ :=
    hconst.add (hmem.const_mul b)
  have hlarge : MemLp (fun ω => a + ρ * b * X ω) q μ :=
    hconst.add (hmem.const_mul (ρ * b))
  have hintegral : (∫ ω, (a + b * X ω) ∂μ) = a := by
    rw [integral_add (MemLp.integrable hq1 hconst)
      (MemLp.integrable hq1 (hmem.const_mul b)),
      integral_const_mul, hmean]
    simp
  have hconst_norm : eLpNorm (fun _ : Ω => a) q μ = ‖a‖ₑ := by
    simpa using eLpNorm_const a hq_ne (NeZero.ne μ)
  have hconst_le :
      eLpNorm (fun _ : Ω => a) q μ ≤
        eLpNorm (fun ω => a + b * X ω) p μ := by
    rw [hconst_norm]
    calc
      ‖a‖ₑ = ‖∫ ω, (a + b * X ω) ∂μ‖ₑ := by rw [hintegral]
      _ ≤ ∫⁻ ω, ‖a + b * X ω‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun ω => a + b * X ω) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ eLpNorm (fun ω => a + b * X ω) p μ :=
        eLpNorm_le_eLpNorm_of_exponent_le hp1 hinput.aestronglyMeasurable
  have hconvex :
      (fun ω => a + σ * b * X ω) =
        θ • (fun ω => a + ρ * b * X ω) +
          (1 - θ) • (fun _ : Ω => a) := by
    ext ω
    change a + σ * b * X ω =
      θ * (a + ρ * b * X ω) + (1 - θ) * a
    dsimp [θ]
    field_simp [hρzero]
    <;> ring
  rw [hconvex]
  calc
    eLpNorm
        (θ • (fun ω => a + ρ * b * X ω) +
          (1 - θ) • (fun _ : Ω => a)) q μ
      ≤ eLpNorm (θ • (fun ω => a + ρ * b * X ω)) q μ +
          eLpNorm ((1 - θ) • (fun _ : Ω => a)) q μ :=
        eLpNorm_add_le
          (hlarge.const_mul θ).aestronglyMeasurable
          (hconst.const_mul (1 - θ)).aestronglyMeasurable hq1
    _ = ‖θ‖ₑ * eLpNorm (fun ω => a + ρ * b * X ω) q μ +
        ‖1 - θ‖ₑ * eLpNorm (fun _ : Ω => a) q μ := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
    _ ≤ ‖θ‖ₑ * eLpNorm (fun ω => a + b * X ω) p μ +
        ‖1 - θ‖ₑ * eLpNorm (fun ω => a + b * X ω) p μ :=
      add_le_add (mul_le_mul_left' (hcontract a b) _)
        (mul_le_mul_left' hconst_le _)
    _ = eLpNorm (fun ω => a + b * X ω) p μ := by
      rw [Real.enorm_eq_ofReal hθ0, Real.enorm_eq_ofReal h1θ0,
        ← add_mul, ← ENNReal.ofReal_add hθ0 h1θ0]
      have hsum : θ + (1 - θ) = 1 := by ring
      rw [hsum, ENNReal.ofReal_one, one_mul]

/-- A measurable real-valued function with `HasAtomLowerBound` belongs to `MemLp`
for every extended exponent, including infinity, on a finite measure space
[OD14, Prop. 10.17].

This extends the source's probability-measure setting to finite measures. Only
the almost-everywhere finite-support clause is used; the atom-mass condition
and the value or sign of `lam` are irrelevant.

**Proof sketch.** Extract the finite support and bound the norm of each supported
value by the sum of the norms of all support points. This gives an almost-everywhere
uniform bound. Apply `MemLp.of_bound` using measurability and finiteness of the measure. -/
theorem HasAtomLowerBound.memLp
    {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {lam : ℝ}
    (h : HasAtomLowerBound X μ lam) (hX : Measurable X) (p : ENNReal) :
    MemLp X p μ := by
  classical
  obtain ⟨s, hs, _⟩ := h
  apply MemLp.of_bound hX.aestronglyMeasurable (∑ x ∈ s, ‖x‖)
  filter_upwards [hs] with ω hω
  exact Finset.single_le_sum (fun x _ => norm_nonneg x) hω

/-- Every multilinear polynomial evaluated on mutually independent real random variables
with finite fourth moments on a probability space belongs to `L⁴`.
[OD14, Cor. 9.6] This establishes integrability only, isolating the finite-moment component
of the source's stronger reasonability bound. The degree, vanishing first and third
moments, and input reasonability assumptions needed for that bound are omitted here.

**Proof sketch.** Induct over each monomial's finite set of inputs. Mutual independence
makes the fourth power of the new input's norm independent of the fourth power of the
preceding product's norm. Apply `IndepFun.integrable_mul` and
`integrable_norm_rpow_iff` to obtain membership in `L⁴` without requiring higher moments.
Scalar multiplication by each coefficient and a finite sum finish the argument. -/
theorem evalMultilinearRV_memLp {n : ℕ}
    (F : ThresholdFunctions.MultilinearPolynomial n) (X : Fin n → Ω → ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hindep : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ) :
    MemLp (evalMultilinearRV F X) 4 μ := by
  classical
  have hprod : ∀ S : Finset (Fin n), MemLp (∏ i ∈ S, X i) 4 μ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa using (memLp_const (μ := μ) (p := 4) (1 : ℝ))
    | insert i S hi hS =>
        rw [Finset.prod_insert hi]
        have hm : AEStronglyMeasurable (X i * ∏ j ∈ S, X j) μ :=
          (hX i).aestronglyMeasurable.mul hS.aestronglyMeasurable
        have hind : IndepFun (X i) (∏ j ∈ S, X j) μ :=
          (hindep.indepFun_finset_prod_of_notMem₀
            (fun j => (hX j).aestronglyMeasurable.aemeasurable) hi).symm
        have hp := hind.comp
          (φ := fun x : ℝ => ‖x‖ ^ (4 : ℕ))
          (ψ := fun x : ℝ => ‖x‖ ^ (4 : ℕ))
          (by fun_prop) (by fun_prop)
        have hI := hp.integrable_mul
          ((hX i).integrable_norm_pow' (p := 4))
          (hS.integrable_norm_pow' (p := 4))
        change Integrable (fun ω =>
          ‖X i ω‖ ^ (4 : ℕ) * ‖(∏ j ∈ S, X j) ω‖ ^ (4 : ℕ)) μ at hI
        apply (integrable_norm_rpow_iff hm
          (by norm_num : (4 : ℝ≥0∞) ≠ 0)
          (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).mp
        simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat,
          Pi.mul_apply, norm_mul, mul_pow] using hI
  unfold evalMultilinearRV
  refine memLp_finset_sum Finset.univ (fun S _ => ?_)
  simpa only [Finset.prod_apply] using (hprod S).const_mul (F S)

/-- If `R ≥ 9`, `a`, `b`, `C`, and `D` are nonnegative, and
`A ≤ R a²`, `D ≤ b²`, and `C² ≤ A D`, then
`A + 6 C + R D ≤ R (a + b)²`.
This scaled algebraic inequality generalizes the constant-9 closing step of
[OD14, Cor. 9.6] to every `R ≥ 9`, allowing its use with `R = max B 9`.

**Proof sketch.** Multiply the bounds using nonnegativity to obtain
`C² ≤ R a² b²`. Since `R ≥ 9`, this gives `(3 C)² ≤ (R a b)²`.
Both `3 C` and `R a b` are nonnegative, so `3 C ≤ R a b`.
Add `A ≤ R a²`, `6 C ≤ 2 R a b`, and `R D ≤ R b²`, then expand
`R (a + b)²`. -/
theorem reasonable_moment_algebra (R a b A D C : ℝ)
    (hR : 9 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hA : A ≤ R * a ^ 2) (hD_bound : D ≤ b ^ 2)
    (hC_sq : C ^ 2 ≤ A * D) :
    A + 6 * C + R * D ≤ R * (a + b) ^ 2 := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRa : 0 ≤ R * a ^ 2 := mul_nonneg hR0 (sq_nonneg a)
  have hprod : C ^ 2 ≤ R * a ^ 2 * b ^ 2 :=
    hC_sq.trans (mul_le_mul hA hD_bound hD hRa)
  have hRR : 9 * R ≤ R ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hR hR0
  have hscale : (3 * C) ^ 2 ≤ (R * a * b) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hRR
      (mul_nonneg (sq_nonneg a) (sq_nonneg b))
    nlinarith only [hprod, hm]
  have hcross : 3 * C ≤ R * a * b := by
    exact (pow_le_pow_iff_left₀
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC)
      (mul_nonneg (mul_nonneg hR0 ha) hb)
      (by decide : (2 : ℕ) ≠ 0)).mp hscale
  have hRD : R * D ≤ R * b ^ 2 :=
    mul_le_mul_of_nonneg_left hD_bound hR0
  nlinarith only [hA, hRD, hcross]

/-- For a finite set `s` and an index `i ∉ s`, the multilinear sum over subsets of
`insert i s` equals the sum over subsets of `s` plus `X i ω` times the sum with
coefficients `F (insert i T)`.
This isolates the finite algebraic decomposition `F = A + x_i D` used in the
Bonami induction for [OD14, Cor. 9.6], and holds for arbitrary real inputs
without probability, measurability, degree, or moment assumptions.

**Proof sketch.** Partition the subsets according to whether they contain `i`
using `Finset.sum_powerset_insert`. Every subset `T` of `s` omits `i`, so
`Finset.prod_insert` factors its inserted monomial as `X i ω` times the
original product over `T`. Distribute this factor across the finite sum and
reassociate the products. -/
theorem multilinear_sum_insert {Ω ι : Type*} [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s)
    (F : Finset ι → ℝ) (X : ι → Ω → ℝ) (ω : Ω) :
    (∑ T ∈ (insert i s).powerset, F T * ∏ j ∈ T, X j ω) =
      (∑ T ∈ s.powerset, F T * ∏ j ∈ T, X j ω) +
        X i ω * (∑ T ∈ s.powerset, F (insert i T) * ∏ j ∈ T, X j ω) := by
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hiT : i ∉ T := fun h => hi ((Finset.mem_powerset.mp hT) h)
  rw [Finset.prod_insert hiT]
  ring

/-- On a finite measure space, a mixed monomial of two real `MemLp` functions is
integrable whenever its total natural degree is at most their natural exponent.

This is a technical integrability lemma supporting the proof of [OD14, Cor. 9.6],
rather than the moment bound stated there.

**Proof sketch.** If `p = 0`, both degrees vanish and the product is constant.
Otherwise, `1 + ‖f‖ + ‖g‖` belongs to `MemLp` at exponent `p` and is at least one.
Its `p`-th power is integrable and dominates the norm of the mixed monomial;
combine this domination with almost-everywhere strong measurability.
-/
theorem integrable_mul_pow_of_memLp
    {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → ℝ} {p a b : ℕ}
    (hf : MemLp f (p : ℝ≥0∞) μ) (hg : MemLp g (p : ℝ≥0∞) μ)
    (hab : a + b ≤ p) :
    Integrable (fun ω => f ω ^ a * g ω ^ b) μ := by
  by_cases hp : p = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    simpa using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
  · let z : Ω → ℝ := fun ω => 1 + ‖f ω‖ + ‖g ω‖
    have h_one : MemLp (fun _ : Ω => (1 : ℝ)) (p : ℝ≥0∞) μ :=
      memLp_const 1
    have hz : MemLp z (p : ℝ≥0∞) μ :=
      (h_one.add hf.norm).add hg.norm
    refine hz.integrable_norm_pow'.mono'
      ((hf.aestronglyMeasurable.pow a).mul (hg.aestronglyMeasurable.pow b)) ?_
    filter_upwards [] with ω
    have hz_one : 1 ≤ z ω := by
      dsimp [z]
      linarith [abs_nonneg (f ω), abs_nonneg (g ω)]
    have hz_f : ‖f ω‖ ≤ z ω := by
      dsimp [z]
      linarith [abs_nonneg (g ω)]
    have hz_g : ‖g ω‖ ≤ z ω := by
      dsimp [z]
      linarith [abs_nonneg (f ω)]
    have hz_nonneg : 0 ≤ z ω := le_trans zero_le_one hz_one
    rw [norm_mul, norm_pow, norm_pow, Real.norm_of_nonneg hz_nonneg]
    calc
      ‖f ω‖ ^ a * ‖g ω‖ ^ b ≤ z ω ^ a * z ω ^ b :=
        mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg (f ω)) hz_f a)
          (pow_le_pow_left₀ (norm_nonneg (g ω)) hz_g b)
          (pow_nonneg (norm_nonneg (g ω)) b)
          (pow_nonneg hz_nonneg a)
      _ = z ω ^ (a + b) := (pow_add (z ω) a b).symm
      _ ≤ z ω ^ p := pow_le_pow_right₀ hz_one hab

end BooleanAnalysis.Hypercontractivity
