/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesFiniteLaw
import TCSlib.BooleanAnalysis.Hypercontractivity.BiasedTwoPointContraction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp hypercontractivity for two-point random variables

This module transfers the sharp weighted two-point inequality to measurable real random
variables with the centered two-point law. Both conjugate directions and the necessary
radius bound provide the two-point ingredients for optimality in [OD14, Theorem 10.18].

## Main definitions

No new definitions are introduced. This module uses `IsHypercontractive` and
`sharpDiscreteRadius` from the random-variable and parameter layers.

## Main results

* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_conjugate_sharp`:
  the centered two-point law contracts from the conjugate exponent of `q > 2` to
  exponent two at the sharp discrete radius.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_conjugate_radius_le`:
  conjugate-to-two contraction forces the radius to be at most the sharp radius.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_forward_sharp`:
  the centered two-point law contracts from exponent two to q at the sharp radius.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercise 10.20(b), equation (10.35), and Theorem 10.18.
-/

open MeasureTheory

namespace BooleanAnalysis.Hypercontractivity.SharpDiscrete

/-- For `q > 2` and `0 < lam < 1 / 2`, a measurable real random variable on a probability
space with mass `lam` at `1 - lam` and mass `1 - lam` at `-lam` is hypercontractive from
the conjugate exponent `q / (q - 1)` to exponent two at the sharp discrete radius.

This is the random-variable form of the sharp weighted two-point inequality
[OD14, Exercise 10.20(b), equation (10.35), Theorem 10.18]. The sample space may be any
measurable space: the two prescribed masses imply almost-everywhere two-point support
and centering, so neither is an additional hypothesis.

**Proof sketch.** Set the input exponent to the conjugate of `q`. It lies strictly between
one and two, and its conjugate is `q`; the sharp radius lies strictly between zero and
one. The fiber masses sum to one, giving almost-everywhere support on the two values
and hence finite norms at every exponent. For an affine input with coefficients `a`
and `b`, its two values are `a + b * (1 - lam)` and `a - b * lam`. Their weighted mean
is `a`, and their difference is `b`. Apply the sharp weighted two-point inequality.
The finite-law norm formulas identify its right-hand side with the squared input norm
and its left-hand side with the squared noisy second norm. Nonnegativity of the real
norms gives the norm comparison; finiteness transfers it to the extended norms used
in hypercontractivity. -/
theorem two_point_conjugate_sharp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (q lam : ℝ) (hX : Measurable X) (hq : 2 < q)
    (hlam0 : 0 < lam) (hlamhalf : lam < 1 / 2)
    (hmass_pos : μ {ω | X ω = 1 - lam} = ENNReal.ofReal lam)
    (hmass_neg : μ {ω | X ω = -lam} = ENNReal.ofReal (1 - lam)) :
    IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2
      (sharpDiscreteRadius q lam) := by
  classical
  let p : ℝ := q / (q - 1)
  have hqsub : 0 < q - 1 := by linarith
  have hp1 : 1 < p := by
    dsimp only [p]
    apply (lt_div_iff₀ hqsub).2
    linarith
  have hp2 : p < 2 := by
    dsimp only [p]
    apply (div_lt_iff₀ hqsub).2
    linarith
  have hconj : p / (p - 1) = q := by
    apply (div_eq_iff (sub_ne_zero.mpr (ne_of_gt hp1))).2
    dsimp only [p]
    field_simp [ne_of_gt hqsub]
    ring
  have hlam1 : lam ≤ 1 := by linarith
  have hxy : 1 - lam ≠ -lam := by linarith
  -- The prescribed masses give finite support and hence finite norms.
  have hmass : μ {ω | X ω = 1 - lam} + μ {ω | X ω = -lam} = 1 := by
    rw [hmass_pos, hmass_neg,
      ← ENNReal.ofReal_add hlam0.le (sub_nonneg.mpr hlam1)]
    rw [show lam + (1 - lam) = 1 by ring, ENNReal.ofReal_one]
  have hfinite : HasAtomLowerBound X μ 0 := by
    refine ⟨{1 - lam, -lam}, ?_, by simp⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      FiniteLaw.ae_two_point_of_mass_sum Ω μ X (1 - lam) (-lam) hX hxy hmass
  have hr := radius_pos_lt_one q lam hq hlam0 hlamhalf
  refine ⟨ENNReal.one_le_ofReal.mpr hp1.le, ?_, hr.1.le, hr.2,
    hfinite.memLp hX 2, ?_⟩
  · simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2.le
  · intro a b
    have houtmem : MemLp (fun ω => a + sharpDiscreteRadius q lam * b * X ω) 2 μ :=
      (memLp_const a).add ((hfinite.memLp hX 2).const_mul (sharpDiscreteRadius q lam * b))
    have hinmem : MemLp (fun ω => a + b * X ω) (ENNReal.ofReal p) μ :=
      (memLp_const a).add ((hfinite.memLp hX (ENNReal.ofReal p)).const_mul b)
    -- The affine values have weighted mean a and difference b.
    have hscalar := weighted_biased_two_point_le p lam
      (a + b * (1 - lam)) (a + b * (-lam)) hp1 hp2 hlam0 hlamhalf
    rw [hconj,
      show lam * (a + b * (1 - lam)) + (1 - lam) * (a + b * (-lam)) = a by ring,
      show (a + b * (1 - lam)) - (a + b * (-lam)) = b by ring] at hscalar
    have hsquare :
        rvLpNorm (fun ω => a + sharpDiscreteRadius q lam * b * X ω) μ 2 ^ 2 ≤
          rvLpNorm (fun ω => a + b * X ω) μ p ^ 2 := by
      calc
        rvLpNorm (fun ω => a + sharpDiscreteRadius q lam * b * X ω) μ 2 ^ 2 =
            a ^ 2 + sharpDiscreteRadius q lam ^ 2 * lam * (1 - lam) * b ^ 2 := by
          rw [FiniteLaw.two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
            hX hxy hlam0.le hlam1 hmass_pos hmass_neg 2 (by norm_num)
            a (sharpDiscreteRadius q lam * b)]
          norm_num only [Real.rpow_two, sq_abs, Real.rpow_one]
          ring
        _ ≤ (lam * |a + b * (1 - lam)| ^ p +
            (1 - lam) * |a + b * (-lam)| ^ p) ^ (2 / p) := hscalar
        _ = rvLpNorm (fun ω => a + b * X ω) μ p ^ 2 :=
          (FiniteLaw.two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
            hX hxy hlam0.le hlam1 hmass_pos hmass_neg p
            (lt_trans zero_lt_one hp1) a b).symm
    apply (ENNReal.toReal_le_toReal houtmem.2.ne hinmem.2.ne).1
    apply (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (by decide : (2 : ℕ) ≠ 0)).1
    simpa only [rvLpNorm, ENNReal.ofReal_ofNat] using hsquare

/-- For `q > 2` and `0 < lam < 1 / 2`, if a measurable real random variable on a
probability space has mass `lam` at `1 - lam` and mass `1 - lam` at `-lam`, then
hypercontractivity from the conjugate exponent `q / (q - 1)` to exponent two at
radius `rho` forces `rho` to be at most the sharp discrete radius.

This is the random-variable form of the sharp two-point optimality statement
[OD14, Theorem 10.18 (optimality), Exercise 10.20(g)-(h), equation (10.35)].
The sample space may be any measurable space; the prescribed masses already
imply almost-everywhere two-point support and centering.

**Proof sketch.** Set `p = q / (q - 1)`, so `1 < p < 2` and its conjugate is `q`.
Hypercontractivity supplies a nonnegative radius and a finite second norm;
monotonicity of finite norms on a probability space gives finite input norms.
For arbitrary real values `u` and `v`, take
`a = lam * u + (1 - lam) * v` and `b = u - v`. The affine input `a + b * X`
has values `u` and `v` at the two atoms. Transfer the extended norm comparison
to squared real norms and evaluate both with the finite-law affine norm formula.
The resulting scalar inequality is precisely the hypothesis of the established
sharp weighted two-point radius bound. Apply that bound and identify the
conjugate exponent with `q`. -/
theorem two_point_conjugate_radius_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (q lam rho : ℝ) (hX : Measurable X) (hq : 2 < q)
    (hlam0 : 0 < lam) (hlamhalf : lam < 1 / 2)
    (hmass_pos : μ {ω | X ω = 1 - lam} = ENNReal.ofReal lam)
    (hmass_neg : μ {ω | X ω = -lam} = ENNReal.ofReal (1 - lam))
    (h : IsHypercontractive X μ (ENNReal.ofReal (q / (q - 1))) 2 rho) :
    rho ≤ sharpDiscreteRadius q lam := by
  classical
  let p : ℝ := q / (q - 1)
  have hc : Real.HolderConjugate q p := by
    simpa only [p, Real.conjExponent] using
      Real.HolderConjugate.conjExponent (show 1 < q by linarith)
  have hp2 : p < 2 := by
    dsimp only [p]
    apply (div_lt_iff₀ hc.sub_one_pos).2
    linarith
  rcases h with ⟨_, hpE, hrho, _, hX2, hcontract⟩
  change ENNReal.ofReal p ≤ 2 at hpE
  have hXp : MemLp X (ENNReal.ofReal p) μ := hX2.mono_exponent hpE
  have hlam1 : lam ≤ 1 := by linarith
  have hxy : 1 - lam ≠ -lam := by linarith
  rw [hc.symm.conjugate_eq]
  apply weighted_biased_radius_le p lam rho hc.symm.lt hp2 hlam0 hlamhalf hrho
  intro u v
  let a : ℝ := lam * u + (1 - lam) * v
  let b : ℝ := u - v
  -- Finiteness transfers the extended norm comparison to squared real norms.
  have houtmem : MemLp (fun ω => a + rho * b * X ω) 2 μ :=
    (memLp_const a).add (hX2.const_mul (rho * b))
  have hinmem : MemLp (fun ω => a + b * X ω) (ENNReal.ofReal p) μ :=
    (memLp_const a).add (hXp.const_mul b)
  have hsquare :
      rvLpNorm (fun ω => a + rho * b * X ω) μ 2 ^ 2 ≤
        rvLpNorm (fun ω => a + b * X ω) μ p ^ 2 := by
    apply (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (by decide : (2 : ℕ) ≠ 0)).2
    simpa only [rvLpNorm, ENNReal.ofReal_ofNat] using
      (ENNReal.toReal_le_toReal houtmem.2.ne hinmem.2.ne).2 (hcontract a b)
  -- The affine input has values u and v at the two atoms.
  calc
    (lam * u + (1 - lam) * v) ^ (2 : ℕ) +
        rho ^ (2 : ℕ) * lam * (1 - lam) * (u - v) ^ (2 : ℕ) =
        rvLpNorm (fun ω => a + rho * b * X ω) μ 2 ^ 2 := by
      rw [FiniteLaw.two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
        hX hxy hlam0.le hlam1 hmass_pos hmass_neg 2 (by norm_num) a (rho * b)]
      norm_num only [Real.rpow_two, sq_abs, Real.rpow_one]
      dsimp only [a, b]
      ring
    _ ≤ rvLpNorm (fun ω => a + b * X ω) μ p ^ 2 := hsquare
    _ = (lam * |u| ^ p + (1 - lam) * |v| ^ p) ^ (2 / p) := by
      rw [FiniteLaw.two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
        hX hxy hlam0.le hlam1 hmass_pos hmass_neg p hc.symm.pos a b,
        show a + b * (1 - lam) = u by dsimp only [a, b]; ring,
        show a + b * (-lam) = v by dsimp only [a, b]; ring]



/-- For `q > 2` and `0 < lam < 1 / 2`, a measurable real random variable on a probability
space with mass `lam` at `1 - lam` and mass `1 - lam` at `-lam` is hypercontractive from
exponent two to exponent `q` at the sharp discrete radius.

This is the random-variable form of the sharp forward weighted two-point inequality
[OD14, Proposition 9.19, Theorem 10.18, Exercise 10.20(b), equation (10.35)].
The sample space may be any measurable space: the prescribed masses imply
almost-everywhere two-point support and centering, so neither is an additional hypothesis.

**Proof sketch.** The two fiber masses sum to one, giving almost-everywhere support on
the two values and hence finite norms at every exponent. The sharp radius lies strictly
between zero and one. For arbitrary real affine coefficients `a` and `b`, set
`u = a + b * (1 - lam)` and `v = a + b * (-lam)`. Their weighted mean is `a`, so the
weighted noise transform has exactly the values of `a + rho * b * X`, where `rho` is
the sharp radius. Apply the established sharp forward weighted two-point inequality.
The finite-law affine norm formulas identify its left-hand side with the squared noisy
`q`-norm and its right-hand side with the squared input second norm. Nonnegativity
removes the squares, and finiteness transfers the real norm comparison to the extended
norms defining hypercontractivity. -/
theorem two_point_forward_sharp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (q lam : ℝ) (hX : Measurable X) (hq : 2 < q)
    (hlam0 : 0 < lam) (hlamhalf : lam < 1 / 2)
    (hmass_pos : μ {ω | X ω = 1 - lam} = ENNReal.ofReal lam)
    (hmass_neg : μ {ω | X ω = -lam} = ENNReal.ofReal (1 - lam)) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q)
      (sharpDiscreteRadius q lam) := by
  classical
  have hq0 : 0 < q := by linarith
  have hlam1 : lam ≤ 1 := by linarith
  have hxy : 1 - lam ≠ -lam := by linarith
  have hmass : μ {ω | X ω = 1 - lam} + μ {ω | X ω = -lam} = 1 := by
    rw [hmass_pos, hmass_neg,
      ← ENNReal.ofReal_add hlam0.le (sub_nonneg.mpr hlam1)]
    rw [show lam + (1 - lam) = 1 by ring, ENNReal.ofReal_one]
  have hfinite : HasAtomLowerBound X μ 0 := by
    refine ⟨{1 - lam, -lam}, ?_, by simp⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      FiniteLaw.ae_two_point_of_mass_sum Ω μ X (1 - lam) (-lam) hX hxy hmass
  have hr := radius_pos_lt_one q lam hq hlam0 hlamhalf
  refine ⟨by norm_num, ?_, hr.1.le, hr.2,
    hfinite.memLp hX (ENNReal.ofReal q), ?_⟩
  · simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq.le
  · intro a b
    have houtmem :
        MemLp (fun ω => a + sharpDiscreteRadius q lam * b * X ω) (ENNReal.ofReal q) μ :=
      (memLp_const a).add
        ((hfinite.memLp hX (ENNReal.ofReal q)).const_mul (sharpDiscreteRadius q lam * b))
    have hinmem : MemLp (fun ω => a + b * X ω) 2 μ :=
      (memLp_const a).add ((hfinite.memLp hX 2).const_mul b)
    have hscalar := weighted_biased_forward_le q lam
      (a + b * (1 - lam)) (a + b * (-lam)) hq hlam0 hlamhalf
    dsimp only at hscalar
    rw [show lam * (a + b * (1 - lam)) + (1 - lam) * (a + b * (-lam)) = a by ring,
      show sharpDiscreteRadius q lam * (a + b * (1 - lam)) +
        (1 - sharpDiscreteRadius q lam) * a =
        a + sharpDiscreteRadius q lam * b * (1 - lam) by ring,
      show sharpDiscreteRadius q lam * (a + b * (-lam)) +
        (1 - sharpDiscreteRadius q lam) * a =
        a + sharpDiscreteRadius q lam * b * (-lam) by ring] at hscalar
    have hsquare :
        rvLpNorm (fun ω => a + sharpDiscreteRadius q lam * b * X ω) μ q ^ 2 ≤
          rvLpNorm (fun ω => a + b * X ω) μ 2 ^ 2 := by
      rw [FiniteLaw.two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
        hX hxy hlam0.le hlam1 hmass_pos hmass_neg q hq0
        a (sharpDiscreteRadius q lam * b),
        FiniteLaw.two_point_affine_norm_sq μ X (1 - lam) (-lam) lam
        hX hxy hlam0.le hlam1 hmass_pos hmass_neg 2 (by norm_num) a b]
      norm_num only [Real.rpow_two, sq_abs, Real.rpow_one]
      exact hscalar
    apply (ENNReal.toReal_le_toReal houtmem.2.ne hinmem.2.ne).1
    apply (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (by decide : (2 : ℕ) ≠ 0)).1
    simpa only [rvLpNorm, ENNReal.ofReal_ofNat] using hsquare


end BooleanAnalysis.Hypercontractivity.SharpDiscrete
