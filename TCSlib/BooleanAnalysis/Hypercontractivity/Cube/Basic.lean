/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shared probability and norm definitions on the uniform cube

## Main definitions

* `cubeIndicator`, `cubeProbability`: the standard indicator and its uniform expectation.
* `cubeVariance`: the second centered moment.
* `cubeLpNorm`: the real-exponent power-mean expression shared by forward and reverse
  hypercontractivity. The reverse mean retains its separate conventions at nonpositive
  exponents.

## Main results

* `fourierCoeff_derivative`: coordinate derivatives remove their Fourier coordinate.
* `cube_moment_interpolation`: weighted Hölder interpolates two absolute moments.
* `cubeLpNorm_rpow`: raising a positive-exponent power mean recovers its moment.
* `cubeProbability_le_cubeLpNorm_div_rpow`: Markov bounds cube tails through their moments.
* `has_degree_at_most_sub_const`: subtracting a constant preserves a Fourier degree bound.
* `l2Norm_noiseOp_le`: Fourier rescaling by `ρ ≥ 1` increases the second norm of a
  degree-`k` function by at most `ρ ^ k`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §§9.1–9.2 and §9.5, Theorems 9.7, 9.21–9.22, and 9.24.
-/

open scoped Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/-- A coordinate derivative has zero Fourier coefficients on sets containing that
coordinate; on any other set, its coefficient is the original function's coefficient
on the set with that coordinate inserted.
[OD14, §2.2, Fourier expansion of discrete derivatives; Cor. 9.25 (proof)]

**Proof sketch.** Pair each cube point with its coordinate flip, which preserves
uniform expectation. The derivative is unchanged by that flip. If the coordinate
belongs to the character's set, the character changes sign, so the paired
coefficient integrand averages to zero. Otherwise, averaging the original function
times the character with that coordinate inserted gives the derivative times the
original character. Taking expectations identifies the coefficients. -/
lemma fourierCoeff_derivative {n : ℕ} (f : BooleanFunc n)
    (i : Fin n) (S : Finset (Fin n)) :
    fourierCoeff (derivative i f) S =
      if i ∈ S then 0 else fourierCoeff f (insert i S) := (by
  classical
  have hbij : Function.Bijective (fun x : BoolCube n => flipBit x i) :=
    (show Function.Involutive (fun x : BoolCube n => flipBit x i) from
      fun x => flipBit_flipBit x i).bijective
  have hdf (x : BoolCube n) :
      derivative i f (flipBit x i) = derivative i f x := by
    simp only [derivative, flipBit, Function.update_idem]
  change expect (fun x => derivative i f x * chiS S x) =
    if i ∈ S then 0 else expect (fun x => f x * chiS (insert i S) x)
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hflip := Fintype.expect_bijective
      (fun x : BoolCube n => flipBit x i) hbij
      (fun x => derivative i f (flipBit x i) * chiS S (flipBit x i))
      (fun x => derivative i f x * chiS S x) (fun _ => rfl)
    simp only [← expect_eq_fintypeExpect, hdf, chiS_flipBit_eq,
      if_pos hi, mul_neg, ThresholdFunctions.expect_neg] at hflip
    linarith
  · rw [if_neg hi]
    have hpair : (fun x => derivative i f x * chiS S x) =
        (fun x => (1 / 2 : ℝ) * (f x * chiS (insert i S) x +
          f (flipBit x i) * chiS (insert i S) (flipBit x i))) := by
      funext x
      rw [chiS_flipBit_eq, if_pos (Finset.mem_insert_self i S)]
      have hins : chiS (insert i S) x = boolToSign (x i) * chiS S x := by
        simp only [chiS, Finset.prod_insert hi]
      rw [hins]
      cases hx : x i <;>
        simp only [derivative, flipBit, hx, Bool.not_false, Bool.not_true,
          boolToSign_false, boolToSign_true] <;>
        have hself := Function.update_eq_self i x <;>
        simp only [hx] at hself <;>
        rw [hself] <;> ring
    have hflip := Fintype.expect_bijective
      (fun x : BoolCube n => flipBit x i) hbij
      (fun x => f (flipBit x i) * chiS (insert i S) (flipBit x i))
      (fun x => f x * chiS (insert i S) x) (fun _ => rfl)
    simp only [← expect_eq_fintypeExpect] at hflip
    rw [hpair, ThresholdFunctions.expect_const_mul,
      ThresholdFunctions.expect_add, hflip]
    ring
)


/-- Subtracting any real constant from a cube function of Fourier degree at most `k`
preserves that degree bound. [OD14, Thms. 9.7 and 9.24 (proofs)]

**Proof sketch.** Subtracting a constant changes only the empty Fourier coefficient.
Character orthogonality leaves all nonempty coefficients unchanged, so coefficients
above level `k` still vanish. -/
lemma has_degree_at_most_sub_const {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (c : ℝ) :
    has_degree_at_most (fun x => f x - c) k := (by
  classical
  intro S hS
  by_cases hSempty : S = ∅
  · subst S
    simp
  · have hmean : expect (chiS S) = 0 := by
      simpa only [innerProduct, chiS_empty, one_mul,
        if_neg (Ne.symm hSempty)] using
        (fourier_coeff_chi (∅ : Finset (Fin n)) S)
    apply hdeg S
    simpa only [fourierCoeff, innerProduct, sub_mul,
      ThresholdFunctions.expect_sub, ThresholdFunctions.expect_const_mul,
      hmean, mul_zero, sub_zero] using hS
)

/-- The indicator of a cube event is one on the event and zero elsewhere.
[OD14, §9.1] This reuses Mathlib's set indicator. -/
noncomputable def cubeIndicator {n : ℕ} (A : BoolCube n → Prop) : BooleanFunc n :=
  Set.indicator {x | A x} (fun _ => 1)

/-- Uniform event probability is the expectation of its indicator. [OD14, §9.1] -/
noncomputable def cubeProbability {n : ℕ} (A : BoolCube n → Prop) : ℝ :=
  expect (cubeIndicator A)

/-- Variance on the uniform cube is the second centered moment. [OD14, Thm. 9.7] -/
noncomputable def cubeVariance {n : ℕ} (f : BooleanFunc n) : ℝ :=
  expect (fun x => (f x - expect f) ^ 2)

/-- The real-exponent `Lᵖ` expression on the uniform cube; applications use `p ≥ 1`.
[OD14, §9.5, Thms. 9.21–9.22] The raw formula is retained at every real exponent so the
reverse-hypercontractivity mean can reuse it without changing its boundary conventions. -/
noncomputable abbrev cubeLpNorm {n : ℕ} (p : ℝ) (f : BooleanFunc n) : ℝ :=
  (expect (fun x => |f x| ^ p)) ^ (1 / p)

/-- For a positive exponent `q`, raising the cube `q`-moment mean to `q`
recovers the expected `q`th power of the absolute value.
[OD14, §9.5, norm definition]

**Proof sketch.** The moment is nonnegative. Compose its real powers
`1 / q` and `q`, whose product is one. -/
lemma cubeLpNorm_rpow {n : ℕ} (f : BooleanFunc n) (q : ℝ) (hq : 0 < q) :
    (cubeLpNorm q f) ^ q = expect (fun x => |f x| ^ q) := (by
  have hmoment : 0 ≤ expect (fun x => |f x| ^ q) :=
    ThresholdFunctions.expect_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  unfold cubeLpNorm
  rw [← Real.rpow_mul hmoment, one_div_mul_cancel hq.ne', Real.rpow_one]
)

/-- For any positive exponent `q` and threshold `c`, the probability that
`|f| ≥ c` is at most `(cubeLpNorm q f / c) ^ q`.
[OD14, Thm. 9.23 (proof), Markov inequality step]

**Proof sketch.** Pointwise, `c ^ q` times the event indicator is at most
`|f| ^ q`. Take expectations and divide by the positive number `c ^ q`.
The defining power mean, raised to `q`, equals the expected `q`th power,
so the result takes the stated norm form. -/
lemma cubeProbability_le_cubeLpNorm_div_rpow {n : ℕ} (f : BooleanFunc n)
    (q c : ℝ) (hq : 0 < q) (hc : 0 < c) :
    cubeProbability (fun x => c ≤ |f x|) ≤
      (cubeLpNorm q f / c) ^ q := (by
  have hpt (x : BoolCube n) :
      c ^ q * cubeIndicator (fun x => c ≤ |f x|) x ≤ |f x| ^ q := by
    by_cases hx : c ≤ |f x|
    · simpa [cubeIndicator, hx] using
        Real.rpow_le_rpow hc.le hx hq.le
    · simpa [cubeIndicator, hx] using
        Real.rpow_nonneg (abs_nonneg (f x)) q
  have hm := ThresholdFunctions.expect_mono hpt
  rw [ThresholdFunctions.expect_const_mul] at hm
  change c ^ q * cubeProbability (fun x => c ≤ |f x|) ≤
    expect (fun x => |f x| ^ q) at hm
  have hnorm : 0 ≤ cubeLpNorm q f :=
    Real.rpow_nonneg
      (ThresholdFunctions.expect_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  rw [Real.div_rpow hnorm hc.le q, cubeLpNorm_rpow f q hq]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hc q)).mpr
    (by simpa only [mul_comm] using hm)
)

/-- For `0 < p < 2 < q`, the second moment of a cube function is bounded by
the geometric interpolation of its absolute `p`th and `q`th moments.
[OD14, Thm. 9.22 (proof)]

**Proof sketch.** Apply weighted Hölder with weight `|f| ^ p`, observable
`|f| ^ (2 - p)`, and exponent `(q - p) / (2 - p)`.
The weighted first moment is the second moment of `f`, and the weighted
higher moment is its absolute `q`th moment. Simplify the interpolation exponents. -/
lemma cube_moment_interpolation {n : ℕ} (f : BooleanFunc n) (p q : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (hq2 : 2 < q) :
    innerProduct f f ≤
      (expect (fun x => |f x| ^ p)) ^ ((q - 2) / (q - p)) *
      (expect (fun x => |f x| ^ q)) ^ ((2 - p) / (q - p)) := (by
  let r : ℝ := (q - p) / (2 - p)
  let w : BoolCube n → ℝ := fun x => |f x| ^ p
  let v : BoolCube n → ℝ := fun x => |f x| ^ (2 - p)
  have hr : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ (sub_pos.mpr hp2)).mpr
    linarith
  have hrinv : r⁻¹ = (2 - p) / (q - p) := by simp [r]
  have hexp : 1 - r⁻¹ = (q - 2) / (q - p) := by
    rw [hrinv]
    field_simp [show q - p ≠ 0 by linarith]
    ring
  have hm : (2 - p) * r = q - p := by
    dsimp [r]
    field_simp [(sub_pos.mpr hp2).ne']
  have hholder := Real.compact_inner_le_weight_mul_Lp_of_nonneg
    (s := Finset.univ) (p := r) (w := w) (f := v) hr
    (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  rw [← expect_eq_fintypeExpect, ← expect_eq_fintypeExpect,
    ← expect_eq_fintypeExpect] at hholder
  have hprod1 (x : BoolCube n) : w x * v x = f x * f x := by
    dsimp [w, v]
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) hp.le (sub_pos.mpr hp2).le]
    have he : p + (2 - p) = (2 : ℝ) := by ring
    rw [he, Real.rpow_two, pow_two, abs_mul_abs_self]
  have hprod2 (x : BoolCube n) : w x * v x ^ r = |f x| ^ q := by
    dsimp [w, v]
    rw [← Real.rpow_mul (abs_nonneg _), hm,
      ← Real.rpow_add_of_nonneg (abs_nonneg _) hp.le (by linarith : 0 ≤ q - p)]
    congr 1
    ring
  simp_rw [hprod1, hprod2] at hholder
  rw [hexp, hrinv] at hholder
  simpa only [innerProduct, w] using hholder
)

/-- If `A ≥ 0`, `M > 0`, `u > 0`, and `u + v = 2`, then
`M² ≤ A ^ u (exp(c) M) ^ v` implies `M ≤ exp(c v / u) A`.
[OD14, Thm. 9.22 (proof)] This abstracts the scalar cancellation step
for reuse in norm interpolation, allowing arbitrary real `v` and `c`.

**Proof sketch.** Positivity of `M` forces `A` to be positive.
Take logarithms of the assumed bound, expand the products and powers,
and use `u + v = 2` to cancel the repeated logarithm of `M`.
Divide by positive `u` and exponentiate. -/
lemma lp_interpolation_cancel (A M u v c : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hu : 0 < u)
    (huv : u + v = 2)
    (hbound : M ^ 2 ≤ A ^ u * (Real.exp c * M) ^ v) :
    M ≤ Real.exp (c * v / u) * A := (by
  have hApos : 0 < A := by
    rcases hA.eq_or_lt with hzero | hpos
    · rw [← hzero, Real.zero_rpow hu.ne', zero_mul] at hbound
      exact False.elim ((not_le_of_gt (sq_pos_of_pos hM)) hbound)
    · exact hpos
  have hlog := Real.log_le_log (sq_pos_of_pos hM) hbound
  rw [Real.log_pow,
    Real.log_mul (Real.rpow_pos_of_pos hApos u).ne'
      (Real.rpow_pos_of_pos (mul_pos (Real.exp_pos c) hM) v).ne',
    Real.log_rpow hApos, Real.log_rpow (mul_pos (Real.exp_pos c) hM),
    Real.log_mul (Real.exp_pos c).ne' hM.ne', Real.log_exp] at hlog
  norm_num at hlog
  rw [← huv] at hlog
  have hcancel : Real.log M - Real.log A ≤ c * v / u := by
    apply (le_div_iff₀ hu).mpr
    nlinarith only [hlog]
  calc
    M = Real.exp (Real.log M) := (Real.exp_log hM).symm
    _ ≤ Real.exp (c * v / u + Real.log A) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (c * v / u) * A := by
      rw [Real.exp_add, Real.exp_log hApos]
)

/-- For `0 < p < 2 < q`, an upper bound `‖f‖q ≤ exp(c) ‖f‖₂` implies
`‖f‖₂ ≤ exp(c q (2-p)/(p(q-2))) ‖f‖p`.
[OD14, Thm. 9.22 (proof)] This abstracts the moment interpolation and
cancellation argument, allowing any real exponential coefficient `c`.

**Proof sketch.** Interpolate the second moment between the absolute
`p`th and `q`th moments, then rewrite the moments as powers of their means.
Apply the assumed upper bound to the resulting positive power of the
`q`-moment mean. The powers of the two means sum to two, so scalar
cancellation gives the result. If the second norm is zero, use nonnegativity. -/
lemma cube_norm_interpolation_bound {n : ℕ} (f : BooleanFunc n) (p q c : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (hq2 : 2 < q)
    (hbound : cubeLpNorm q f ≤ Real.exp c * l2Norm f) :
    l2Norm f ≤
      Real.exp (c * q * (2 - p) / (p * (q - 2))) * cubeLpNorm p f :=
  (by
  have hpNorm : 0 ≤ cubeLpNorm p f :=
    Real.rpow_nonneg
      (ThresholdFunctions.expect_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  have hqNorm : 0 ≤ cubeLpNorm q f :=
    Real.rpow_nonneg
      (ThresholdFunctions.expect_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _
  by_cases hzero : l2Norm f = 0
  · rw [hzero]
    exact mul_nonneg (Real.exp_pos _).le hpNorm
  have hM : 0 < l2Norm f :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzero)
  have hq : 0 < q := by linarith
  have hqp : 0 < q - p := by linarith
  let u : ℝ := p * ((q - 2) / (q - p))
  let v : ℝ := q * ((2 - p) / (q - p))
  have hu : 0 < u := mul_pos hp (div_pos (sub_pos.mpr hq2) hqp)
  have hv : 0 ≤ v := mul_nonneg hq.le (div_nonneg (sub_pos.mpr hp2).le hqp.le)
  have huv : u + v = 2 := by
    dsimp [u, v]
    field_simp [hqp.ne']
    ring
  have hi := cube_moment_interpolation f p q hp hp2 hq2
  rw [← cubeLpNorm_rpow f p hp, ← cubeLpNorm_rpow f q hq,
    ← Real.rpow_mul hpNorm, ← Real.rpow_mul hqNorm] at hi
  change innerProduct f f ≤ cubeLpNorm p f ^ u * cubeLpNorm q f ^ v at hi
  have hmoment : l2Norm f ^ 2 ≤
      cubeLpNorm p f ^ u * (Real.exp c * l2Norm f) ^ v := by
    calc
      _ = innerProduct f f := by
        unfold l2Norm
        exact Real.sq_sqrt (innerProduct_self_nonneg f)
      _ ≤ cubeLpNorm p f ^ u * cubeLpNorm q f ^ v := hi
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hqNorm hbound hv) (Real.rpow_nonneg hpNorm u)
  have hc := lp_interpolation_cancel (cubeLpNorm p f) (l2Norm f) u v c
    hpNorm hM hu huv hmoment
  have hexp : c * v / u = c * q * (2 - p) / (p * (q - 2)) := by
    dsimp [u, v]
    field_simp [hp.ne', (sub_pos.mpr hq2).ne', hqp.ne']
  simpa only [hexp] using hc
)

/-- A mean-zero cube function has squared expected absolute value at most four times
its squared second norm times the probability that it is strictly positive.
[OD14, Thm. 9.24 (proof)]

**Proof sketch.** The positive part has expectation half the expected absolute value,
because the function has mean zero. Cauchy–Schwarz applied to the function and the
indicator of its positive event bounds the square of that expectation by the squared
second norm times the event probability. -/
lemma centered_abs_expect_sq_le {n : ℕ} (g : BooleanFunc n)
    (hmean : expect g = 0) :
    (expect (fun x => |g x|)) ^ 2 ≤
      4 * innerProduct g g * cubeProbability (fun x => 0 < g x) :=
  (by
  classical
  let I := cubeIndicator (fun x => 0 < g x)
  have habs : expect (fun x => |g x|) = 2 * expect (fun x => g x * I x) := by
    calc
      _ = expect (fun x => 2 * (g x * I x) - g x) := by
        congr 1
        funext x
        by_cases hx : 0 < g x
        · simp [I, cubeIndicator, hx, abs_of_pos hx]
          ring
        · simp [I, cubeIndicator, hx, abs_of_nonpos (le_of_not_gt hx)]
      _ = _ := by
        rw [ThresholdFunctions.expect_sub, ThresholdFunctions.expect_const_mul,
          hmean, sub_zero]
  have hsq : (expect (fun x => g x * I x)) ^ 2 ≤ innerProduct g g * expect I := by
    have hI : (fun x => I x ^ 2) = I := by
      funext x
      by_cases hx : 0 < g x <;> simp [I, cubeIndicator, hx]
    simpa only [← expect_eq_fintypeExpect, hI, innerProduct, ← pow_two] using
      (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ g I)
  rw [habs]
  change (2 * expect (fun x => g x * I x)) ^ 2 ≤ 4 * innerProduct g g * expect I
  nlinarith [hsq]
)

/-- If an indicator `f` has positive mean `α` and `E[exp(t g)] ≤ exp(b)`, then
`t E[f g] ≤ α (b - log α)`. [OD14, §9.5 and Ex. 9.18(b)]
This states the conditional exponential-moment step for an arbitrary real cube function.

**Proof sketch.** Apply `1 + u ≤ exp u` with `u = t g - b + log α`.
At points where the indicator is one this bounds `t f g`; where it is zero
the same bound follows from positivity of the exponential. Take expectations
and use the exponential-moment hypothesis to cancel the remaining exponential factor. -/
lemma indicator_innerProduct_le_of_mgf {n : ℕ} (f g : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) (t b : ℝ)
    (hmgf : expect (fun x => Real.exp (t * g x)) ≤ Real.exp b) :
    t * innerProduct f g ≤ expect f * (b - Real.log (expect f)) :=
  (by
  have hpt (x : BoolCube n) :
      t * (f x * g x) ≤
        (b - Real.log (expect f) - 1) * f x +
          expect f * Real.exp (-b) * Real.exp (t * g x) := by
    have hex : expect f * Real.exp (-b) * Real.exp (t * g x) =
        Real.exp (t * g x - b + Real.log (expect f)) := by
      rw [← Real.exp_log hα, ← Real.exp_add, ← Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring
    rcases hf x with hx | hx
    · rw [hx]
      simp only [mul_zero, zero_mul, zero_add]
      positivity
    · rw [hx, hex]
      linarith [Real.add_one_le_exp (t * g x - b + Real.log (expect f))]
  calc
    t * innerProduct f g = expect (fun x => t * (f x * g x)) :=
      (ThresholdFunctions.expect_const_mul t _).symm
    _ ≤ expect (fun x => (b - Real.log (expect f) - 1) * f x +
          expect f * Real.exp (-b) * Real.exp (t * g x)) :=
      ThresholdFunctions.expect_mono hpt
    _ = (b - Real.log (expect f) - 1) * expect f +
        expect f * Real.exp (-b) * expect (fun x => Real.exp (t * g x)) := by
      rw [ThresholdFunctions.expect_add, ThresholdFunctions.expect_const_mul,
        ThresholdFunctions.expect_const_mul]
    _ ≤ (b - Real.log (expect f) - 1) * expect f +
        expect f * Real.exp (-b) * Real.exp b :=
      add_le_add_left (mul_le_mul_of_nonneg_left hmgf (by positivity)) _
    _ = expect f * (b - Real.log (expect f)) := by
      rw [mul_assoc (expect f), ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      ring
)

/-- For a cube function of degree at most `k`, Fourier rescaling by `ρ ≥ 1` increases
its second norm by at most `ρ ^ k`. [OD14, Thm. 9.21 (proof)]
Here the noise operator's Fourier formula is used beyond its probabilistic parameter range.

**Proof sketch.** Parseval expresses the squared rescaled norm as a sum of squared
Fourier coefficients multiplied by `ρ ^ (2 * |S|)`. Nonzero coefficients have
`|S| ≤ k`, so each multiplier is at most `ρ ^ (2 * k)`. Sum these inequalities
and take square roots. -/
lemma l2Norm_noiseOp_le {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    l2Norm (noiseOp ρ f) ≤ ρ ^ k * l2Norm f := (by
  classical
  have hsq : innerProduct (noiseOp ρ f) (noiseOp ρ f) ≤
      (ρ ^ k) ^ 2 * innerProduct f f := by
    rw [parseval, parseval, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    rw [noiseOp_fourier, mul_pow]
    by_cases hS : fourierCoeff f S = 0
    · simp [hS]
    · apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ hρ (Nat.mul_le_mul_right 2 (hdeg S hS))
  unfold l2Norm
  calc
    _ ≤ Real.sqrt ((ρ ^ k) ^ 2 * innerProduct f f) := Real.sqrt_le_sqrt hsq
    _ = ρ ^ k * Real.sqrt (innerProduct f f) := by
      rw [Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (pow_nonneg (zero_le_one.trans hρ) _)]
)

end BooleanAnalysis.Hypercontractivity
