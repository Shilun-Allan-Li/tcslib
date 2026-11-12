/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.LowDegree

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stable influence and level inequalities

Stable influence and level estimates, with their indicator bounds kept file-private.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `stableInfluence_le`.
* `stableInfluence_one_third`.
* `level_k_inequality`.
* `level_one_inequality`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §9.5 and Exercise 9.18.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity


/-- An indicator-valued cube function of mean `α` has noise stability at most
`α ^ (2 / (1 + ρ))` for `0 < ρ ≤ 1`.
[OD14, §9.5, Small-Set Expansion Theorem, p. 264]

**Proof sketch.** Take the finite set of cube points where the function equals one.
Its indicator equals the function, and its volume equals the function's mean.
Substitute these identities into the existing small-set expansion theorem. -/
private lemma indicator_stability_le {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    innerProduct f (noiseOp ρ f) ≤
      (expect f) ^ (2 / (1 + ρ)) := (by
  let A : Finset (BoolCube n) := Finset.univ.filter (fun x => f x = 1)
  have hA : setIndicator A = f := by
    funext x
    rcases hf x with hx | hx <;>
      simp [setIndicator, cubeIndicator, A, hx]
  simpa only [volume, hA] using
    small_set_expansion ρ hρ0 hρ1 A
)

/-- An indicator of positive mean `α` has squared correlation at most
`2 α² log(1/α)` with any unit-variance Rademacher linear form.
[OD14, §9.5 and Ex. 9.18(b)]

**Proof sketch.** The Rademacher exponential-moment bound and the conditional moment
estimate bound the correlation for every real parameter. Choose the parameter to
be the correlation divided by `α`, multiply by `2 α`, and rearrange. -/
private lemma indicator_linear_form_sq_le {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f)
    (a : Fin n → ℝ) (hnorm : ∑ i : Fin n, a i ^ 2 = 1) :
    innerProduct f (fun x => ∑ i : Fin n, a i * boolToSign (x i)) ^ 2 ≤
      2 * expect f ^ 2 * Real.log (1 / expect f) :=
  (by
  let L : BooleanFunc n := fun x => ∑ i : Fin n, a i * boolToSign (x i)
  let c : ℝ := innerProduct f L
  have h : (c / expect f) * c ≤
      expect f * ((c / expect f) ^ 2 / 2 - Real.log (expect f)) :=
    indicator_innerProduct_le_of_mgf f L hf hα (c / expect f)
      ((c / expect f) ^ 2 / 2) (ThresholdFunctions.rademacher_mgf_le a hnorm _)
  have hzero : c ^ 2 + 2 * expect f ^ 2 * Real.log (expect f) ≤ 0 := by
    calc
      _ = 2 * expect f * ((c / expect f) * c -
          expect f * ((c / expect f) ^ 2 / 2 - Real.log (expect f))) := by
        field_simp [hα.ne']
        ring
      _ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h)
  change c ^ 2 ≤ 2 * expect f ^ 2 * Real.log (1 / expect f)
  rw [one_div, Real.log_inv]
  linarith
)

/-- For `ρ ≥ 0`, the noisy influence of a coordinate equals the squared second norm
of its derivative after noise at parameter `√ρ`.
[OD14, §2.2 and Cor. 9.25 (proof)]
This Fourier identity holds for arbitrary real-valued functions, without an upper
bound on `ρ`.

**Proof sketch.** Expand the derivative's noise stability in Fourier coefficients.
Its coefficients vanish on sets containing the coordinate; adjoining that coordinate
to every remaining set gives the noisy-influence sum, with the degree reduced by one.
Self-adjointness and composition of noise operators identify this stability with
the squared second norm after noise at `√ρ`. The argument retains the degree-zero
term when `ρ = 0`. -/
private lemma noisyInfluence_eq_sq_norm_derivative {n : ℕ} (f : BooleanFunc n)
    (i : Fin n) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    KKL.noisyInfluence ρ i f =
      l2Norm (noiseOp (Real.sqrt ρ) (derivative i f)) ^ 2 :=
  (by
  classical
  rw [l2Norm, Real.sq_sqrt (innerProduct_self_nonneg _),
    noiseOp_self_adjoint, noiseOp_compose,
    ← pow_two, Real.sq_sqrt hρ, stability_formula, KKL.noisyInfluence]
  have hcoeff :
      (∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff (derivative i f) S ^ 2) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S),
          ρ ^ S.card * fourierCoeff f (insert i S) ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : i ∈ S <;> simp [fourierCoeff_derivative, h]
  rw [hcoeff, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun S _ => S.erase i) (fun S _ => insert i S)
    ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp
  · intro S hS
    simp
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro S hS
    exact Finset.erase_insert (Finset.mem_filter.mp hS).2
  · intro S hS
    have hiS := (Finset.mem_filter.mp hS).2
    simp only [Finset.card_erase_of_mem hiS, Finset.insert_erase hiS]
)


/-- Every positive absolute moment of a coordinate derivative of a `±1`-valued
cube function equals that coordinate's ordinary influence.
[OD14, Cor. 9.25 (proof)] The identity is stated for every positive exponent,
since the derivative's absolute value is always zero or one.

**Proof sketch.** The derivative's square equals its absolute value, forcing that
absolute value to be zero or one. Positive powers preserve these values.
Therefore the absolute moment equals the expected derivative square, which is
the ordinary influence. -/
private lemma derivative_abs_moment_eq_influence {n : ℕ} (f : BooleanFunc n)
    (hf : isPmOne f) (i : Fin n) (p : ℝ) (hp : 0 < p) :
    expect (fun x => |derivative i f x| ^ p) = influence i f :=
  (by
  rw [ThresholdFunctions.influence_eq_expect_derivative_sq]
  congr 1
  funext x
  have hs := ThresholdFunctions.derivative_sq_eq_abs_of_pmOne hf i x
  rw [hs]
  have habs : |derivative i f x| * (|derivative i f x| - 1) = 0 := by
    nlinarith [sq_abs (derivative i f x)]
  rcases mul_eq_zero.mp habs with hz | ho
  · rw [hz, Real.zero_rpow hp.ne']
  · have hone : |derivative i f x| = 1 := sub_eq_zero.mp ho
    rw [hone, Real.one_rpow]
)


/-- Stable influence at `ρ ∈ [0,1]` is at most ordinary influence to the power
`2/(1+ρ)` for Boolean functions. [OD14, Cor. 9.25]

**Proof sketch.** Apply `(1+ρ,2)`-hypercontractivity to the coordinate derivative and
evaluate its norm using its `{-1,0,1}`-valued range. -/
theorem stableInfluence_le {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (i : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc 0 1) :
    KKL.noisyInfluence ρ i f ≤ (influence i f) ^ (2 / (1 + ρ)) := (by
  rcases hρ with ⟨hρ0, hρ1⟩
  have hp : 0 < 1 + ρ := by linarith
  have hc := general_one_function_hypercontractivity
    (1 + ρ) 2 (by linarith) (by linarith) (by norm_num)
    (Real.sqrt ρ) (Real.sqrt_nonneg _)
    (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hρ1)
    (by norm_num) (derivative i f)
  rw [derivative_abs_moment_eq_influence f hf i (1 + ρ) hp] at hc
  have hcontract :
      l2Norm (noiseOp (Real.sqrt ρ) (derivative i f)) ≤
        (influence i f) ^ (1 / (1 + ρ)) := by
    simpa only [l2Norm, innerProduct, Real.sqrt_eq_rpow, Real.rpow_two,
      pow_two, abs_mul_abs_self] using hc
  have hI : 0 ≤ influence i f := by
    rw [ThresholdFunctions.influence_eq_expect_derivative_sq]
    exact ThresholdFunctions.expect_nonneg (fun x => sq_nonneg _)
  rw [noisyInfluence_eq_sq_norm_derivative f i ρ hρ0]
  convert pow_le_pow_left₀ (Real.sqrt_nonneg _) hcontract 2 using 1
  rw [← Real.rpow_mul_natCast hI]
  congr 1
  norm_num; ring
)

/-- The one-third-stable influence of a Boolean function is at most its ordinary influence
to the power `3/2`. [OD14, Cor. 9.12]

**Proof sketch.** Specialize the general stable-influence bound to `ρ=1/3` and
simplify the exponent `2/(1+ρ)` to `3/2`. -/
theorem stableInfluence_one_third {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f) (i : Fin n) :
    KKL.noisyInfluence (1 / 3) i f ≤ (influence i f) ^ (3 / 2 : ℝ) := by
  convert stableInfluence_le f hf i (1 / 3) (by norm_num) using 1 <;> norm_num

/-- For `0 ≤ ρ ≤ 1`, multiplying the Fourier weight through level `k` by `ρ ^ k`
gives a lower bound on the noise stability.
[OD14, §9.5, Level-k Inequalities proof]

**Proof sketch.** Expand noise stability as the weighted sum of squared Fourier
coefficients. On levels at most `k`, the weight `ρ ^ |S|` is at least `ρ ^ k`.
Above `k`, the truncated weight is zero and the stability summand is nonnegative.
Multiply by the squared coefficients and sum. -/
private lemma weighted_fourierWeightUpTo_le_stability {n k : ℕ}
    (f : BooleanFunc n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ k * ThresholdFunctions.fourierWeightUpTo k f ≤
      innerProduct f (noiseOp ρ f) := (by
  rw [ThresholdFunctions.fourierWeightUpTo, stability_formula, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S.card ≤ k
  · simp only [if_pos hS]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hρ0 hρ1 hS) (sq_nonneg _)
  · simp only [if_neg hS, mul_zero]
    positivity
)

/-- For `0 < α ≤ 1` and `ρ ≥ 0`, the power `α ^ (2 / (1 + ρ))` is at most
`α² exp(2 ρ log(1/α))`. [OD14, §9.5, Level-k Inequalities proof]

**Proof sketch.** Since `2 (1 - ρ) ≤ 2 / (1 + ρ)` and `α ≤ 1`, decreasing
the exponent to `2 (1 - ρ)` increases the power. Express that power using
the exponential and logarithm, then separate the square of `α`. -/
private lemma indicator_rpow_le_sq_mul_exp (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 ≤ ρ) :
    α ^ (2 / (1 + ρ)) ≤
      α ^ 2 * Real.exp (2 * ρ * Real.log (1 / α)) := (by
  have hden : 0 < 1 + ρ := by positivity
  have hcomp : 2 * (1 - ρ) ≤ 2 / (1 + ρ) :=
    (le_div_iff₀ hden).mpr (by nlinarith [sq_nonneg ρ])
  calc
    α ^ (2 / (1 + ρ)) ≤ α ^ (2 * (1 - ρ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 hcomp
    _ = α ^ 2 * Real.exp (2 * ρ * Real.log (1 / α)) := by
      rw [Real.rpow_def_of_pos hα, ← Real.rpow_natCast α 2,
        Real.rpow_def_of_pos hα, one_div, Real.log_inv, ← Real.exp_add]
      congr 1
      ring
)

/-- If `0 < α ≤ 1`, `1 ≤ k ≤ 2 log(1/α)`, and
`ρ ^ k W ≤ α ^ (2 / (1 + ρ))` for every `0 < ρ ≤ 1`, then
`W ≤ ((2e/k) log(1/α)) ^ k α²`.
[OD14, §9.5, Level-k Inequalities proof]

**Proof sketch.** Write `L = log(1/α)` and choose `ρ = k / (2L)`, which
lies in `(0, 1]`. The scalar exponent bound gives `ρ ^ k W ≤ α² exp(k)`.
The product of `ρ ^ k` and `((2e/k)L) ^ k` equals `exp(k)`.
Cancel the positive factor `ρ ^ k`. -/
private lemma level_k_optimization {k : ℕ} (α W : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hk : 0 < k)
    (hkα : (k : ℝ) ≤ 2 * Real.log (1 / α))
    (hW : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ρ ^ k * W ≤ α ^ (2 / (1 + ρ))) :
    W ≤ ((2 * Real.exp 1 / (k : ℝ)) * Real.log (1 / α)) ^ k * α ^ 2 :=
  (by
  let L : ℝ := Real.log (1 / α)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hL : 0 < L := by
    dsimp [L]
    linarith
  let ρ : ℝ := (k : ℝ) / (2 * L)
  have hρ0 : 0 < ρ := div_pos hkR (by positivity)
  have hρ1 : ρ ≤ 1 := (div_le_one (by positivity)).mpr hkα
  have hexp : 2 * ρ * L = (k : ℝ) := by
    calc
      _ = ρ * (2 * L) := by ring
      _ = (k : ℝ) := div_mul_cancel₀ _ (by positivity)
  have hbound : ρ ^ k * W ≤ α ^ 2 * Real.exp (k : ℝ) := by
    calc
      _ ≤ α ^ (2 / (1 + ρ)) := hW ρ hρ0 hρ1
      _ ≤ α ^ 2 * Real.exp (2 * ρ * L) :=
        indicator_rpow_le_sq_mul_exp α ρ hα hα1 hρ0.le
      _ = _ := by rw [hexp]
  have hprod : ρ * ((2 * Real.exp 1 / (k : ℝ)) * L) = Real.exp 1 := by
    dsimp [ρ]
    field_simp [hL.ne', hkR.ne']
  apply le_of_mul_le_mul_left ?_ (pow_pos hρ0 k)
  calc
    ρ ^ k * W ≤ α ^ 2 * Real.exp (k : ℝ) := hbound
    _ = ρ ^ k * (((2 * Real.exp 1 / (k : ℝ)) * L) ^ k * α ^ 2) := by
      rw [← mul_assoc, ← mul_pow, hprod, ← Real.exp_nat_mul, mul_one]
      ring
)

/-- For an indicator of positive mean `α` and `1 ≤ k ≤ 2 ln(1/α)`, its Fourier weight
through level `k` is at most `((2e/k) ln(1/α))^k α²`.
[OD14, §9.5, Level-k Inequalities] The zero indicator is excluded from the logarithmic formula.

**Proof sketch.** Small-set expansion bounds the weight by `ρ^(-k) α^(2/(1+ρ))`.
Weaken the exponent to `2(1-ρ)` and set `ρ = k/(2 ln(1/α))`. -/
theorem level_k_inequality {n k : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) (hk : 0 < k)
    (hkα : (k : ℝ) ≤ 2 * Real.log (1 / expect f)) :
    ThresholdFunctions.fourierWeightUpTo k f ≤
      ((2 * Real.exp 1 / (k : ℝ)) * Real.log (1 / expect f)) ^ k * (expect f) ^ 2 := (by
  have hα1 : expect f ≤ 1 := by
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) :=
        ThresholdFunctions.expect_mono fun x => by
          rcases hf x with hx | hx <;> simp [hx]
      _ = 1 := ThresholdFunctions.expect_const 1
  apply level_k_optimization (expect f)
    (ThresholdFunctions.fourierWeightUpTo k f) hα hα1 hk hkα
  intro ρ hρ0 hρ1
  exact (weighted_fourierWeightUpTo_le_stability f ρ hρ0.le hρ1).trans
    (indicator_stability_le f hf ρ hρ0 hρ1)
)


/-- An indicator of positive mean `α` has level-one Fourier weight at most
`2α² ln(1/α)`. [OD14, §9.5 and Ex. 9.18(b)]

**Proof sketch.** Use the subgaussian exponential moment bound for the normalized
degree-one part, and optimize its exponential parameter on the indicator's support. -/
theorem level_one_inequality {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) :
    weightLevel 1 f ≤ 2 * (expect f) ^ 2 * Real.log (1 / expect f) := (by
  have hα1 : expect f ≤ 1 := by
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) :=
        ThresholdFunctions.expect_mono fun x => by
          rcases hf x with hx | hx <;> simp [hx]
      _ = 1 := ThresholdFunctions.expect_const 1
  have hlog : 0 ≤ Real.log (1 / expect f) :=
    Real.log_nonneg ((one_le_div hα).mpr hα1)
  rcases (ThresholdFunctions.weightLevel_nonneg 1 f).eq_or_lt with hw0 | hw
  · rw [← hw0]
    positivity
  obtain ⟨a, hnorm, hcorr⟩ := ThresholdFunctions.exists_unit_linear_form f hw
  have h := indicator_linear_form_sq_le f hf hα a hnorm
  simpa only [innerProduct, hcorr, Real.sq_sqrt hw.le] using h
)

end BooleanAnalysis.Hypercontractivity
