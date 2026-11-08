/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.EvenMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.OneBit
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Extended power means on the cube

One stage of Borell's reverse Bonami–Beckner argument, retaining the extended-mean conventions.

## Main definitions

* `IsNonnegative`: pointwise nonnegativity of a cube function.
* `lpMean`: the extended power mean, with geometric and negative-exponent conventions.

## Main results

* `lpMean_of_pos`.
* `lpMean_nonneg`.
* `lpMean_mono`.
* `lpMean_const_mul`.
* `lpMean_dim_zero`.
* `lpMean_collapse_last`.
* `lpMean_comm`.
* `fourierCoeff_const_mul`.
* `noiseOp_const_mul`.
* `noiseOp_dim_zero`.
* `noiseOp_nonneg`.
* `noiseOp_affine_one_bit`.
* `fourierCoeff_avgLast_restrictions`.
* `fourierCoeff_diffLast_restrictions`.
* `noiseOp_snoc_slice`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.6–10.9.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

attribute [local simp] BooleanAnalysis.Hypercontractivity.cubeLpNorm

/-! ### The extended `L^p` means -/

/-- Pointwise nonnegativity, the natural domain of reverse hypercontractivity.
[OD14, Exs. 10.6--10.9] -/
def IsNonnegative (f : BooleanFunc n) : Prop :=
  ∀ x, 0 ≤ f x

open Classical in
/-- The uniform `L^p` mean for finite real exponents. At `p = 0` this is the geometric mean; for
`p ≤ 0`, a function with a zero has mean zero. [OD14, Exs. 10.6--10.9]
The ordinary expression is shared with `Hypercontractivity.cubeLpNorm`. The source also
defines the `p = -∞` mean as the minimum; that endpoint is not represented here. -/
noncomputable def lpMean (p : ℝ) (f : BooleanFunc n) : ℝ :=
  if (∃ x, f x = 0) ∧ p ≤ 0 then 0
  else if p = 0 then Real.exp (expect (fun x ↦ Real.log |f x|))
  else BooleanAnalysis.Hypercontractivity.cubeLpNorm p f

/-- For positive exponents, `lpMean` is the usual power mean. -/
lemma lpMean_of_pos (p : ℝ) (hp : 0 < p) (f : BooleanFunc n) :
    lpMean p f = (expect (fun x ↦ |f x| ^ p)) ^ (1 / p) := by
  simp [lpMean, hp.ne', not_le.mpr hp]

/-- Power means with a positive exponent are nonnegative. -/
lemma lpMean_nonneg (p : ℝ) (hp : 0 < p) (f : BooleanFunc n) : 0 ≤ lpMean p f := by
  rw [lpMean_of_pos p hp]
  exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _

/-- Power means with a positive exponent are monotone on nonnegative functions. -/
lemma lpMean_mono (p : ℝ) (hp : 0 < p) {f g : BooleanFunc n} (hf : IsNonnegative f)
    (hfg : ∀ x, f x ≤ g x) : lpMean p f ≤ lpMean p g := by
  have hg : ∀ x, 0 ≤ g x := fun x ↦ (hf x).trans (hfg x)
  rw [lpMean_of_pos p hp, lpMean_of_pos p hp]
  simp_rw [abs_of_nonneg (hf _), abs_of_nonneg (hg _)]
  refine Real.rpow_le_rpow
    (by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hf x) p) ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _ ↦ Real.rpow_le_rpow (hf x) (hfg x) hp.le)
    (pow_nonneg (by norm_num) _)

/-- Power means with a positive exponent are homogeneous. -/
lemma lpMean_const_mul (p c : ℝ) (hp : 0 < p) (hc : 0 < c) (f : BooleanFunc n) :
    lpMean p (fun x ↦ c * f x) = c * lpMean p f := by
  have hE : expect (fun x ↦ |c * f x| ^ p) = c ^ p * expect (fun x ↦ |f x| ^ p) := by
    unfold expect
    simp_rw [abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg _), ← Finset.mul_sum]
    ring
  rw [lpMean_of_pos p hp, lpMean_of_pos p hp, hE,
    Real.mul_rpow (Real.rpow_nonneg hc.le p) (expect_rpow_abs_nonneg p f),
    ← Real.rpow_mul hc.le, mul_one_div, div_self hp.ne', Real.rpow_one]

/-- On the empty cube every mean is the single value of the function. -/
lemma lpMean_dim_zero (p : ℝ) (hp : 0 < p) (f : BooleanFunc 0) (hf : IsNonnegative f) :
    lpMean p f = f (fun i ↦ Fin.elim0 i) := by
  rw [lpMean_of_pos p hp]
  unfold expect uniformWeight
  norm_num
  change (|f (fun i ↦ Fin.elim0 i)| ^ p) ^ p⁻¹ = f (fun i ↦ Fin.elim0 i)
  rw [abs_of_nonneg (hf _), ← Real.rpow_mul (hf _), show p * p⁻¹ = 1 by field_simp,
    Real.rpow_one]

/-- Splitting off the last coordinate: an `L^p` mean on `n + 1` bits is the `L^p`
mean over the first `n` bits of the one-bit `L^p` means. -/
lemma lpMean_collapse_last (p : ℝ) (hp : 0 < p) (f : BooleanFunc (n + 1)) :
    lpMean p f =
      lpMean p (fun x : BoolCube n ↦
        lpMean p (fun y : BoolCube 1 ↦ f (Fin.snoc x (y 0)))) := by
  have hinner (x : BoolCube n) :
      0 ≤ expect (fun y : BoolCube 1 ↦ |f (Fin.snoc x (y 0))| ^ p) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (abs_nonneg _) p
  rw [lpMean_of_pos p hp, lpMean_of_pos p hp]
  simp_rw [lpMean_of_pos p hp, abs_of_nonneg (Real.rpow_nonneg (hinner _) _),
    ← Real.rpow_mul (hinner _), show 1 / p * p = 1 by field_simp, Real.rpow_one]
  rw [norm_collapse_rpow p hp f]
  congr 2 with x
  unfold expect uniformWeight
  rw [show (Finset.univ : Finset (BoolCube 1)) = {fun _ ↦ false, fun _ ↦ true} by decide,
    Finset.sum_pair (by decide)]
  norm_num

/-- Iterated means over two blocks of coordinates commute. -/
lemma lpMean_comm (p : ℝ) (hp : 0 < p) (F : BoolCube n → BoolCube 1 → ℝ) :
    lpMean p (fun x ↦ lpMean p (fun y ↦ F x y)) =
      lpMean p (fun y ↦ lpMean p (fun x ↦ F x y)) := by
  have hx (x : BoolCube n) : 0 ≤ expect (fun y : BoolCube 1 ↦ |F x y| ^ p) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (abs_nonneg _) p
  have hy (y : BoolCube 1) : 0 ≤ expect (fun x : BoolCube n ↦ |F x y| ^ p) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) p
  simp_rw [lpMean_of_pos p hp, abs_of_nonneg (Real.rpow_nonneg (hx _) _),
    abs_of_nonneg (Real.rpow_nonneg (hy _) _), ← Real.rpow_mul (hx _), ← Real.rpow_mul (hy _),
    show 1 / p * p = 1 by field_simp, Real.rpow_one]
  congr 1
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, mul_comm (uniformWeight n)]

/-! ### The noise operator on nonnegative and on affine functions -/

/-- Fourier coefficients are homogeneous. -/
lemma fourierCoeff_const_mul (c : ℝ) (f : BooleanFunc n) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ c * f x) S = c * fourierCoeff f S := by
  unfold fourierCoeff innerProduct expect
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- The noise operator is homogeneous. -/
lemma noiseOp_const_mul (ρ c : ℝ) (f : BooleanFunc n) :
    noiseOp ρ (fun x ↦ c * f x) = fun x ↦ c * noiseOp ρ f x := by
  funext x
  unfold noiseOp
  simp_rw [fourierCoeff_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ ↦ by ring

/-- On the empty cube the noise operator is the identity. -/
lemma noiseOp_dim_zero (ρ : ℝ) (f : BooleanFunc 0) : noiseOp ρ f = f := by
  funext x
  conv_rhs => rw [walsh_expansion f]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun i _ ↦ i.elim0
  simp

/-- The noise operator preserves nonnegativity, since its kernel is nonnegative. -/
lemma noiseOp_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {f : BooleanFunc n}
    (hf : IsNonnegative f) : IsNonnegative (noiseOp ρ f) := fun x ↦ by
  rw [noiseOp_eq_kernel_sum]
  exact Finset.sum_nonneg fun y _ ↦
    mul_nonneg (noiseKernel_nonneg hρ0 hρ1 x y) (hf y)

/-- The noise operator shrinks the coefficient of a one-bit affine function. -/
lemma noiseOp_affine_one_bit (ρ a : ℝ) :
    noiseOp ρ (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0)) =
      fun x ↦ 1 + (ρ * a) * boolToSign (x 0) := by
  funext x
  unfold noiseOp
  rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} by decide,
    Finset.sum_pair (by decide)]
  norm_num [fourierCoeff, innerProduct, expect, uniformWeight, chiS, boolToSign]
  repeat' first
    | rw [show (Finset.univ : Finset (BoolCube 1)) =
        {fun _ ↦ false, fun _ ↦ true} by decide]
    | rw [Finset.sum_pair (by decide)]
  cases hx : x 0 <;> norm_num [boolToSign] <;> ring

/-- The Fourier coefficients of the average of the two restrictions of the last bit. -/
lemma fourierCoeff_avgLast_restrictions (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (avgLast f) S =
      (fourierCoeff (restrictLast f false) S + fourierCoeff (restrictLast f true) S) / 2 := by
  unfold fourierCoeff innerProduct expect avgLast
  ring_nf
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- The Fourier coefficients of the difference of the two restrictions of the last bit. -/
lemma fourierCoeff_diffLast_restrictions (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (diffLast f) S =
      (fourierCoeff (restrictLast f false) S - fourierCoeff (restrictLast f true) S) / 2 := by
  unfold fourierCoeff innerProduct expect diffLast
  ring_nf
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- Noise on `n + 1` bits factors as noise on the last bit applied to the noised
restrictions of the first `n` bits. -/
lemma noiseOp_snoc_slice (ρ : ℝ) (f : BooleanFunc (n + 1)) (x : BoolCube n) (y : BoolCube 1) :
    noiseOp ρ f (Fin.snoc x (y 0)) =
      noiseOp ρ (fun t : BoolCube 1 ↦ noiseOp ρ (restrictLast f (t 0)) x) y := by
  have hy : y = Fin.snoc (fun i ↦ Fin.elim0 i) (y 0) := by
    funext i
    fin_cases i
    rfl
  conv_lhs => rw [noiseOp_snoc]
  conv_rhs => rw [hy, noiseOp_snoc, noiseOp_dim_zero, noiseOp_dim_zero]
  dsimp [avgLast, diffLast, restrictLast]
  unfold noiseOp
  simp_rw [fourierCoeff_avgLast_restrictions, fourierCoeff_diffLast_restrictions]
  simp only [show (Fin.snoc (fun i ↦ Fin.elim0 i) false : BoolCube 1) 0 = false from rfl,
    show (Fin.snoc (fun i ↦ Fin.elim0 i) true : BoolCube 1) 0 = true from rfl]
  ring_nf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  repeat rw [← Finset.sum_mul]
  ring

end BooleanAnalysis.Hypercontractivity
