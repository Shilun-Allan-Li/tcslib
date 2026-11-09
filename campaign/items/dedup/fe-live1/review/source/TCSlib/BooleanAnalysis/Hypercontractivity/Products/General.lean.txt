/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.NoiseKernel
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Tensorization
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseContraction
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hypercontractivity on finite product spaces

## Main definitions

The definitions are bundled in `FiniteProduct`. Norms here have finite real exponents.

## Main results

* `one_coordinate_hypercontractivity`: Corollary 10.20.
* `product_hypercontractivity`: the General Hypercontractivity Theorem, with both
  the `(2,q)` and conjugate `(q',2)` estimates and possibly different coordinate spaces.
* `product_hypercontractivity_induction`: tensorization for finite ordered exponents `p ≤ q`.
* `product_hypercontractivity_sharp`: both conjugate estimates at the sharp discrete radius.

The one-coordinate corollary reuses the general product theorem.
The minimum-atom estimate follows from the sharp radius and a scalar radius comparison.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Chapter 10, opening theorem, Remark 9.20, §10.1,
  and Corollary 10.20.
-/

open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- For finite exponents `p ≥ 1` and `q > 1`, coordinatewise noise
contraction implies contraction on the heterogeneous finite product.
[OD14, §10.1, Hypercontractivity Induction Theorem; Rem. 9.20]
This technical form does not require an ordering of the two exponents.

**Proof sketch.** Write coordinate noise using its nonnegative resampling
kernel. Convert the coordinate norm estimates to two-function pairing
bounds, tensorize those bounds, and recover the product norm estimate by
weighted norm duality. The product resampling kernel represents precisely
the spectral noise operator. -/
private theorem product_hypercontractivity_induction_gt_one {n : ℕ}
    (P : FiniteProduct.{u} n)
    (p q ρ : ℝ) (hp : 1 ≤ p) (hq : 1 < q)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcoord : ∀ i (g : P.Ω i → ℝ),
      ((∑ x, P.weight i x *
        |ρ * g x + (1 - ρ) * (∑ y, P.weight i y * g y)| ^ q) ^ (1 / q)) ≤
      ((∑ x, P.weight i x * |g x| ^ p) ^ (1 / p)))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm p f :=
  (by
  classical
  unfold FiniteProduct.norm FiniteProduct.expect FiniteProduct.mass
  simp_rw [P.noise_kernel]
  refine FiniteTensorization.norm_tensorization P.Ω P.weight
    (fun i a => (P.weight_pos i a).le)
    (fun i a b =>
      ρ * (if a = b then 1 else 0) + (1 - ρ) * P.weight i b)
    ?_ p q hp hq ?_ f
  · intro i a b
    exact add_nonneg
      (mul_nonneg hρ (by split_ifs <;> norm_num))
      (mul_nonneg (sub_nonneg.mpr hρ1) (P.weight_pos i b).le)
  · intro i g
    simpa only [add_mul, Finset.sum_add_distrib, mul_assoc,
      ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, ← Finset.mul_sum] using hcoord i g
)

/-- Coordinatewise hypercontractivity tensorizes to the full product for finite
ordered exponents `1 ≤ p ≤ q`.
[OD14, §10.1, Hypercontractivity Induction Theorem]
The source allows any `p,q ≥ 1`. This declaration specializes to `p ≤ q`, the range needed
for the finite-`q` General Hypercontractivity Theorem, and does not represent infinite
exponents or the source's `p > q` contraction cases.

**Proof sketch.** For `q > 1`, express noise through its nonnegative product
resampling kernel. Weighted Hölder converts coordinate contraction to
two-function estimates, which tensorize by induction on coordinate slices.
Weighted norm duality recovers the product norm bound. If `q = 1`, the
exponent ordering forces `p = 1`, and preservation of the product law gives
the absolute first-moment contraction. -/
theorem product_hypercontractivity_induction {n : ℕ} (P : FiniteProduct.{u} n)
    (p q ρ : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcoord : ∀ i (g : P.Ω i → ℝ),
      ((∑ x, P.weight i x *
        |ρ * g x + (1 - ρ) * (∑ y, P.weight i y * g y)| ^ q) ^ (1 / q)) ≤
      ((∑ x, P.weight i x * |g x| ^ p) ^ (1 / p)))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm p f := (by
  rcases lt_or_eq_of_le (hp.trans hpq) with hq | hq
  · exact product_hypercontractivity_induction_gt_one
      P p q ρ hp hq hρ hρ1 hcoord f
  · have hp1 : p = 1 := by linarith
    subst p
    subst q
    exact P.noise_norm_one_le ρ hρ hρ1 f
)


/-- An inequality between squared real-power norms implies the corresponding
norm inequality when both moment bases are nonnegative.

**Proof sketch.** The real-power norms are nonnegative. Express their squares
by doubling the exponents and use monotonicity of squaring on nonnegative reals. -/
private theorem rpow_norm_le_of_sq_moments
    (A B p q : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ^ (2 / q) ≤ B ^ (2 / p)) :
    A ^ (1 / q) ≤ B ^ (1 / p) :=
  (by
  apply (sq_le_sq₀ (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)).mp
  simpa only [← Real.rpow_mul_natCast hA (1 / q) 2,
    ← Real.rpow_mul_natCast hB (1 / p) 2, Nat.cast_ofNat,
    show (1 / q) * (2 : ℝ) = 2 / q by ring,
    show (1 / p) * (2 : ℝ) = 2 / p by ring] using h
)

/-- On a finite probability space with nonnegative weights, the quadratic
noise objective increases with the nonnegative noise parameter.
This is the finite mean-square-plus-variance calculation underlying
[OD14, Thm. 10.18].

**Proof sketch.** Weighted Cauchy–Schwarz bounds the squared mean by the second
moment. Write the objective as the squared mean plus the squared noise rate
times this nonnegative variance. Increasing the nonnegative rate increases
its square and therefore the objective. -/
private theorem finite_noise_quadratic_mono {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρ σ : ℝ) (hρ : 0 ≤ ρ) (hρσ : ρ ≤ σ) (g : ι → ℝ) :
    ρ ^ (2 : ℕ) * (∑ i, w i * g i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * g i) ^ (2 : ℕ) ≤
      σ ^ (2 : ℕ) * (∑ i, w i * g i ^ (2 : ℕ)) +
        (1 - σ ^ (2 : ℕ)) * (∑ i, w i * g i) ^ (2 : ℕ) :=
  (by
  have hvariance := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := Finset.univ) (r := fun i => w i * g i)
    (f := fun i => w i * g i ^ 2) (g := w)
    (fun i _ => mul_nonneg (hw i) (sq_nonneg (g i)))
    (fun i _ => hw i) (fun i _ => by ring)
  simp only [hw_sum, mul_one] at hvariance
  have hrates := (sq_le_sq₀ hρ (hρ.trans hρσ)).2 hρσ
  nlinarith [mul_nonneg (sub_nonneg.mpr hrates) (sub_nonneg.mpr hvariance)]
)

/-- On a finite probability space whose atoms have mass at least
`0 < lam < 1 / 2`, every nonnegative noise rate at most the sharp discrete
radius satisfies both the `2`-to-`q` and conjugate-to-`2` norm estimates.
[OD14, Thm. 10.18; Prop. 9.19 (proof)]

**Proof sketch.** Apply the existing sharp finite-space quadratic contraction
at the sharp radius. Monotonicity of the quadratic noise objective extends
this contraction to the smaller rate. Finite-space self-adjoint duality
gives the squared `2`-to-`q` estimate, and the finite-noise second-moment
identity gives the squared conjugate-to-`2` estimate. Nonnegativity of the
moments removes the squares in both inequalities. -/
private theorem finite_coordinate_hypercontractivity_sharp
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_sum : ∑ i, w i = 1)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2)
    (hπ : ∀ i, lam ≤ w i) (hq : 2 < q)
    (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam)
    (g : ι → ℝ) :
    (∑ x, w x *
      |ρ * g x + (1 - ρ) * (∑ y, w y * g y)| ^ q) ^ (1 / q) ≤
        (∑ x, w x * |g x| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ∧
      (∑ x, w x *
        |ρ * g x + (1 - ρ) * (∑ y, w y * g y)| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
        (∑ x, w x * |g x| ^ (q / (q - 1))) ^
          (1 / (q / (q - 1))) :=
  (by
  have hw : ∀ i, 0 ≤ w i := fun i => (le_of_lt hlam).trans (hπ i)
  have hmoment (f : ι → ℝ) (r : ℝ) : 0 ≤ ∑ i, w i * |f i| ^ r :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hcontract (f : ι → ℝ) :
      ρ ^ 2 * (∑ i, w i * f i ^ 2) +
        (1 - ρ ^ 2) * (∑ i, w i * f i) ^ 2 ≤
      (∑ i, w i * |f i| ^ (q / (q - 1))) ^ (2 / (q / (q - 1))) :=
    (finite_noise_quadratic_mono w hw hw_sum ρ (sharpDiscreteRadius q lam)
      hρ hbound f).trans
      (SharpDiscrete.finite_noise_sharp_contraction
        w hw_sum q lam hq hlam hlamhalf hπ f)
  constructor
  · apply rpow_norm_le_of_sq_moments _ _ 2 q (hmoment _ _) (hmoment _ _)
    simpa only [Real.rpow_two, sq_abs,
      div_self (two_ne_zero : (2 : ℝ) ≠ 0), Real.rpow_one] using
      SharpDiscrete.finite_noise_duality w hw hw_sum q hq ρ hcontract g
  · apply rpow_norm_le_of_sq_moments _ _ (q / (q - 1)) 2
      (hmoment _ _) (hmoment _ _)
    simpa only [Real.rpow_two, sq_abs,
      div_self (two_ne_zero : (2 : ℝ) ≠ 0), Real.rpow_one] using
      (SharpDiscrete.finite_noise_identities w hw_sum ρ g g).1.trans_le (hcontract g)
)

/-- The sharp discrete radius also tensorizes, giving the improved parameter explicitly
mentioned in the General Hypercontractivity Theorem.
[OD14, Ch. 10, General Hypercontractivity Theorem and Thm. 10.18]

**Proof sketch.** Apply the sharp finite conjugate-noise inequality on each coordinate.
Weighted Cauchy–Schwarz makes its quadratic bound monotone in the nonnegative noise radius.
Self-adjoint duality gives the forward coordinate estimate; take square roots of both
moment bounds and tensorize the resulting norm inequalities. -/
theorem product_hypercontractivity_sharp {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam)
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f := (by
  have hqone : 1 < q := lt_trans one_lt_two hq
  have hconj : Real.HolderConjugate q (q / (q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hqone).2 rfl
  have hρ1 : ρ ≤ 1 :=
    hbound.trans (SharpDiscrete.radius_pos_lt_one q lam hq hlam hlamhalf).2.le
  have hcoord (i : Fin n) (g : P.Ω i → ℝ) :=
    finite_coordinate_hypercontractivity_sharp
      (P.weight i) (P.weight_sum i) lam q ρ hlam hlamhalf (hπ i) hq hρ hbound g
  constructor
  · exact product_hypercontractivity_induction_gt_one P 2 q ρ
      one_le_two hqone hρ hρ1 (fun i g => (hcoord i g).1) f
  · exact product_hypercontractivity_induction_gt_one P (q / (q - 1)) 2 ρ
      hconj.symm.lt.le one_lt_two hρ hρ1 (fun i g => (hcoord i g).2) f
)

/-- For `0 < a ≤ b`, the hyperbolic-sine ratio is at least
`(a / b) * exp (a - b)`.
This is a technical ingredient for [OD14, Ch. 10, General Hypercontractivity Theorem].

**Proof sketch.** Convexity of the exponential between zero and `-2 * b`
gives `(a / b) * (1 - exp (-2 * b)) ≤ 1 - exp (-2 * a)`.
Expand each hyperbolic sine as `exp x * (1 - exp (-2 * x)) / 2`
and divide by the positive denominator. -/
private theorem sinh_ratio_lower_bound (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    (a / b) * Real.exp (a - b) ≤ Real.sinh a / Real.sinh b :=
  (by
    have hb : 0 < b := ha.trans_le hab
    have hblend : (1 - a / b) * 0 + (a / b) * (-2 * b) = -2 * a := by
      field_simp [hb.ne']
      ring
    have hconv :
        Real.exp ((1 - a / b) * 0 + (a / b) * (-2 * b)) ≤
          (1 - a / b) * Real.exp 0 + (a / b) * Real.exp (-2 * b) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _)
        (sub_nonneg.mpr (div_le_one_of_le₀ hab hb.le))
        (div_nonneg ha.le hb.le) (by ring)
    rw [hblend, Real.exp_zero] at hconv
    have hsmall : (a / b) * (1 - Real.exp (-2 * b)) ≤
        1 - Real.exp (-2 * a) := by
      nlinarith
    have hsinh (x : ℝ) :
        Real.sinh x = Real.exp x / 2 * (1 - Real.exp (-2 * x)) := by
      rw [Real.sinh_eq]
      have hexp : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      nlinarith
    apply (le_div_iff₀ (Real.sinh_pos_iff.mpr hb)).2
    rw [hsinh a, hsinh b, Real.exp_sub]
    convert mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ Real.exp a / 2 by positivity) using 1
    field_simp [hb.ne', Real.exp_ne_zero b]
)

/-- For `q > 2` and `0 < lam < 1`, the minimum-atom radius is at most
the sharp discrete radius evaluated at `lam / (1 + lam)`.
[OD14, Ch. 10, General Hypercontractivity Theorem; Thm. 10.18]
This comparison lowers the atom bound below one half, where the sharp-radius formula applies.

**Proof sketch.** Set `u = log (1 / lam) > 0`. The logarithmic odds at
`lam / (1 + lam)` equal `u`. Apply the hyperbolic-sine ratio bound to
`u / q` and `u / (q / (q - 1))`. Their ratio is `1 / (q - 1)`,
and the exponential of their difference is `lam ^ (1 - 2 / q)`.
The resulting bound compares the squares of the two radii; take square roots. -/
private theorem coarse_radius_le_sharp (q lam : ℝ)
    (hq : 2 < q) (hlam : 0 < lam) (hlam1 : lam < 1) :
    (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q) ≤
      sharpDiscreteRadius q (lam / (1 + lam)) :=
  (by
  have hqpos : 0 < q := lt_trans zero_lt_two hq
  have hqsub : 0 < q - 1 := by linarith
  let u := Real.log (1 / lam)
  have hu : 0 < u := Real.log_pos ((one_lt_div hlam).2 hlam1)
  have hab : u / q ≤ u / (q / (q - 1)) :=
    div_le_div_of_nonneg_left hu.le (div_pos hqpos hqsub)
      ((div_le_iff₀ hqsub).2 (by
        nlinarith [mul_nonneg hqpos.le (show 0 ≤ q - 2 by linarith)]))
  have hquot : (u / q) / (u / (q / (q - 1))) = 1 / (q - 1) := by
    field_simp [hu.ne', hqpos.ne', hqsub.ne']
  have hlog : u = -Real.log lam := by
    simp only [u, one_div, Real.log_inv]
  have hdiff : u / q - u / (q / (q - 1)) =
      Real.log lam * (1 - 2 / q) := by
    rw [hlog]
    field_simp [hqpos.ne', hqsub.ne']
    ring
  have hratio := sinh_ratio_lower_bound
    (u / q) (u / (q / (q - 1))) (div_pos hu hqpos) hab
  rw [hquot, hdiff, ← Real.rpow_def_of_pos hlam (1 - 2 / q)] at hratio
  have hodds : (1 - lam / (1 + lam)) / (lam / (1 + lam)) = 1 / lam := by
    field_simp [hlam.ne', (by positivity : 1 + lam ≠ 0)]
    ring
  unfold sharpDiscreteRadius
  rw [hodds]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hqsub.le,
    ← Real.rpow_mul_natCast hlam.le (1 / 2 - 1 / q) 2, Nat.cast_ofNat,
    show (1 / (2 : ℝ) - 1 / q) * (2 : ℝ) = 1 - 2 / q by ring]
  exact hratio
)

/-- If every coordinate atom has mass at least one, product noise at every
real rate satisfies both conjugate hypercontractive estimates for `q > 2`.
This is the singleton endpoint permitted by the bundled formulation of
[OD14, Ch. 10, General Hypercontractivity Theorem].

**Proof sketch.** Normalization forces every coordinate weight to equal one.
Two distinct outcomes would contribute at least two to a coordinate's total mass,
so the product has a single outcome. Noise fixes every function, and every norm
with nonzero exponent equals its absolute value at that outcome. -/
private theorem product_hypercontractivity_atom_one {n : ℕ}
    (P : FiniteProduct.{u} n) (q ρ : ℝ)
    (hπ : P.AtomBound 1) (hq : 2 < q)
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f :=
  (by
  classical
  have hweight (i : Fin n) (a : P.Ω i) : P.weight i a = 1 :=
    le_antisymm
      ((Finset.single_le_sum (fun b _ => (P.weight_pos i b).le)
        (Finset.mem_univ a)).trans_eq (P.weight_sum i))
      (hπ i a)
  have hpoint (x y : P.Point) : x = y := by
    funext i
    by_contra hne
    have htwo := Finset.add_le_sum
      (fun a _ => (P.weight_pos i a).le)
      (Finset.mem_univ (x i)) (Finset.mem_univ (y i)) hne
    rw [hweight i (x i), hweight i (y i), P.weight_sum i] at htwo
    norm_num at htwo
  have hsum (x : P.Point) (F : P.Point → ℝ) : ∑ y, F y = F x :=
    Fintype.sum_eq_single x (fun y hy => (hy (hpoint y x)).elim)
  have hmass (x : P.Point) : P.mass x = 1 := by
    simp [FiniteProduct.mass, hweight]
  have hnoise : P.noise ρ f = f := by
    funext x
    rw [P.noise_kernel, hsum x]
    simp [hweight, show ρ + (1 - ρ) = 1 by ring]
  have hnonempty : Nonempty P.Point := by
    by_contra hn
    haveI : IsEmpty P.Point := not_nonempty_iff.mp hn
    simpa using P.mass_sum
  obtain ⟨x⟩ := hnonempty
  have hnorm (r : ℝ) (hr : r ≠ 0) : P.norm r f = |f x| := by
    simp only [FiniteProduct.norm, FiniteProduct.expect, hmass, one_mul]
    rw [hsum x]
    simpa only [one_div] using Real.rpow_rpow_inv (abs_nonneg (f x)) hr
  have hqpos : 0 < q := lt_trans zero_lt_two hq
  have hqsub : 0 < q - 1 := by linarith
  rw [hnoise, hnorm q hqpos.ne', hnorm 2 two_ne_zero,
    hnorm (q / (q - 1)) (div_ne_zero hqpos.ne' hqsub.ne')]
  exact ⟨le_rfl, le_rfl⟩
)

/-- On a heterogeneous finite product with every atom at least `lam`, the minimum-atom
radius gives both conjugate hypercontractive inequalities.
[OD14, Ch. 10, General Hypercontractivity Theorem]

**Proof sketch.** For `lam < 1`, lower the atom bound to `lam / (1 + lam)`.
Convexity of the exponential compares the stated radius with the sharp radius at this
smaller atom bound, so the sharp product theorem applies. At `lam = 1`, normalization
forces each coordinate to be a singleton; noise fixes every function and all norms agree. -/
theorem product_hypercontractivity {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ)
    (hbound : ρ ≤ (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f := (by
  rcases lt_or_eq_of_le hlam1 with hlamlt | rfl
  · have hden : 0 < 1 + lam := by linarith
    exact product_hypercontractivity_sharp P (lam / (1 + lam)) q ρ
      (div_pos hlam hden)
      ((div_lt_iff₀ hden).2 (by linarith))
      (fun i x => (div_le_self hlam.le (by linarith)).trans (hπ i x))
      hq hρ (hbound.trans (coarse_radius_le_sharp q lam hq hlam hlamlt)) f
  · exact product_hypercontractivity_atom_one P q ρ hπ hq f
)

/-- On a single finite coordinate, noise is hypercontractive from `2` to `q` and from
`q/(q-1)` to `2` at the minimum-atom radius. [OD14, Cor. 10.20]
The book assumes at least two outcomes; the singleton case satisfies the same statement.

**Proof sketch.** Specialize the general product theorem to one coordinate. -/
theorem one_coordinate_hypercontractivity (P : FiniteProduct.{u} 1)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ)
    (hbound : ρ ≤ (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q))
    (f : P.Point → ℝ) :
    P.norm q (P.noise ρ f) ≤ P.norm 2 f ∧
      P.norm 2 (P.noise ρ f) ≤ P.norm (q / (q - 1)) f := by
  exact product_hypercontractivity P lam q ρ hlam hlam1 hπ hq hρ hbound f

end BooleanAnalysis.Hypercontractivity
