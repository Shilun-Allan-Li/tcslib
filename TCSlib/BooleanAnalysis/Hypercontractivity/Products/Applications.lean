/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Applications.LowDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Applications of finite-product hypercontractivity

## Contents

* `Applications.LowDegree`: low-degree norm comparisons, one-sided anticoncentration,
  and concentration on finite products.

## Main definitions

`productNormComparisonConstant` is defined in `Parameters`, with its continuous value
`e` at `lam = 1/2`.

## Main results

* `product_smallSet_expansion`, `product_smallSet_expansion_sharp`: small-set expansion.
* `product_stableInfluence`, `product_stableInfluence_four`, `product_stableInfluence_sharp`:
  stable-influence bounds.
* `product_kkl_isoperimetric`, `product_kkl`: the product KKL influence bounds.
* `product_friedgut_junta`: the product Friedgut junta theorem.
* `productNormComparisonConstant_asymptotic_zero`, `productNormComparisonConstant_tendsto_half`:
  limiting behavior of the norm-comparison constant.

The product bundle permits heterogeneous coordinates; the homogeneous product statements
in the source follow by choosing the same law at every coordinate. The low-degree norm
comparisons, one-sided anticoncentration, and concentration are proved in the imported
child. Small-set expansion, stable-influence bounds, KKL, and Friedgut's junta theorem
are proved here.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.3, Theorems 10.21–10.26 and the named KKL and junta theorems.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u


/-- Noise stability at the squared rate `c ^ 2` equals the squared second norm after
noise at rate `c`. [OD14, Thm. 10.25, proof; §8.2]
The spectral definition extends this identity to every real rate and heterogeneous
finite coordinate laws.

**Proof sketch.** Noise is self-adjoint because each component is a linear combination
of self-adjoint conditional expectations. Applying noise twice squares each component
multiplier. Move one noise operator across the expectation pairing, then identify the
second moment with the squared second norm. -/
private theorem product_stability_sq_eq_norm_noise_sq {n : ℕ}
    (P : FiniteProduct.{u} n) (c : ℝ) (f : P.Point → ℝ) :
    P.stability (c ^ 2) f = P.norm 2 (P.noise c f) ^ 2 := (by
  classical
  have hself (g h : P.Point → ℝ) :
      P.expect (fun x => g x * P.noise c h x) =
        P.expect (fun x => P.noise c g x * h x) := by
    simp only [FiniteProduct.noise, FiniteProduct.component,
      Finset.mul_sum, Finset.sum_mul]
    simp_rw [P.expect_sum]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro T _
    calc
      _ = (c ^ S.card * (-1 : ℝ) ^ (S.card - T.card)) *
          P.expect (fun x => g x * P.condExp T h x) := by
        rw [← P.expect_const_mul]
        congr 1
        funext x
        ring
      _ = _ := by
        rw [P.condExp_selfAdjoint, ← P.expect_const_mul]
        congr 1
        funext x
        ring
  have hcomp : P.noise c (P.noise c f) = P.noise (c ^ 2) f := by
    funext x
    change (∑ S : Finset (Fin n), c ^ S.card *
        P.component S (P.noise c f) x) =
      ∑ S : Finset (Fin n), (c ^ 2) ^ S.card * P.component S f x
    apply Finset.sum_congr rfl
    intro S _
    rw [RandomizationAux.component_noise, ← mul_assoc, ← mul_pow, pow_two]
  have hnonneg : 0 ≤ P.expect (fun x => P.noise c f x ^ 2) := by
    unfold FiniteProduct.expect
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (sq_nonneg _)
    unfold FiniteProduct.mass
    exact Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
  calc
    P.stability (c ^ 2) f = P.expect (fun x => P.noise c f x ^ 2) := by
      unfold FiniteProduct.stability
      rw [← hcomp, hself]
      simp only [pow_two]
    _ = _ := by
      unfold FiniteProduct.norm
      simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
      exact (Real.sq_sqrt hnonneg).symm
)



/-- The squared `p`-norm of an indicator equals its event probability raised to
`2 / p`, for every positive real exponent `p`. [OD14, Thm. 10.25, proof]

**Proof sketch.** Every positive power of the indicator equals the indicator.
Its moment is therefore the event probability; combine the norm's reciprocal
exponent with the outer square. -/
private theorem product_indicator_norm_sq {n : ℕ} (P : FiniteProduct.{u} n)
    (p : ℝ) (hp : 0 < p) (A : P.Point → Prop) :
    P.norm p (P.indicator A) ^ 2 = P.prob A ^ (2 / p) := (by
  classical
  have hmoment : (fun x => |P.indicator A x| ^ p) = P.indicator A := by
    funext x
    by_cases hx : A x <;>
      simp [FiniteProduct.indicator, hx, Real.zero_rpow hp.ne']
  have hnonneg : 0 ≤ P.prob A := by
    unfold FiniteProduct.prob FiniteProduct.expect
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg
    · unfold FiniteProduct.mass
      exact Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
    · by_cases hx : A x <;> simp [FiniteProduct.indicator, hx]
  unfold FiniteProduct.norm
  rw [hmoment]
  change (P.prob A ^ (1 / p)) ^ 2 = P.prob A ^ (2 / p)
  rw [← Real.rpow_two, ← Real.rpow_mul hnonneg]
  congr 1
  ring
)


/-- The noise stability of an indicator is at most its volume to the power `2-2/q`
at the squared minimum-atom radius. [OD14, Thm. 10.25]

**Proof sketch.** Express stability as the squared `L²` norm after noise at `√ρ`, apply
the conjugate hypercontractive bound, and evaluate the norm of the indicator. -/
theorem product_smallSet_expansion {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 ≤ q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ (1 / (q - 1)) * lam ^ (1 - 2 / q))
    (A : P.Point → Prop) :
    P.stability ρ (P.indicator A) ≤ P.prob A ^ (2 - 2 / q) := (by
  classical
  rcases eq_or_lt_of_le hq with rfl | hq
  · -- At the endpoint, first-moment contraction bounds indicator stability.
    norm_num at hbound ⊢
    calc
      P.stability ρ (P.indicator A) ≤
          P.norm 1 (P.noise ρ (P.indicator A)) := by
        simp only [FiniteProduct.stability, FiniteProduct.norm,
          one_div_one, Real.rpow_one, FiniteProduct.expect]
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left
        · by_cases hx : A x
          · simpa [FiniteProduct.indicator, hx] using
              le_abs_self (P.noise ρ (P.indicator A) x)
          · simp [FiniteProduct.indicator, hx]
        · unfold FiniteProduct.mass
          exact Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
      _ ≤ P.norm 1 (P.indicator A) :=
        P.noise_norm_one_le ρ hρ hbound (P.indicator A)
      _ = P.prob A := by
        unfold FiniteProduct.norm FiniteProduct.prob
        norm_num
        congr 1
        funext x
        by_cases hx : A x <;> simp [FiniteProduct.indicator, hx]
  · have hrate : Real.sqrt ρ ≤
        (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q) := by
      apply (Real.sqrt_le_left (by positivity : 0 ≤
        (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q))).2
      calc
        ρ ≤ (1 / (q - 1)) * lam ^ (1 - 2 / q) := hbound
        _ = ((1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q)) ^ 2 := by
          rw [mul_pow, div_pow, one_pow,
            Real.sq_sqrt (by linarith : 0 ≤ q - 1),
            ← Real.rpow_two, ← Real.rpow_mul hlam.le,
            show (1 / 2 - 1 / q) * 2 = 1 - 2 / q by ring]
    have hcontract :=
      (product_hypercontractivity P lam q (Real.sqrt ρ) hlam hlam1 hπ hq
        (Real.sqrt_nonneg ρ) hrate (P.indicator A)).2
    have hnorm : 0 ≤ P.norm 2 (P.noise (Real.sqrt ρ) (P.indicator A)) := by
      unfold FiniteProduct.norm
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_nonneg _
    calc
      P.stability ρ (P.indicator A) =
          P.norm 2 (P.noise (Real.sqrt ρ) (P.indicator A)) ^ 2 := by
        simpa only [Real.sq_sqrt hρ] using
          product_stability_sq_eq_norm_noise_sq P (Real.sqrt ρ) (P.indicator A)
      _ ≤ P.norm (q / (q - 1)) (P.indicator A) ^ 2 :=
        pow_le_pow_left₀ hnorm hcontract 2
      _ = P.prob A ^ (2 / (q / (q - 1))) :=
        product_indicator_norm_sq P (q / (q - 1))
          (div_pos (by linarith) (by linarith)) A
      _ = P.prob A ^ (2 - 2 / q) := by
        congr 1
        field_simp [ne_of_gt (show (0 : ℝ) < q by linarith),
          ne_of_gt (show (0 : ℝ) < q - 1 by linarith)]
)

/-- Multiplying stable coordinate influence by a nonnegative rate gives the
squared second norm of the coordinate Laplacian after noise at the square-root
rate. [OD14, §8.3; Thm. 10.26, proof]
This identity includes rate zero and heterogeneous finite coordinate laws.

**Proof sketch.** Conditional averaging removes precisely the components
containing the coordinate. Parseval and the component multiplier for noise
then identify the two sums. -/
private theorem product_stableInfluence_eq_sq_norm_noise_laplacian
    {n : ℕ} (P : FiniteProduct.{u} n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : P.Point → ℝ) (i : Fin n) :
    ρ * P.stableInfluence ρ i f =
      P.norm 2 (P.noise (Real.sqrt ρ) (P.laplacian i f)) ^ 2 := (by
  classical
  have hnonneg :
      0 ≤ P.expect (fun x => P.noise (Real.sqrt ρ) (P.laplacian i f) x ^ 2) := by
    unfold FiniteProduct.expect
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (sq_nonneg _)
    unfold FiniteProduct.mass
    exact Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le
  unfold FiniteProduct.norm
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt hnonneg, P.parseval]
  unfold FiniteProduct.stableInfluence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  simp_rw [RandomizationAux.component_noise, RandomizationAux.component_laplacian]
  by_cases hi : i ∈ S
  · simp only [hi, if_pos, mul_pow, P.expect_const_mul]
    rw [← pow_mul, Nat.mul_comm S.card 2, pow_mul, Real.sq_sqrt hρ]
    have hcard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨i, hi⟩
    rw [← mul_assoc, mul_comm ρ (ρ ^ (S.card - 1)),
      ← pow_succ, Nat.sub_add_cancel hcard]
  · simp [hi, P.expect_const]
)

/-- For a Boolean product function, the first absolute moment of its residual
after conditional expectation equals that residual's second moment.
[OD14, Prop. 8.24; Ex. 8.10]
The coordinate-conditioning identity is extended to conditioning on any
coordinate set, since the same Boolean conditional-variance argument applies.

**Proof sketch.** The conditional mean lies between minus one and one, so the
absolute residual equals one minus the product of the function and its
conditional mean. Self-adjointness and idempotence of conditional expectation
identify the expected product with the conditional mean's second moment.
Expanding the residual square gives the same expectation. -/
private theorem product_boolean_residual_abs_expect {n : ℕ}
    (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (hf : P.IsBoolean f)
    (S : Finset (Fin n)) :
    P.expect (fun x => |f x - P.condExp S f x|) =
      P.expect (fun x => (f x - P.condExp S f x) ^ 2) :=
  (by
  classical
  let m := P.condExp S f
  have hmean (x : P.Point) : |m x| ≤ 1 := by
    dsimp only [m, FiniteProduct.condExp, FiniteProduct.expect]
    calc
      _ ≤ ∑ y, |P.mass y * f (fun j => if j ∈ S then x j else y j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, P.mass y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [abs_mul, abs_of_nonneg (show 0 ≤ P.mass y from by
          unfold FiniteProduct.mass
          exact Finset.prod_nonneg fun j _ => (P.weight_pos j (y j)).le)]
        rcases hf (fun j => if j ∈ S then x j else y j) with hy | hy <;>
          simp [hy]
      _ = 1 := P.mass_sum
  have habs (x : P.Point) : |f x - m x| = 1 - f x * m x := by
    rcases hf x with hx | hx
    · rw [hx, abs_of_nonpos (by linarith [(abs_le.mp (hmean x)).1])]
      ring
    · rw [hx, abs_of_nonneg (by linarith [(abs_le.mp (hmean x)).2])]
      ring
  have hcross : P.expect (fun x => f x * m x) =
      P.expect (fun x => m x ^ 2) := by
    calc
      _ = P.expect (fun x => f x * P.condExp S m x) := by
        simp only [m, P.condExp_comp, Finset.inter_self]
      _ = P.expect (fun x => m x * m x) :=
        P.condExp_selfAdjoint S f m
      _ = _ := by simp only [pow_two]
  change P.expect (fun x => |f x - m x|) =
    P.expect (fun x => (f x - m x) ^ 2)
  calc
    _ = P.expect (fun x => 1 - f x * m x) := by simp_rw [habs]
    _ = P.expect (fun _ => 1) - P.expect (fun x => f x * m x) := by
      simp only [FiniteProduct.expect, mul_sub, Finset.sum_sub_distrib]
    _ = 1 - P.expect (fun x => m x ^ 2) := by
      rw [P.expect_const, hcross]
    _ = P.expect (fun x => (f x - m x) ^ 2) := by
      symm
      calc
        _ = P.expect (fun x => 1 - 2 * (f x * m x) + m x ^ 2) := by
          congr 1
          funext x
          rcases hf x with hx | hx <;> rw [hx] <;> ring
        _ = P.expect (fun _ => 1) -
            P.expect (fun x => 2 * (f x * m x)) +
            P.expect (fun x => m x ^ 2) := by
          simp only [FiniteProduct.expect, mul_add, mul_sub,
            Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = 1 - P.expect (fun x => m x ^ 2) := by
          rw [P.expect_const, P.expect_const_mul, hcross]
          ring
)

/-- Every absolute moment of a Boolean coordinate Laplacian with exponent
between one and two is at most that coordinate's influence.
[OD14, Ex. 8.10(b); Thm. 10.26, proof]
This gives the inequality needed for general finite coordinate laws.

**Proof sketch.** The first absolute moment and second moment of each
Boolean residual equal its conditional variance. Interpolate pointwise
between the first and second powers, then average. -/
private theorem product_laplacian_abs_moment_le_influence
    {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n)
    (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    P.expect (fun x => |P.laplacian i f x| ^ p) ≤ P.influence i f := (by
  classical
  have hpower (z : ℝ) : |z| ^ p ≤ (2 - p) * |z| + (p - 1) * z ^ 2 := by
    have hbern := rpow_one_add_le_one_add_mul_self
      (s := |z| - 1) (by linarith [abs_nonneg z])
      (by linarith : 0 ≤ p - 1) (by linarith : p - 1 ≤ 1)
    rw [show 1 + (|z| - 1) = |z| by ring] at hbern
    calc
      _ = |z| ^ (p - 1) * |z| := by
        simpa only [sub_add_cancel] using
          Real.rpow_add_one' (abs_nonneg z) (by linarith : p - 1 + 1 ≠ 0)
      _ ≤ (1 + (p - 1) * (|z| - 1)) * |z| :=
        mul_le_mul_of_nonneg_right hbern (abs_nonneg z)
      _ = (2 - p) * |z| + (p - 1) * z ^ 2 := by
        rw [show (1 + (p - 1) * (|z| - 1)) * |z| =
          (2 - p) * |z| + (p - 1) * |z| ^ 2 by ring, sq_abs]
  have hfirst : P.expect (fun x => |P.laplacian i f x|) = P.influence i f :=
    product_boolean_residual_abs_expect P f hf (Finset.univ.erase i)
  calc
    _ ≤ P.expect (fun x =>
        (2 - p) * |P.laplacian i f x| + (p - 1) * P.laplacian i f x ^ 2) := by
      unfold FiniteProduct.expect
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left (hpower _)
      unfold FiniteProduct.mass
      exact Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le
    _ = (2 - p) * P.expect (fun x => |P.laplacian i f x|) +
        (p - 1) * P.influence i f := by
      simp only [FiniteProduct.expect, FiniteProduct.influence, Finset.mul_sum,
        mul_add, Finset.sum_add_distrib, mul_left_comm]
    _ = P.influence i f := by rw [hfirst]; ring
)

/-- Conjugate-to-second norm contraction for a Boolean function's coordinate
Laplacian bounds its rate-weighted stable influence by a power of ordinary
influence. [OD14, Thm. 10.26, proof; Ex. 8.10(b)]
The explicit contraction hypothesis separates this argument from the choice
of hypercontractive radius, and includes the endpoint exponent two.

**Proof sketch.** Express the weighted stable influence as the squared noisy
second norm of the Laplacian. Square the contraction bound, then bound the
Laplacian's conjugate absolute moment by its influence and raise to the
nonnegative exponent two divided by the conjugate exponent. -/
private theorem product_stableInfluence_le_of_norm_noise_laplacian_le
    {n : ℕ} (P : FiniteProduct.{u} n) (q ρ : ℝ) (hq : 2 ≤ q) (hρ : 0 ≤ ρ)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n)
    (hcontract : P.norm 2 (P.noise (Real.sqrt ρ) (P.laplacian i f)) ≤
      P.norm (q / (q - 1)) (P.laplacian i f)) :
    ρ * P.stableInfluence ρ i f ≤ P.influence i f ^ (2 - 2 / q) :=
  (by
  classical
  let p : ℝ := q / (q - 1)
  have hp : 1 ≤ p ∧ p ≤ 2 := by
    dsimp only [p]
    constructor
    · apply (le_div_iff₀ (show 0 < q - 1 by linarith)).2
      linarith
    · apply (div_le_iff₀ (show 0 < q - 1 by linarith)).2
      linarith
  have hnorm : 0 ≤ P.norm 2 (P.noise (Real.sqrt ρ) (P.laplacian i f)) := by
    unfold FiniteProduct.norm
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hmoment : 0 ≤ P.expect (fun x => |P.laplacian i f x| ^ p) := by
    unfold FiniteProduct.expect
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (Real.rpow_nonneg (abs_nonneg _) _)
    unfold FiniteProduct.mass
    exact Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le
  calc
    ρ * P.stableInfluence ρ i f =
        P.norm 2 (P.noise (Real.sqrt ρ) (P.laplacian i f)) ^ 2 :=
      product_stableInfluence_eq_sq_norm_noise_laplacian P ρ hρ f i
    _ ≤ P.norm p (P.laplacian i f) ^ 2 :=
      pow_le_pow_left₀ hnorm hcontract 2
    _ = P.expect (fun x => |P.laplacian i f x| ^ p) ^ (2 / p) := by
      unfold FiniteProduct.norm
      rw [← Real.rpow_two, ← Real.rpow_mul hmoment]
      congr 1
      ring
    _ ≤ P.influence i f ^ (2 / p) :=
      Real.rpow_le_rpow hmoment
        (product_laplacian_abs_moment_le_influence P f hf i p hp.1 hp.2)
        (div_nonneg (by norm_num) (zero_le_one.trans hp.1))
    _ = P.influence i f ^ (2 - 2 / q) := by
      congr 1
      dsimp only [p]
      field_simp [ne_of_gt (show (0 : ℝ) < q by linarith),
        ne_of_gt (show (0 : ℝ) < q - 1 by linarith)]
)

/-- Stable influence, multiplied by `ρ`, is bounded by ordinary influence to the power
`2-2/q` on a finite product. [OD14, Thm. 10.26]

**Proof sketch.** Apply conjugate hypercontractivity to the coordinate Laplacian. The
Boolean range bounds its `q'`-moment by its expected conditional variance, giving the
ordinary influence on the right. -/
theorem product_stableInfluence {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 ≤ q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ (1 / (q - 1)) * lam ^ (1 - 2 / q))
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n) :
    ρ * P.stableInfluence ρ i f ≤ P.influence i f ^ (2 - 2 / q) := (by
  apply product_stableInfluence_le_of_norm_noise_laplacian_le P q ρ hq hρ f hf i
  rcases eq_or_lt_of_le hq with rfl | hq
  · norm_num at hbound ⊢
    exact ProductAux.noise_norm_two_le P (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
      (Real.sqrt_le_one.mpr hbound) (P.laplacian i f)
  · have hrate : Real.sqrt ρ ≤
        (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q) := by
      calc
        Real.sqrt ρ ≤ Real.sqrt ((1 / (q - 1)) * lam ^ (1 - 2 / q)) :=
          Real.sqrt_le_sqrt hbound
        _ = (1 / Real.sqrt (q - 1)) * lam ^ (1 / 2 - 1 / q) := by
          rw [Real.sqrt_mul (div_nonneg zero_le_one (by linarith)),
            Real.sqrt_div zero_le_one, Real.sqrt_one]
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlam.le]
          congr 1
          ring
    exact (product_hypercontractivity P lam q (Real.sqrt ρ) hlam hlam1 hπ hq
      (Real.sqrt_nonneg ρ) hrate (P.laplacian i f)).2
)

/-- At `q=4`, the weighted spectral influence is at most the ordinary influence to
the power `3/2`. [OD14, Thm. 10.26, equation (10.6)]

**Proof sketch.** Substitute `q=4` and `ρ=√lam/3` in the stable influence estimate and
expand the orthogonal-component formula. -/
theorem product_stableInfluence_four {n : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n) :
    (∑ S : Finset (Fin n), if i ∈ S then (Real.sqrt lam / 3) ^ S.card *
      P.expect (fun x => P.component S f x ^ 2) else 0) ≤
      P.influence i f ^ (3 / 2 : ℝ) := by
  let ρ : ℝ := Real.sqrt lam / 3
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hbound : ρ ≤ (1 / ((4 : ℝ) - 1)) * lam ^ (1 - 2 / (4 : ℝ)) := by
    norm_num [ρ, Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm]
  have h := product_stableInfluence P lam 4 ρ hlam hlam1 hπ
    (by norm_num) hρ hbound f hf i
  norm_num at h
  change (∑ S : Finset (Fin n), if i ∈ S then
    ρ ^ S.card * P.expect (fun x => P.component S f x ^ 2) else 0) ≤
    P.influence i f ^ (3 / 2 : ℝ)
  calc
    _ = ρ * P.stableInfluence ρ i f := by
      rw [FiniteProduct.stableInfluence, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hi : i ∈ S
      · simp only [hi, if_pos]
        have hcard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨i, hi⟩
        rw [← mul_assoc, mul_comm ρ (ρ ^ (S.card - 1)),
          ← pow_succ, Nat.sub_add_cancel hcard]
      · simp [hi]
    _ ≤ _ := h

/-- A nonconstant Boolean product function has a coordinate influence at least
`Ĩ⁻² (9/lam)^(-Ĩ)`, where `Ĩ` is total influence divided by variance.
[OD14, §10.3, KKL Isoperimetric Theorem for general product space domains]

**Proof sketch.** Sum equation (10.6) over coordinates. Normalize nonempty component
weights by the variance and use Jensen's inequality on the exponential of their degrees. -/
theorem product_kkl_isoperimetric {n : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (hvar : 0 < P.variance f) :
    ∃ i : Fin n, (P.totalInfluence f / P.variance f)⁻¹ ^ 2 *
      (9 / lam) ^ (-(P.totalInfluence f / P.variance f)) ≤ P.influence i f := (by
  classical
  let ρ : ℝ := Real.sqrt lam / 3
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hlam) (by norm_num)
  have hinfluence (i : Fin n) : 0 ≤ P.influence i f := by
    unfold FiniteProduct.influence FiniteProduct.expect
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le)
        (sq_nonneg _)
  have hVI : P.variance f ≤ P.totalInfluence f := by
    have h := ComparisonAux.variance_rpow_ratio_le_noisy_total P f hvar 1 zero_lt_one
    simpa only [Real.one_rpow, one_pow, mul_one,
      ← RandomizationAux.totalInfluence_eq_sum_card_components P f] using h
  have hI : 0 < P.totalInfluence f := hvar.trans_le hVI
  have hstable :
      (∑ S : Finset (Fin n), (S.card : ℝ) * ρ ^ S.card *
        P.expect (fun x => P.component S f x ^ 2)) ≤
        ∑ i : Fin n, P.influence i f ^ (3 / 2 : ℝ) := by
    calc
      _ = ∑ i : Fin n, ∑ S : Finset (Fin n), if i ∈ S then
          ρ ^ S.card * P.expect (fun x => P.component S f x ^ 2) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S _
        simp [Finset.sum_ite, nsmul_eq_mul, mul_assoc]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        product_stableInfluence_four P lam hlam
          (hlamhalf.trans (by norm_num)) hπ f hf i
  obtain ⟨i, hi⟩ := FiniteNorms.exists_sq_div_sum_le_of_sum_three_halves
    (fun i => P.influence i f) hinfluence hI
    (P.variance f * ρ ^ (P.totalInfluence f / P.variance f))
    (mul_nonneg hvar.le (Real.rpow_nonneg hρ.le _))
    ((ComparisonAux.variance_rpow_ratio_le_noisy_total P f hvar ρ hρ).trans hstable)
  refine ⟨i, ?_⟩
  rw [← ComparisonAux.kkl_coefficient_eq lam (P.variance f) (P.totalInfluence f) hlam hvar]
  exact hi
)

/-- The KKL influence lower bound on products loses only a factor `log(1/lam)` compared
with the uniform cube. The constant is independent of every product parameter.
[OD14, §10.3, KKL Isoperimetric Theorem, consequence]

**Proof sketch.** If normalized total influence is large, use the average influence;
otherwise use the exponential isoperimetric estimate to find a larger coordinate. -/
theorem product_kkl : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (lam : ℝ), 2 ≤ n → 0 < lam → lam ≤ 1 / 2 →
      P.AtomBound lam → ∀ f : P.Point → ℝ, P.IsBoolean f →
      ∃ i : Fin n, c / Real.log (1 / lam) * P.variance f *
        (Real.log (n : ℝ) / n) ≤ P.influence i f := (by
  classical
  refine ⟨(1 / 100 : ℝ), by norm_num, ?_⟩
  intro n P lam hn hlam hlamhalf hπ f hf
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  obtain ⟨hLhalf, hLD, hD⟩ :=
    ComparisonAux.kkl_log_parameters lam hlam hlamhalf
  have hL : 0 < Real.log (1 / lam) := by linarith
  have hx : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hinfluence (i : Fin n) : 0 ≤ P.influence i f := by
    unfold FiniteProduct.influence FiniteProduct.expect
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le)
        (sq_nonneg _)
  have htarget :
      (1 / 100 : ℝ) / Real.log (1 / lam) * P.variance f *
        (Real.log (n : ℝ) / n) =
      P.variance f * (Real.log (n : ℝ) /
        (100 * Real.log (1 / lam) * n)) := by
    field_simp [hL.ne', hnpos.ne']
  rw [htarget]
  by_cases hvar : 0 < P.variance f
  · have hVI : P.variance f ≤ P.totalInfluence f := by
      have h := ComparisonAux.variance_rpow_ratio_le_noisy_total P f hvar 1 zero_lt_one
      simpa only [Real.one_rpow, one_pow, mul_one,
        ← RandomizationAux.totalInfluence_eq_sum_card_components P f] using h
    have hI : 0 < P.totalInfluence f := hvar.trans_le hVI
    let t : ℝ := P.totalInfluence f / P.variance f
    have hscalar := ComparisonAux.kkl_scalar_dichotomy
      (Real.log (1 / lam)) (Real.log (9 / lam)) (Real.log (n : ℝ)) t
      (by linarith) (by linarith) hx (div_pos hI hvar)
    rw [Real.exp_log hnpos] at hscalar
    rcases hscalar with havg | hiso
    · -- The average influence supplies a coordinate in the first scalar branch.
      have hsum :
          (∑ _i : Fin n, P.totalInfluence f / (n : ℝ)) ≤
            ∑ i : Fin n, P.influence i f := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        change (n : ℝ) * (P.totalInfluence f / (n : ℝ)) ≤ P.totalInfluence f
        rw [mul_div_cancel₀ _ hnpos.ne']
      obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
        (show (Finset.univ : Finset (Fin n)).Nonempty from
          ⟨⟨0, by omega⟩, Finset.mem_univ _⟩) hsum
      refine ⟨i, ?_⟩
      calc
        P.variance f * (Real.log (n : ℝ) /
            (100 * Real.log (1 / lam) * n)) ≤ P.variance f * (t / n) :=
          mul_le_mul_of_nonneg_left havg hvar.le
        _ = P.totalInfluence f / n := by
          dsimp only [t]
          field_simp [hvar.ne', hnpos.ne']
        _ ≤ P.influence i f := hi
    · -- Boolean variance is at most one, so the isoperimetric coefficient suffices.
      obtain ⟨i, hi⟩ := product_kkl_isoperimetric P lam hlam hlamhalf hπ f hf hvar
      refine ⟨i, ?_⟩
      calc
        P.variance f * (Real.log (n : ℝ) /
            (100 * Real.log (1 / lam) * n)) ≤
            P.variance f * (t⁻¹ ^ 2 * Real.exp (-Real.log (9 / lam) * t)) :=
          mul_le_mul_of_nonneg_left hiso hvar.le
        _ ≤ t⁻¹ ^ 2 * Real.exp (-Real.log (9 / lam) * t) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (RandomizationAux.boolean_variance_le_one P f hf)
            (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
        _ ≤ P.influence i f := by
          simpa only [t,
            Real.rpow_def_of_pos (div_pos (by norm_num : (0 : ℝ) < 9) hlam),
            mul_neg, neg_mul] using hi
  · refine ⟨⟨0, by omega⟩, ?_⟩
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hvar)
      (div_nonneg hx (by positivity))).trans (hinfluence _)
)


/-- Every Boolean product function is `ε`-close to a Boolean junta on at most
`(1/lam)^(C I[f]/ε)` coordinates for an absolute constant `C`.
[OD14, §10.3, Friedgut's Junta Theorem for general product space domains]

**Proof sketch.** Discard high-degree components using total influence and Markov's
inequality. The stable-influence estimate removes low-degree components involving small
influences. Average over the remaining coordinates and round to a Boolean function. -/
theorem product_friedgut_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (lam : ℝ), 0 < lam → lam ≤ 1 / 2 →
      P.AtomBound lam → ∀ (f : P.Point → ℝ), P.IsBoolean f →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (J : Finset (Fin n)) (g : P.Point → ℝ), P.IsBoolean g ∧ P.DependsOn J g ∧
        (J.card : ℝ) ≤ (1 / lam) ^ (C * P.totalInfluence f / ε) ∧
        P.prob (fun x => f x ≠ g x) ≤ ε := (by
  classical
  refine ⟨(100 : ℝ), by norm_num, ?_⟩
  intro n P lam hlam hlamhalf hπ f hf ε hε hε1
  let I : ℝ := P.totalInfluence f
  have hinfluence (i : Fin n) : 0 ≤ P.influence i f := by
    unfold FiniteProduct.influence FiniteProduct.expect
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le)
        (sq_nonneg _)
  by_cases hsmall : I ≤ ε
  · -- Small total influence permits a constant Boolean approximation.
    have htail :
        (∑ S : Finset (Fin n), if 0 < S.card then
          P.expect (fun x => P.component S f x ^ 2) else 0) ≤ ε := by
      have h := RandomizationAux.component_tail_le_totalInfluence P f 0
      simp only [Nat.cast_zero, zero_add, one_mul] at h
      exact h.trans hsmall
    have hlow :
        (∑ S : Finset (Fin n), if S.card ≤ 0 ∧ ¬ S ⊆ ∅ then
          P.expect (fun x => P.component S f x ^ 2) else 0) ≤ 0 := by
      simp [Finset.card_eq_zero, Finset.subset_empty]
    obtain ⟨g, hg, hdep, hprob⟩ :=
      RandomizationAux.exists_boolean_junta_of_energy_bounds
        P f hf ∅ 0 ε 0 htail hlow
    refine ⟨∅, g, hg, hdep, ?_, ?_⟩
    · simpa only [Finset.card_empty, Nat.cast_zero] using
        Real.rpow_nonneg (div_nonneg zero_le_one hlam.le) (100 * I / ε)
    · simpa only [add_zero] using hprob
  · -- Choose the degree cutoff and the influence threshold.
    have hlarge : ε < I := lt_of_not_ge hsmall
    have hI : 0 < I := hε.trans hlarge
    let t : ℝ := I / ε
    have ht : 1 < t :=
      (lt_div_iff₀ hε).2 (by simpa only [one_mul] using hlarge)
    have ht0 : 0 ≤ t := by linarith
    have htI : t * ε = I := by
      dsimp only [t]
      exact div_mul_cancel₀ I hε.ne'
    let k : ℕ := Nat.ceil (2 * t)
    have hklower : 2 * t ≤ (k : ℝ) := Nat.le_ceil (2 * t)
    have hkupper : (k : ℝ) ≤ 3 * t := by
      have hceil : (k : ℝ) < 2 * t + 1 :=
        Nat.ceil_lt_add_one (show 0 ≤ 2 * t by positivity)
      linarith
    let ρ : ℝ := Real.sqrt lam / 3
    let τ : ℝ := (ε / (2 * I)) ^ 2 * ρ ^ (2 * k)
    obtain ⟨hρ, hρ1, hτ, hτroot, hcount⟩ :
        0 < ρ ∧ ρ ≤ 1 ∧ 0 < τ ∧
          Real.sqrt τ * I = (ε / 2) * ρ ^ k ∧
          I / τ = (4 * I ^ 3 / ε ^ 2) * (9 / lam) ^ k :=
      ComparisonAux.junta_threshold_parameters lam I ε hlam hlamhalf hI hε k
    let J : Finset (Fin n) := Finset.univ.filter (fun i => τ ≤ P.influence i f)
    have houtside (i : Fin n) (hi : i ∉ J) : P.influence i f ≤ τ :=
      le_of_lt (by simpa [J] using hi)
    -- High-degree and omitted low-degree energies each cost at most ε/2.
    have htail :
        (∑ S : Finset (Fin n), if k < S.card then
          P.expect (fun x => P.component S f x ^ 2) else 0) ≤ ε / 2 := by
      apply (mul_le_mul_iff_right₀ (show 0 < (k : ℝ) + 1 by positivity)).mp
      calc
        ((k : ℝ) + 1) *
            (∑ S : Finset (Fin n), if k < S.card then
              P.expect (fun x => P.component S f x ^ 2) else 0) ≤ I :=
          RandomizationAux.component_tail_le_totalInfluence P f k
        _ ≤ ((k : ℝ) + 1) * (ε / 2) := by
          have hscaled := mul_le_mul_of_nonneg_right hklower hε.le
          nlinarith [htI]
    have hlow :
        (∑ S : Finset (Fin n), if S.card ≤ k ∧ ¬ S ⊆ J then
          P.expect (fun x => P.component S f x ^ 2) else 0) ≤ ε / 2 := by
      have h := ComparisonAux.lowDegree_omission_le_of_stable_bound
        P f J k ρ τ hρ.le hρ1 hτ.le houtside
        (fun i => product_stableInfluence_four P lam hlam
          (hlamhalf.trans (by norm_num)) hπ f hf i)
      rw [hτroot] at h
      exact (mul_le_mul_iff_right₀ (pow_pos hρ k)).mp
        (by simpa only [mul_comm] using h)
    -- The selected influences control the number of retained coordinates.
    have hcard : (J.card : ℝ) ≤ I / τ := by
      apply (le_div_iff₀ hτ).2
      calc
        (J.card : ℝ) * τ ≤ ∑ i ∈ J, P.influence i f := by
          simpa only [nsmul_eq_mul] using
            Finset.card_nsmul_le_sum J (fun i => P.influence i f) τ
              (fun i hi => (Finset.mem_filter.mp hi).2)
        _ ≤ I :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
            (fun i _ _ => hinfluence i)
    have hsize : (J.card : ℝ) ≤ (1 / lam) ^ (100 * I / ε) := by
      calc
        (J.card : ℝ) ≤ I / τ := hcard
        _ = (4 * I ^ 3 / ε ^ 2) * (9 / lam) ^ k := hcount
        _ ≤ (1 / lam) ^ (100 * I / ε) :=
          ComparisonAux.junta_polynomial_absorption
            lam I ε hlam hlamhalf hε hε1 hlarge.le k hkupper
    obtain ⟨g, hg, hdep, hprob⟩ :=
      RandomizationAux.exists_boolean_junta_of_energy_bounds
        P f hf J k (ε / 2) (ε / 2) htail hlow
    refine ⟨J, g, hg, hdep, hsize, ?_⟩
    linarith
)


/-- The sharp comparison constant is asymptotic to `1/√lam` as `lam` decreases to zero.
The limit of the ratio expresses the source's asymptotic equivalence. [OD14, Thm. 10.22]

**Proof sketch.** Take logarithms of the ratio and simplify; the remaining terms tend to
zero using `lam log(lam) → 0`. Exponentiate. -/
theorem productNormComparisonConstant_asymptotic_zero :
    Filter.Tendsto (fun lam : ℝ => productNormComparisonConstant lam * Real.sqrt lam)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := (by
  have hid : Filter.Tendsto (fun lam : ℝ => lam)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog : Filter.Tendsto (fun lam : ℝ => Real.log lam * lam)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hexponent : Filter.Tendsto
      (fun lam : ℝ =>
        (Real.log (1 - lam) - 2 * (Real.log lam * lam)) / (2 * (1 - 2 * lam)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      ((((tendsto_const_nhds (x := (1 : ℝ))).sub hid).log
        (by norm_num : (1 : ℝ) - 0 ≠ 0)).sub (hlog.const_mul 2)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).sub
          (hid.const_mul 2)).const_mul 2)
        (by norm_num : (2 : ℝ) * (1 - 2 * 0) ≠ 0)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hexponent
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with lam hlam
  have hnum : 0 < 1 - lam := by linarith [hlam.2]
  have hgap : 1 - 2 * lam ≠ 0 := ne_of_gt (by linarith [hlam.2])
  symm
  rw [productNormComparisonConstant, if_neg hlam.2.ne, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (div_pos hnum hlam.1), Real.rpow_def_of_pos hlam.1,
    ← Real.exp_add, Real.log_div hnum.ne' hlam.1.ne']
  congr 1
  dsimp only
  field_simp [hgap, show 1 - lam * 2 ≠ 0 from ne_of_gt (by linarith [hlam.2])]
  ring
)

/-- The sharp comparison constant tends to `e` as the minimum atom mass tends to one half
from below. [OD14, Thm. 10.22]

**Proof sketch.** Take logarithms and evaluate the removable singularity of
`log((1-lam)/lam)/(2(1-2lam))` at one half by differentiation. Exponentiate its limit one. -/
theorem productNormComparisonConstant_tendsto_half :
    Filter.Tendsto productNormComparisonConstant
      (nhdsWithin (1 / 2) (Set.Ioo 0 (1 / 2))) (nhds (Real.exp 1)) := (by
  exact ComparisonAux.constant_tendsto_half
)

/-- Small-set expansion also holds up to the square of the sharp discrete radius.
[OD14, Thm. 10.25, parenthetical improvement]

**Proof sketch.** Express stability as the noisy second norm squared, use sharp product
hypercontractivity at `√ρ`, and evaluate the indicator's conjugate norm. -/
theorem product_smallSet_expansion_sharp {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam ^ 2)
    (A : P.Point → Prop) :
    P.stability ρ (P.indicator A) ≤ P.prob A ^ (2 - 2 / q) := (by
  have hrate : Real.sqrt ρ ≤ sharpDiscreteRadius q lam :=
    (Real.sqrt_le_left
      (SharpDiscrete.radius_pos_lt_one q lam hq hlam hlamhalf).1.le).2 hbound
  have hcontract :=
    (product_hypercontractivity_sharp P lam q (Real.sqrt ρ) hlam hlamhalf hπ hq
      (Real.sqrt_nonneg ρ) hrate (P.indicator A)).2
  have hnorm : 0 ≤ P.norm 2 (P.noise (Real.sqrt ρ) (P.indicator A)) := by
    unfold FiniteProduct.norm
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  calc
    P.stability ρ (P.indicator A) =
        P.norm 2 (P.noise (Real.sqrt ρ) (P.indicator A)) ^ 2 := by
      simpa only [Real.sq_sqrt hρ] using
        product_stability_sq_eq_norm_noise_sq P (Real.sqrt ρ) (P.indicator A)
    _ ≤ P.norm (q / (q - 1)) (P.indicator A) ^ 2 :=
      pow_le_pow_left₀ hnorm hcontract 2
    _ = P.prob A ^ (2 / (q / (q - 1))) :=
      product_indicator_norm_sq P (q / (q - 1))
        (div_pos (by linarith) (by linarith)) A
    _ = P.prob A ^ (2 - 2 / q) := by
      congr 1
      field_simp [ne_of_gt (show (0 : ℝ) < q by linarith),
        ne_of_gt (show (0 : ℝ) < q - 1 by linarith)]
)


/-- Stable influence has the same bound at the squared sharp discrete radius as at the
simpler radius. [OD14, Thm. 10.26, in the full setting of Thm. 10.25]

**Proof sketch.** Apply sharp conjugate hypercontractivity to the coordinate Laplacian
and bound its conjugate moment by the conditional-variance influence. -/
theorem product_stableInfluence_sharp {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam ^ 2)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n) :
    ρ * P.stableInfluence ρ i f ≤ P.influence i f ^ (2 - 2 / q) := (by
  have hrate : Real.sqrt ρ ≤ sharpDiscreteRadius q lam :=
    (Real.sqrt_le_left
      (SharpDiscrete.radius_pos_lt_one q lam hq hlam hlamhalf).1.le).2 hbound
  exact product_stableInfluence_le_of_norm_noise_laplacian_le P q ρ hq.le hρ f hf i
    (product_hypercontractivity_sharp P lam q (Real.sqrt ρ) hlam hlamhalf hπ hq
      (Real.sqrt_nonneg ρ) hrate (P.laplacian i f)).2
)

end BooleanAnalysis.Hypercontractivity
