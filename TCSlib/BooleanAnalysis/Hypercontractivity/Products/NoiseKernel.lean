/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Resampling kernels for finite product noise

## Main definitions

Conditional expectation and spectral noise are defined in `Products.Basic`.

## Main results

* `FiniteProduct.condExp_kernel`: conditional expectation as a resampling kernel.
* `FiniteProduct.noise_kernel`: spectral noise as a product resampling kernel.
* `FiniteProduct.noise_norm_one_le`: resampling noise contracts the absolute first moment.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Definitions 8.26–8.27, §8.3, and §10.1.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity.FiniteProduct

universe u

/-- Conditional expectation retains the selected input coordinates and independently
resamples the others: its finite kernel is the product of equality indicators and
coordinate weights. [OD14, §8.3]
The formula also permits heterogeneous finite coordinate laws.

**Proof sketch.** Express function evaluation as a sum of equality indicators and
exchange the two finite sums. Factor the sample sum coordinatewise. Normalization
removes the retained-coordinate averages, and each resampled-coordinate sum selects
its probability weight. -/
theorem condExp_kernel {n : ℕ} (P : FiniteProduct.{u} n)
    (S : Finset (Fin n)) (f : P.Point → ℝ) (x : P.Point) :
    P.condExp S f x = ∑ y : P.Point,
      (∏ i, if i ∈ S then (if x i = y i then 1 else 0)
        else P.weight i (y i)) * f y :=
  (by
  classical
  have hdelta (a : P.Point) :
      (∑ y : P.Point, (∏ i, if a i = y i then (1 : ℝ) else 0) * f y) = f a := by
    simp only [Fintype.prod_boole, ← funext_iff, ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq a f
  have hkernel (y : P.Point) :
      (∑ z : P.Point, P.mass z *
        (∏ i, if (if i ∈ S then x i else z i) = y i then (1 : ℝ) else 0)) =
        ∏ i, if i ∈ S then (if x i = y i then 1 else 0) else P.weight i (y i) := by
    simp only [mass, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (i : Fin n) (a : P.Ω i) =>
      P.weight i a * (if (if i ∈ S then x i else a) = y i then (1 : ℝ) else 0))]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hiS : i ∈ S
    · simp only [hiS, ite_true]
      rw [← Finset.sum_mul, P.weight_sum, one_mul]
    · simp [hiS, mul_ite]
  unfold condExp expect
  calc
    (∑ z : P.Point, P.mass z * f (fun i => if i ∈ S then x i else z i)) =
        ∑ z : P.Point, P.mass z *
          ∑ y : P.Point,
            (∏ i, if (if i ∈ S then x i else z i) = y i then (1 : ℝ) else 0) * f y := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hdelta]
    _ = ∑ y : P.Point,
        (∑ z : P.Point, P.mass z *
          (∏ i, if (if i ∈ S then x i else z i) = y i then (1 : ℝ) else 0)) *
        f y := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ y : P.Point,
        (∏ i, if i ∈ S then (if x i = y i then 1 else 0) else P.weight i (y i)) *
        f y := by
      simp only [hkernel]
)

/-- The inclusion-exclusion combination of product kernels replaces each selected
coordinate factor by its difference and leaves the other factors unchanged.

**Proof sketch.** Factor the coordinates outside the selected set out of the sum.
Expand the product of differences on that set with the finite product-add formula;
the negative factors give the inclusion-exclusion sign. -/
private theorem signed_product_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a b : ι → ℝ) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
      ∏ i, if i ∈ T then a i else b i) =
      ∏ i, if i ∈ S then a i - b i else b i :=
  (by
  classical
  conv_rhs =>
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff]
  simp only [sub_eq_add_neg, Finset.prod_add, Finset.prod_neg, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.mp hT
  rw [Finset.card_sdiff_of_subset hTS]
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff]
  rw [Finset.compl_eq_univ_sdiff,
    ← sdiff_sup_sdiff_cancel (Finset.subset_univ S) hTS,
    Finset.sup_eq_union,
    Finset.prod_union (Finset.disjoint_left.mpr fun i hi hj =>
      (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1)]
  simp only [Finset.compl_eq_univ_sdiff]
  ring
)

/-- The kernel of an orthogonal component uses centered equality indicators in
its coordinate set and sampling weights elsewhere. [OD14, §8.3]

**Proof sketch.** Expand the conditional averages in the inclusion-exclusion
formula into kernels, exchange the finite sums, and apply product expansion. -/
private theorem component_kernel {n : ℕ} (P : FiniteProduct.{u} n)
    (S : Finset (Fin n)) (f : P.Point → ℝ) (x : P.Point) :
    P.component S f x = ∑ y : P.Point,
      (∏ i, if i ∈ S then
        (if x i = y i then 1 else 0) - P.weight i (y i)
        else P.weight i (y i)) * f y :=
  (by
  classical
  unfold component
  simp_rw [P.condExp_kernel, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, signed_product_kernel]
)

/-- Spectral product noise equals the product of the coordinate resampling kernels,
at every real noise rate. [OD14, §8.3; §10.1]
The identity permits heterogeneous finite coordinate laws; positivity is not required
for this polynomial identity.

**Proof sketch.** Write each orthogonal component with its centered kernel. Expand
the product of a coordinate weight plus its centered indicator times the noise rate.
Each subset contributes precisely its spectral multiplier and component kernel. -/
theorem noise_kernel {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) :
    P.noise ρ f x = ∑ y : P.Point,
      (∏ i, (ρ * (if x i = y i then 1 else 0) +
        (1 - ρ) * P.weight i (y i))) * f y :=
  (by
  classical
  unfold noise
  simp_rw [component_kernel, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  apply congrArg (fun z : ℝ => z * f y)
  calc
    _ = ∏ i, (ρ * ((if x i = y i then 1 else 0) - P.weight i (y i)) +
        P.weight i (y i)) := by
      rw [Fintype.prod_add]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff]
      ring
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
)

/-- Noise at every rate between zero and one contracts the finite-product
`L¹` norm, including both endpoint rates and heterogeneous coordinate laws.
[OD14, Defs. 8.26–8.27; §8.3; §10.1]
This supplies the `p = q = 1` endpoint of product hypercontractivity.

**Proof sketch.** Express noise using its nonnegative resampling kernel.
The triangle inequality bounds each noisy absolute value by the kernel
average of the original absolute values. Exchange the finite sums in the
product expectation. Coordinate weight normalization shows that the kernel
preserves the product law, leaving the original absolute first moment. -/
theorem noise_norm_one_le {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : P.Point → ℝ) :
    P.norm 1 (P.noise ρ f) ≤ P.norm 1 f :=
  (by
  classical
  let K : P.Point → P.Point → ℝ := fun x y =>
    ∏ i, (ρ * (if x i = y i then 1 else 0) + (1 - ρ) * P.weight i (y i))
  have hK (x y : P.Point) : 0 ≤ K x y := by
    apply Finset.prod_nonneg
    intro i hi
    exact add_nonneg
      (mul_nonneg hρ (by split_ifs <;> norm_num))
      (mul_nonneg (sub_nonneg.mpr hρ1) (P.weight_pos i (y i)).le)
  have hstation (y : P.Point) :
      (∑ x : P.Point, P.mass x * K x y) = P.mass y := by
    dsimp only [mass, K]
    simp only [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum
      (fun (i : Fin n) (a : P.Ω i) =>
        P.weight i a *
          (ρ * (if a = y i then (1 : ℝ) else 0) +
            (1 - ρ) * P.weight i (y i)))]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_mul, P.weight_sum]
    ring
  have hpoint (x : P.Point) :
      |P.noise ρ f x| ≤ ∑ y : P.Point, K x y * |f y| := by
    rw [P.noise_kernel]
    change |∑ y : P.Point, K x y * f y| ≤ _
    calc
      |∑ y : P.Point, K x y * f y| ≤ ∑ y : P.Point, |K x y * f y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y : P.Point, K x y * |f y| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_mul, abs_of_nonneg (hK x y)]
  simp only [norm, expect, div_self (one_ne_zero : (1 : ℝ) ≠ 0), Real.rpow_one]
  calc
    (∑ x : P.Point, P.mass x * |P.noise ρ f x|) ≤
        ∑ x : P.Point, P.mass x * ∑ y : P.Point, K x y * |f y| := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x)
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
    _ = ∑ y : P.Point, (∑ x : P.Point, P.mass x * K x y) * |f y| := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ y : P.Point, P.mass y * |f y| := by
      simp only [hstation]
)

end BooleanAnalysis.Hypercontractivity.FiniteProduct
