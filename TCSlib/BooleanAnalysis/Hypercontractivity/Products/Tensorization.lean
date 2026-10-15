/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Norms

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tensorization of finite positive kernels

## Main definitions

The coordinate weights and joint kernels are explicit parameters.

## Main results

* `FiniteTensorization.pair_tensorization`: tensorization of coordinate pairing bounds.
* `FiniteTensorization.norm_tensorization`: tensorization of coordinate norm contractions.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Proposition 10.4 (proof), §9.4, Remark 9.20, and §10.1.
-/

open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity.FiniteTensorization

universe u

/-- Coordinate pairing bounds for nonnegative finite joint kernels tensorize to the
heterogeneous product at real exponents `p,r ≥ 1`.
[OD14, §9.4, Two-Function Hypercontractivity Induction Theorem; Rem. 9.20]
This technical formulation permits arbitrary nonnegative weights and joint kernels:
normalization is unnecessary because the coordinate estimates are explicit hypotheses.

**Proof sketch.** Split off the first coordinate. Apply its coordinate bound to
each pair of slices under the nonnegative remaining kernel, then apply the
induction hypothesis to the resulting slice norms. Cancel the nested norm powers
and reindex the finite sums.
For the empty product, bound the product by the product of absolute values. -/
theorem pair_tensorization {n : ℕ} (Ω : Fin n → Type u)
    [∀ i, Fintype (Ω i)] (w : ∀ i, Ω i → ℝ)
    (hw : ∀ i x, 0 ≤ w i x)
    (k : ∀ i, Ω i → Ω i → ℝ)
    (hk : ∀ i x y, 0 ≤ k i x y)
    (p r : ℝ) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hcoord : ∀ i (f g : Ω i → ℝ),
      (∑ x, ∑ y, k i x y * f x * g y) ≤
        (∑ x, w i x * |f x| ^ p) ^ (1 / p) *
          (∑ y, w i y * |g y| ^ r) ^ (1 / r))
    (f g : ((i : Fin n) → Ω i) → ℝ) :
    (∑ x : (i : Fin n) → Ω i,
      ∑ y : (i : Fin n) → Ω i,
        (∏ i, k i (x i) (y i)) * f x * g y) ≤
      (∑ x : (i : Fin n) → Ω i,
        (∏ i, w i (x i)) * |f x| ^ p) ^ (1 / p) *
      (∑ y : (i : Fin n) → Ω i,
        (∏ i, w i (y i)) * |g y| ^ r) ^ (1 / r) :=
  (by
  classical
  induction n with
  | zero =>
      simp only [Fin.prod_univ_zero, one_mul, Fintype.sum_unique, one_div]
      rw [Real.rpow_rpow_inv (abs_nonneg _) (by linarith),
        Real.rpow_rpow_inv (abs_nonneg _) (by linarith)]
      simpa only [abs_mul] using le_abs_self (f default * g default)
  | succ n ih =>
      have hsplit (H : ((i : Fin (n + 1)) → Ω i) → ℝ) :
          (∑ x, H x) =
            ∑ x : (i : Fin n) → Ω i.succ, ∑ a : Ω 0, H (Fin.cons a x) := by
        rw [← (Fin.consEquiv Ω).sum_comp H, Fintype.sum_prod_type,
          Finset.sum_comm]
        rfl
      have hmoment (s : ℝ) (hs : 1 ≤ s)
          (H : ((i : Fin (n + 1)) → Ω i) → ℝ) :
          (∑ x : (i : Fin n) → Ω i.succ,
            (∏ i, w i.succ (x i)) *
              |(∑ a : Ω 0, w 0 a * |H (Fin.cons a x)| ^ s) ^ (1 / s)| ^ s) =
            ∑ x : (i : Fin (n + 1)) → Ω i,
              (∏ i, w i (x i)) * |H x| ^ s := by
        rw [hsplit]
        simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        apply Finset.sum_congr rfl
        intro x hx
        have hnonneg :
            0 ≤ ∑ a : Ω 0, w 0 a * |H (Fin.cons a x)| ^ s :=
          Finset.sum_nonneg fun a _ =>
            mul_nonneg (hw 0 a) (Real.rpow_nonneg (abs_nonneg _) _)
        rw [abs_of_nonneg (Real.rpow_nonneg hnonneg _), one_div,
          Real.rpow_inv_rpow hnonneg (by linarith), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      let F : ((i : Fin n) → Ω i.succ) → ℝ :=
        fun x => (∑ a : Ω 0, w 0 a * |f (Fin.cons a x)| ^ p) ^ (1 / p)
      let G : ((i : Fin n) → Ω i.succ) → ℝ :=
        fun y => (∑ b : Ω 0, w 0 b * |g (Fin.cons b y)| ^ r) ^ (1 / r)
      calc
        (∑ x : (i : Fin (n + 1)) → Ω i,
          ∑ y : (i : Fin (n + 1)) → Ω i,
            (∏ i, k i (x i) (y i)) * f x * g y) =
            ∑ x : (i : Fin n) → Ω i.succ,
              ∑ y : (i : Fin n) → Ω i.succ,
                (∏ i, k i.succ (x i) (y i)) *
                  (∑ a : Ω 0, ∑ b : Ω 0,
                    k 0 a b * f (Fin.cons a x) * g (Fin.cons b y)) := by
          rw [hsplit]
          simp_rw [hsplit, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ ≤ ∑ x : (i : Fin n) → Ω i.succ,
            ∑ y : (i : Fin n) → Ω i.succ,
              (∏ i, k i.succ (x i) (y i)) * F x * G y := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          simpa only [F, G, mul_assoc] using
            mul_le_mul_of_nonneg_left
              (hcoord 0 (fun a => f (Fin.cons a x)) (fun b => g (Fin.cons b y)))
              (Finset.prod_nonneg fun i _ => hk i.succ (x i) (y i))
        _ ≤ (∑ x : (i : Fin n) → Ω i.succ,
              (∏ i, w i.succ (x i)) * |F x| ^ p) ^ (1 / p) *
            (∑ y : (i : Fin n) → Ω i.succ,
              (∏ i, w i.succ (y i)) * |G y| ^ r) ^ (1 / r) :=
          ih (Ω := fun i => Ω i.succ)
            (w := fun i => w i.succ) (hw := fun i => hw i.succ)
            (k := fun i => k i.succ) (hk := fun i => hk i.succ)
            (hcoord := fun i => hcoord i.succ) (f := F) (g := G)
        _ = (∑ x : (i : Fin (n + 1)) → Ω i,
              (∏ i, w i (x i)) * |f x| ^ p) ^ (1 / p) *
            (∑ y : (i : Fin (n + 1)) → Ω i,
              (∏ i, w i (y i)) * |g y| ^ r) ^ (1 / r) := by
          dsimp only [F, G]
          rw [hmoment p hp f, hmoment r hr g]
)

/-- Coordinate norm contractions for nonnegative finite kernels tensorize to
heterogeneous products, from a real exponent `p ≥ 1` to `q > 1`.
[OD14, Prop. 10.4 (proof); §9.4, Two-Function Hypercontractivity Induction Theorem;
Rem. 9.20; §10.1, Hypercontractivity Induction Theorem]
The kernel's first argument is its output coordinate and its second argument
is its input coordinate. This technical formulation permits arbitrary
nonnegative weights and kernels: normalization and `p ≤ q` are unnecessary
because the coordinate contractions are explicit hypotheses.

**Proof sketch.** Weighted Hölder turns each coordinate norm contraction into
a pairing bound with conjugate exponent `q/(q-1)`. Include the output weight
in each nonnegative joint kernel and apply the product pairing theorem.
Finite product factorization identifies the resulting pairing with the
product operator's weighted pairing. Weighted norm duality then recovers
its `q` norm bound. -/
theorem norm_tensorization {n : ℕ} (Ω : Fin n → Type u)
    [∀ i, Fintype (Ω i)] (w : ∀ i, Ω i → ℝ)
    (hw : ∀ i x, 0 ≤ w i x)
    (k : ∀ i, Ω i → Ω i → ℝ)
    (hk : ∀ i y x, 0 ≤ k i y x)
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 < q)
    (hcoord : ∀ i (f : Ω i → ℝ),
      (∑ y, w i y * |∑ x, k i y x * f x| ^ q) ^ (1 / q) ≤
        (∑ x, w i x * |f x| ^ p) ^ (1 / p))
    (f : ((i : Fin n) → Ω i) → ℝ) :
    (∑ y : (i : Fin n) → Ω i,
      (∏ i, w i (y i)) *
        |∑ x : (i : Fin n) → Ω i,
          (∏ i, k i (y i) (x i)) * f x| ^ q) ^ (1 / q) ≤
      (∑ x : (i : Fin n) → Ω i,
        (∏ i, w i (x i)) * |f x| ^ p) ^ (1 / p) :=
  (by
  classical
  have hconj : Real.HolderConjugate q (q / (q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  refine FiniteNorms.norm_le_of_pairing
    (fun (y : (i : Fin n) → Ω i) => ∏ i, w i (y i))
    (fun (y : (i : Fin n) → Ω i) =>
      Finset.prod_nonneg fun i _ => hw i (y i))
    q hq _ _ ?_ ?_
  · exact Real.rpow_nonneg
      (Finset.sum_nonneg fun x _ =>
        mul_nonneg (Finset.prod_nonneg fun i _ => hw i (x i))
          (Real.rpow_nonneg (abs_nonneg _) _)) _
  · intro g
    calc
      _ = ∑ x : (i : Fin n) → Ω i, ∑ y : (i : Fin n) → Ω i,
          (∏ i, w i (y i) * k i (y i) (x i)) * f x * g y := by
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]
        rw [Finset.sum_comm]
      _ ≤ _ := by
        refine pair_tensorization Ω w hw
          (fun i x y => w i y * k i y x)
          (fun i x y => mul_nonneg (hw i y) (hk i y x))
          p (q / (q - 1)) hp hconj.symm.lt.le ?_ f g
        intro i a b
        calc
          _ = ∑ y, w i y * (∑ x, k i y x * a x) * b y := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          _ ≤ (∑ y, w i y * |∑ x, k i y x * a x| ^ q) ^ (1 / q) *
              (∑ y, w i y * |b y| ^ (q / (q - 1))) ^ (1 / (q / (q - 1))) :=
            FiniteNorms.weighted_holder (w i) (hw i) hconj
              (fun y => ∑ x, k i y x * a x) b
          _ ≤ _ := mul_le_mul_of_nonneg_right (hcoord i a)
            (Real.rpow_nonneg
              (Finset.sum_nonneg fun y _ =>
                mul_nonneg (hw i y) (Real.rpow_nonneg (abs_nonneg _) _)) _)
)

end BooleanAnalysis.Hypercontractivity.FiniteTensorization
