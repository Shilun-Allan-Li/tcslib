/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Definitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Centered

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Orthogonal components and conditional moment bounds

## Main definitions

No new definitions are introduced. This file uses finite-product conditional
expectations and orthogonal components from `Products.Basic`.

## Main results

* `RandomizationAux.condExp_component`: conditional expectation retains exactly
  the components supported on the retained coordinates.
* `RandomizationAux.component_noise`: ordinary noise scales each component by
  its degree multiplier.
* `RandomizationAux.component_reconstruction`: the components sum to the original function.
* `RandomizationAux.weighted_abs_rpow_sum_le`: finite weighted Jensen inequality.
* `RandomizationAux.condExp_negative_moment_le`: conditional reflected-residual
  contraction from the scalar comparison.
* `RandomizationAux.condExp_moment_le`: conditional expectation contracts absolute moments.

The spectral identities permit arbitrary real noise rates. The moment comparisons
use explicit exponent and scalar-comparison hypotheses. All results apply to
heterogeneous finite coordinate laws.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §8.3, Theorem 8.35, Exercise 8.14,
  Lemmas 10.14 and 10.43, and Definition 10.40.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity.RandomizationAux

universe u

/-- Inclusion-exclusion cancels when its argument ignores an indexed coordinate.

**Proof sketch.** Choose an index outside the retained set and pair each subset omitting
it with the subset obtained by inserting it. Their intersections agree and signs oppose. -/
private theorem signed_intersection_zero {α : Type*} [DecidableEq α]
    (S J : Finset α) (g : Finset α → ℝ) (h : ¬ S ⊆ J) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g (T ∩ J)) = 0 :=
  (by
  classical
  obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp h
  conv_lhs => rw [← Finset.insert_erase hiS]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i S),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro T hT
  have hTS := Finset.mem_powerset.mp hT
  have hiT : i ∉ T := Finset.notMem_mono hTS (Finset.notMem_erase i S)
  have hcard := Finset.card_le_card hTS
  simp only [Finset.card_insert_of_notMem (Finset.notMem_erase i S),
    Finset.card_insert_of_notMem hiT, Nat.add_sub_add_right,
    Finset.insert_inter_of_notMem hiJ]
  rw [show (S.erase i).card + 1 - T.card =
    (S.erase i).card - T.card + 1 by omega, pow_succ]
  ring
)

/-- Conditional expectation onto `J` retains an orthogonal component indexed by `S`
exactly when every coordinate of `S` belongs to `J`. [OD14, §8.3]

**Proof sketch.** Expand the component's inclusion-exclusion formula and commute its
finite linear combination with conditional expectation. Composition replaces each
subset by its intersection with `J`. If `S` lies in `J`, all intersections are unchanged;
otherwise the alternating terms cancel along a coordinate of `S` outside `J`. -/
theorem condExp_component {n : ℕ} (P : FiniteProduct.{u} n)
    (J S : Finset (Fin n)) (f : P.Point → ℝ) (x : P.Point) :
    P.condExp J (P.component S f) x =
      if S ⊆ J then P.component S f x else 0 :=
  (by
  classical
  calc
    P.condExp J (P.component S f) x =
        ∑ T ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - T.card) * P.condExp (T ∩ J) f x := by
      change P.expect (fun y => ∑ T ∈ S.powerset,
        (-1 : ℝ) ^ (S.card - T.card) *
          P.condExp T f (fun i => if i ∈ J then x i else y i)) = _
      rw [P.expect_sum_mul]
      change (∑ T ∈ S.powerset,
        (-1 : ℝ) ^ (S.card - T.card) *
          P.condExp J (P.condExp T f) x) = _
      simp only [P.condExp_comp, Finset.inter_comm]
    _ = _ := by
      split_ifs with h
      · unfold FiniteProduct.component
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.inter_eq_left.mpr ((Finset.mem_powerset.mp hT).trans h)]
      · exact signed_intersection_zero S J (fun T => P.condExp T f x) h
)

/-- Summing the inclusion-exclusion transforms over all subsets of `U` recovers
the original value `g U`. [OD14, Thm. 8.35, property (5); Ex. 8.14]

**Proof sketch.** Induct on the finite set. Split both subset sums according to
whether they contain the new coordinate. Opposite signs cancel the original
transforms, leaving the induction hypothesis with that coordinate inserted. -/
theorem sum_powerset_signed_sum {α : Type*} [DecidableEq α]
    (U : Finset α) (g : Finset α → ℝ) :
    (∑ S ∈ U.powerset,
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T) =
        g U := (by
  classical
  induction U using Finset.induction_on generalizing g with
  | empty =>
      simp
  | @insert i U hi ih =>
      rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib]
      calc
        _ = ∑ S ∈ U.powerset,
            ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ (S.card - T.card) * g (insert i T) := by
          apply Finset.sum_congr rfl
          intro S hS
          have hiS : i ∉ S :=
            Finset.notMem_mono (Finset.mem_powerset.mp hS) hi
          rw [Finset.sum_powerset_insert hiS]
          simp only [Finset.card_insert_of_notMem hiS, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro T hT
          have hiT : i ∉ T :=
            Finset.notMem_mono (Finset.mem_powerset.mp hT) hiS
          have hcard := Finset.card_le_card (Finset.mem_powerset.mp hT)
          simp only [Finset.card_insert_of_notMem hiT, Nat.add_sub_add_right]
          rw [show S.card + 1 - T.card = S.card - T.card + 1 by omega, pow_succ]
          ring
        _ = g (insert i U) := ih (fun T => g (insert i T))
)

/-- Component projection onto `S` retains the component indexed by `T` exactly when
`S = T`, and otherwise gives zero. [OD14, Thm. 8.35; §8.3]
This pointwise identity extends to heterogeneous finite coordinate laws.

**Proof sketch.** Expand the outer inclusion-exclusion sum and use the conditional
expectation rule for a component. Equal indices leave only the full-set term.
Unequal indices either leave no retained subset or cancel in pairs along a
coordinate present in the outer index but absent from the inner index. -/
theorem component_component {n : ℕ} (P : FiniteProduct.{u} n)
    (S T : Finset (Fin n)) (f : P.Point → ℝ) (x : P.Point) :
    P.component S (P.component T f) x =
      if S = T then P.component S f x else 0 := (by
  classical
  change (∑ U ∈ S.powerset,
    (-1 : ℝ) ^ (S.card - U.card) * P.condExp U (P.component T f) x) = _
  simp_rw [condExp_component]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl, Finset.sum_eq_single S]
    · simp
    · intro U hU hUS
      have hSU : ¬ S ⊆ U := fun h =>
        hUS (Finset.Subset.antisymm (Finset.mem_powerset.mp hU) h)
      simp [hSU]
    · simp
  · rw [if_neg hST]
    by_cases hsub : S ⊆ T
    · apply Finset.sum_eq_zero
      intro U hU
      have hTU : ¬ T ⊆ U := fun h =>
        hST (Finset.Subset.antisymm hsub (h.trans (Finset.mem_powerset.mp hU)))
      simp [hTU]
    · simpa only [Finset.subset_inter_iff, Finset.Subset.refl, and_true] using
        (signed_intersection_zero S T
          (fun U => if T ⊆ U then P.component T f x else 0) hsub)
)



/-- At every real noise rate, the component indexed by `S` of the noised function
is `ρ ^ |S|` times its original component. [OD14, Ex. 8.18; Def. 10.40]
The polynomial identity holds for all real rates and heterogeneous finite coordinate laws.

**Proof sketch.** Commute component projection with the finite noise expansion using
linearity of conditional expectation. Projection kills every component except the
one indexed by `S`, leaving its noise multiplier. -/
theorem component_noise {n : ℕ} (P : FiniteProduct.{u} n)
    (S : Finset (Fin n)) (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) :
    P.component S (P.noise ρ f) x =
      ρ ^ S.card * P.component S f x := (by
  classical
  calc
    P.component S (P.noise ρ f) x =
        ∑ T : Finset (Fin n), ρ ^ T.card * P.component S (P.component T f) x := by
      change (∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) *
        P.expect (fun y => ∑ T : Finset (Fin n),
          ρ ^ T.card * P.component T f
            (fun i => if i ∈ U then x i else y i))) = _
      simp_rw [P.expect_sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      change _ = ∑ T : Finset (Fin n), ρ ^ T.card *
        ∑ U ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - U.card) * P.condExp U (P.component T f) x
      simp only [FiniteProduct.condExp, Finset.mul_sum, mul_left_comm]
    _ = _ := by simp [component_component, mul_ite]
)


/-- The orthogonal components of a finite-product function sum pointwise to
the original function. [OD14, Thm. 8.35, property (5); Ex. 8.14]
The identity also holds for heterogeneous finite coordinate laws.

**Proof sketch.** Expand each component by inclusion-exclusion. Summing over
all subsets cancels the alternating terms and leaves conditional expectation
onto the full coordinate set. This conditional expectation fixes the function,
since the independent sample contributes only its total probability mass one. -/
theorem component_reconstruction {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) :
    (∑ S : Finset (Fin n), P.component S f x) = f x :=
  (by
  classical
  calc
    (∑ S : Finset (Fin n), P.component S f x) =
        P.condExp Finset.univ f x := by
      simpa only [FiniteProduct.component, Finset.powerset_univ] using
        (sum_powerset_signed_sum (Finset.univ : Finset (Fin n))
          (fun T => P.condExp T f x))
    _ = f x := by
      simp only [FiniteProduct.condExp, Finset.mem_univ, ite_true, P.expect_const]
)

/-- The absolute `q`-power of a probability-weighted finite average is bounded by
the average of the absolute `q`-powers when `q≥1`. [OD14, Lem. 10.14, proof]
This is the finite weighted form of Jensen's inequality used in that proof.

**Proof sketch.** Bound the absolute value of the weighted sum by the weighted sum
of absolute values. Monotonicity of the nonnegative `q`-power and the weighted
power-mean inequality then give the bound. -/
theorem weighted_abs_rpow_sum_le {α : Type*}
    (s : Finset α) (w F : α → ℝ) (q : ℝ)
    (hw0 : ∀ a ∈ s, 0 ≤ w a) (hw1 : ∑ a ∈ s, w a = 1) (hq : 1 ≤ q) :
    |∑ a ∈ s, w a * F a| ^ q ≤ ∑ a ∈ s, w a * |F a| ^ q :=
  (by
  calc
    |∑ a ∈ s, w a * F a| ^ q ≤ (∑ a ∈ s, w a * |F a|) ^ q := by
      apply Real.rpow_le_rpow (abs_nonneg _) ?_ (zero_le_one.trans hq)
      calc
        |∑ a ∈ s, w a * F a| ≤ ∑ a ∈ s, |w a * F a| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a ∈ s, w a * |F a| := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [abs_mul, abs_of_nonneg (hw0 a ha)]
    _ ≤ ∑ a ∈ s, w a * |F a| ^ q :=
      Real.rpow_arith_mean_le_arith_mean_rpow s w (fun a => |F a|)
        hw0 hw1 (fun a _ => abs_nonneg (F a)) hq
)

/-- Reflecting a finite probability-weighted family around its mean with rate `c`
does not increase its absolute `q`-moment whenever the normalized scalar contraction
holds. [OD14, Lem. 10.43, proof]
This finite-sum reformulation assumes the scalar comparison explicitly and therefore
permits every positive exponent for which that comparison is available.

**Proof sketch.** Apply the affine scalar comparison to each value minus the weighted
mean. Sum with the nonnegative weights. The centered values have weighted sum zero,
so the linear correction vanishes. -/
private theorem weighted_negative_moment_le {α : Type*}
    (s : Finset α) (w F : α → ℝ) (q : ℝ) (hq : 0 < q)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hscalar : ∀ z : ℝ, |1 - c * z| ^ q ≤
      |1 + z| ^ q - q * (1 + c) * z)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) :
    let a : ℝ := ∑ i ∈ s, w i * F i
    (∑ i ∈ s, w i * |a - c * (F i - a)| ^ q) ≤
      ∑ i ∈ s, w i * |F i| ^ q :=
  (by
  classical
  let a : ℝ := ∑ i ∈ s, w i * F i
  let k : ℝ := q * (1 + c) * |a| ^ q / a
  change (∑ i ∈ s, w i * |a - c * (F i - a)| ^ q) ≤
    ∑ i ∈ s, w i * |F i| ^ q
  have hcenter : ∑ i ∈ s, w i * (F i - a) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    exact sub_self a
  calc
    _ ≤ ∑ i ∈ s, w i * (|F i| ^ q - k * (F i - a)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw0 i hi)
      simpa [k] using
        CenteredContraction.scalar_affine q hq c hc0 hc1 hscalar a (F i - a)
    _ = ∑ i ∈ s, (w i * |F i| ^ q - k * (w i * (F i - a))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i ∈ s, w i * |F i| ^ q) -
        k * (∑ i ∈ s, w i * (F i - a)) := by
      rw [Finset.sum_sub_distrib]
      exact congrArg (fun t : ℝ => (∑ i ∈ s, w i * |F i| ^ q) - t)
        (Finset.mul_sum s (fun i => w i * (F i - a)) k).symm
    _ = ∑ i ∈ s, w i * |F i| ^ q := by
      rw [hcenter, mul_zero, sub_zero]
)

set_option maxHeartbeats 200000 in
/-- Reflecting a function's residual around its conditional mean with rate `c`
does not increase its absolute `q`-moment whenever the normalized scalar contraction
holds. [OD14, Lem. 10.43, proof; Def. 10.40]
This finite-product reformulation allows conditioning on any coordinate set and
assumes the scalar comparison explicitly.

**Proof sketch.** Fix the retained coordinates and apply the finite weighted
contraction to the complementary-coordinate fiber. Its mean is the conditional
expectation, which remains unchanged when complementary coordinates are resampled.
Average over the retained input and exchange coordinates between the two independent
samples; the resulting double averages equal the original moments. -/
theorem condExp_negative_moment_le {n : ℕ} (P : FiniteProduct.{u} n)
    (J : Finset (Fin n)) (f : P.Point → ℝ) (q : ℝ) (hq : 0 < q)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hscalar : ∀ z : ℝ, |1 - c * z| ^ q ≤
      |1 + z| ^ q - q * (1 + c) * z) :
    P.expect (fun x =>
      |P.condExp J f x - c * (f x - P.condExp J f x)| ^ q) ≤
      P.expect (fun x => |f x| ^ q) :=
  (by
  classical
  have hmass (x : P.Point) : 0 ≤ P.mass x :=
    Finset.prod_nonneg (fun i _ => (P.weight_pos i (x i)).le)
  have hmean (x y : P.Point) :
      P.condExp J f (fun i => if i ∈ J then x i else y i) =
        P.condExp J f x := by
    unfold FiniteProduct.condExp
    refine congrArg P.expect (funext fun z => ?_)
    refine congrArg f (funext fun i => ?_)
    by_cases hi : i ∈ J
    · simp only [if_pos hi]
    · simp only [if_neg hi]
  have havg (g : P.Point → ℝ) :
      P.expect (fun x => P.expect (fun y =>
        g (fun i => if i ∈ J then x i else y i))) = P.expect g := by
    calc
      _ = P.expect (fun x => P.expect (fun _ => g x)) :=
        P.expect_swap_samples J (fun x _ => g x)
      _ = P.expect g := by
        refine congrArg P.expect (funext fun x => ?_)
        exact P.expect_const (g x)
  calc
    _ = P.expect (fun x => P.expect (fun y =>
        |P.condExp J f (fun i => if i ∈ J then x i else y i) -
          c * (f (fun i => if i ∈ J then x i else y i) -
            P.condExp J f (fun i => if i ∈ J then x i else y i))| ^ q)) :=
      (havg (fun x =>
        |P.condExp J f x - c * (f x - P.condExp J f x)| ^ q)).symm
    _ = P.expect (fun x => P.expect (fun y =>
        |P.condExp J f x -
          c * (f (fun i => if i ∈ J then x i else y i) -
            P.condExp J f x)| ^ q)) := by
      refine congrArg P.expect (funext fun x => ?_)
      refine congrArg P.expect (funext fun y => ?_)
      rw [hmean x y]
    _ ≤ P.expect (fun x => P.expect (fun y =>
        |f (fun i => if i ∈ J then x i else y i)| ^ q)) := by
      unfold FiniteProduct.expect
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hmass x)
      simpa only [FiniteProduct.condExp, FiniteProduct.expect] using
        weighted_negative_moment_le Finset.univ P.mass
          (fun y => f (fun i => if i ∈ J then x i else y i))
          q hq c hc0 hc1 hscalar (fun y _ => hmass y) P.mass_sum
    _ = P.expect (fun x => |f x| ^ q) :=
      havg (fun x => |f x| ^ q)
)

/-- Conditional expectation onto any coordinate set does not increase the absolute
`q`-moment for `q≥1`. [OD14, §8.3; Lem. 10.14, proof]

**Proof sketch.** Apply finite weighted Jensen to the independent sample defining
each conditional average. Average over the original input and exchange complementary
coordinates between the two independent product samples. This preserves their joint
law and recovers the original absolute `q`-moment. -/
theorem condExp_moment_le {n : ℕ} (P : FiniteProduct.{u} n)
    (J : Finset (Fin n)) (f : P.Point → ℝ) (q : ℝ) (hq : 1 ≤ q) :
    P.expect (fun x => |P.condExp J f x| ^ q) ≤
      P.expect (fun x => |f x| ^ q) :=
  (by
  classical
  have hmass (x : P.Point) : 0 ≤ P.mass x :=
    Finset.prod_nonneg (fun i _ => (P.weight_pos i (x i)).le)
  calc
    P.expect (fun x => |P.condExp J f x| ^ q) ≤
        P.expect (fun x => P.expect (fun y =>
          |f (fun i => if i ∈ J then x i else y i)| ^ q)) := by
      unfold FiniteProduct.expect
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hmass x)
      exact weighted_abs_rpow_sum_le Finset.univ P.mass
        (fun y => f (fun i => if i ∈ J then x i else y i)) q
        (fun y _ => hmass y) P.mass_sum hq
    _ = P.expect (fun x => |f x| ^ q) := by
      rw [P.expect_swap_samples J (fun x _ => |f x| ^ q)]
      simp only [P.expect_const]
)

end BooleanAnalysis.Hypercontractivity.RandomizationAux
