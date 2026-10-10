/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Logic.Function.DependsOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite product spaces for hypercontractivity

## Main definitions

* `FiniteProduct`: a bundle of possibly different finite coordinate probability spaces.
* `FiniteProduct.condExp`, `component`, and `noise`: coordinate averaging, the orthogonal
  decomposition, and its noise multiplier.
* `FiniteProduct.influence`, `stableInfluence`, and `HasDegreeLE`: the basis-independent
  notions used in Chapter 10.

All definitions have concrete finite-sum bodies. Positive atom masses implement the book's
full-support convention; null outcomes can be removed before forming the bundle. We use
the orthogonal decomposition, so no arbitrary choice of a Fourier basis is necessary.

## Main results

* `FiniteProduct.mass_sum`: normalization of the product probability law.
* `FiniteProduct.expect_const`, `expect_sum_mul`: constants and finite linear combinations.
* `FiniteProduct.expect_swap_samples`: invariance under exchanging sample coordinates.
* `FiniteProduct.condExp_comp`, `condExp_selfAdjoint`: conditional-expectation algebra.

Further hypercontractivity statements are in `Products.General` and `Products.Applications`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §§8.1–8.3 and Chapters 9–10.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- The signed intersection energy is the quadratic subset sum associated with
inclusion-exclusion coefficients. -/
private noncomputable def signedIntersectionEnergy {α : Type*} [DecidableEq α]
    (S : Finset α) (g : Finset α → ℝ) : ℝ :=
  ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
    (-1 : ℝ) ^ (S.card - A.card) *
      (-1 : ℝ) ^ (S.card - B.card) * g (A ∩ B)

/-- Inserting a new element changes signed intersection energy by the difference
between the energy with that element inserted into each argument and the original energy.

**Proof sketch.** Split each inner subset according to whether it contains the new
element. The four cases have signs positive, negative, negative, positive. The first
three intersections omit the element; the last includes it. Combining the four terms
gives the stated difference. -/
private theorem signedIntersectionEnergy_insert {α : Type*} [DecidableEq α]
    (S : Finset α) (i : α) (hi : i ∉ S) (g : Finset α → ℝ) :
    signedIntersectionEnergy (insert i S) g =
      signedIntersectionEnergy S (fun T => g (insert i T)) -
        signedIntersectionEnergy S g := (by
  classical
  have hsign (A : Finset α) (hA : A ⊆ S) :
      (-1 : ℝ) ^ (S.card + 1 - A.card) =
        -(-1 : ℝ) ^ (S.card - A.card) := by
    have hcard := Finset.card_le_card hA
    rw [show S.card + 1 - A.card = S.card - A.card + 1 by omega, pow_succ]
    ring
  unfold signedIntersectionEnergy
  rw [Finset.sum_powerset_insert hi]
  simp_rw [Finset.sum_powerset_insert hi]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  have hAS := Finset.mem_powerset.mp hA
  have hBS := Finset.mem_powerset.mp hB
  have hiA : i ∉ A := Finset.notMem_mono hAS hi
  have hiB : i ∉ B := Finset.notMem_mono hBS hi
  simp only [Finset.card_insert_of_notMem hi,
    Finset.card_insert_of_notMem hiA, Finset.card_insert_of_notMem hiB,
    Nat.add_sub_add_right, hsign A hAS, hsign B hBS,
    Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA,
    ← Finset.insert_inter_distrib]
  ring
)


/-- Summing signed intersection energy over all subsets recovers the value on the
whole finite set.

**Proof sketch.** Induct on the finite set, allowing the function to vary. Split the
powerset into subsets omitting the new element and subsets containing it. The insertion
recurrence cancels the two original-energy sums, leaving the induction hypothesis for
the function with the new element inserted into each argument. -/
private theorem sum_powerset_signed_inter {α : Type*} [DecidableEq α]
    (U : Finset α) (g : Finset α → ℝ) :
    (∑ S ∈ U.powerset, signedIntersectionEnergy S g) = g U :=
      (by
  classical
  induction U using Finset.induction_on generalizing g with
  | empty =>
      simp [signedIntersectionEnergy]
  | @insert i U hi ih =>
      rw [Finset.sum_powerset_insert hi]
      calc
        _ = (∑ S ∈ U.powerset, signedIntersectionEnergy S g) +
            ∑ S ∈ U.powerset,
              (signedIntersectionEnergy S (fun T => g (insert i T)) -
                signedIntersectionEnergy S g) := by
          congr 1
          apply Finset.sum_congr rfl
          intro S hS
          exact signedIntersectionEnergy_insert S i
            (Finset.notMem_mono (Finset.mem_powerset.mp hS) hi) g
        _ = g (insert i U) := by
          simp only [Finset.sum_sub_distrib, ih]
          ring
)

/-- A finite product probability space with full-support coordinate laws, allowing different
outcome spaces in different coordinates. [OD14, §8.1; Ch. 10, General Hypercontractivity Theorem]
The real weights encode the finite probability mass functions directly. -/
structure FiniteProduct (n : ℕ) where
  Ω : Fin n → Type u
  fintypeΩ : ∀ i, Fintype (Ω i)
  weight : ∀ i, Ω i → ℝ
  weight_pos : ∀ i x, 0 < weight i x
  weight_sum : ∀ i, @Finset.sum (Ω i) ℝ _ (@Finset.univ (Ω i) (fintypeΩ i))
    (weight i) = 1

attribute [instance] FiniteProduct.fintypeΩ

namespace FiniteProduct

variable {n : ℕ} (P : FiniteProduct.{u} n)

/-- An outcome of the product is a choice of one outcome in every coordinate.
[OD14, §8.1] -/
abbrev Point := (i : Fin n) → P.Ω i

/-- The product probability mass of an outcome is the product of its coordinate masses.
[OD14, §8.1] -/
noncomputable def mass (x : P.Point) : ℝ := ∏ i, P.weight i (x i)

/-- Expectation under the product law is the probability-weighted finite sum.
[OD14, §8.1] -/
noncomputable def expect (f : P.Point → ℝ) : ℝ := ∑ x, P.mass x * f x

/-- The indicator of a subset of the product takes values zero and one. [OD14, Thm. 10.25] -/
noncomputable def indicator (A : P.Point → Prop) : P.Point → ℝ :=
  Set.indicator {x | A x} (fun _ => 1)

/-- Event probability under the product law is the expectation of its indicator.
[OD14, §8.1] -/
noncomputable def prob (A : P.Point → Prop) : ℝ :=
  P.expect (P.indicator A)

/-- The real `q`-norm is the `1/q` power of the absolute `q`-moment; its intended domain
is `q > 0`. [OD14, §8.1 and §10.2] -/
noncomputable def norm (q : ℝ) (f : P.Point → ℝ) : ℝ :=
  (P.expect (fun x => |f x| ^ q)) ^ (1 / q)

/-- Variance is the second moment about the product expectation. [OD14, §8.2] -/
noncomputable def variance (f : P.Point → ℝ) : ℝ :=
  P.expect (fun x => (f x - P.expect f) ^ 2)

/-- A function depends only on `S` if agreeing on `S` forces equal outputs.
[OD14, §8.3; §10.3, Friedgut's Junta Theorem]
This is Mathlib's coordinate-dependence predicate with a finite coordinate set. -/
abbrev DependsOn (S : Finset (Fin n)) (f : P.Point → ℝ) : Prop :=
  _root_.DependsOn f (S : Set (Fin n))

/-- Conditional expectation given the coordinates in `S` averages every other coordinate.
Using a full independent product sample avoids a choice of values outside `S`.
[OD14, §8.3, the operator `f ⊆ S`] -/
noncomputable def condExp (S : Finset (Fin n)) (f : P.Point → ℝ)
    (x : P.Point) : ℝ :=
  P.expect (fun y => f (fun i => if i ∈ S then x i else y i))

/-- The orthogonal component indexed by `S` is the inclusion-exclusion combination of
conditional expectations on its subsets. [OD14, §8.3, orthogonal decomposition formula] -/
noncomputable def component (S : Finset (Fin n)) (f : P.Point → ℝ)
    (x : P.Point) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * P.condExp T f x

/-- Degree at most `k` means that every orthogonal component above level `k` vanishes.
[OD14, §8.3; Thm. 10.21] -/
def HasDegreeLE (k : ℕ) (f : P.Point → ℝ) : Prop :=
  ∀ S : Finset (Fin n), k < S.card → ∀ x, P.component S f x = 0

/-- Projection onto degree at most `k` sums the corresponding orthogonal components.
[OD14, §8.3; §10.4] -/
noncomputable def lowDegree (k : ℕ) (f : P.Point → ℝ) (x : P.Point) : ℝ :=
  ∑ S : Finset (Fin n), if S.card ≤ k then P.component S f x else 0

/-- Noise multiplies the component indexed by `S` by `ρ ^ |S|`. The polynomial definition
also covers `ρ` outside `[0,1]`, as required in randomization. [OD14, §8.3; Def. 10.40] -/
noncomputable def noise (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) : ℝ :=
  ∑ S : Finset (Fin n), ρ ^ S.card * P.component S f x

/-- The coordinate Laplacian removes the conditional expectation over coordinate `i`.
[OD14, §8.3] -/
noncomputable def laplacian (i : Fin n) (f : P.Point → ℝ) (x : P.Point) : ℝ :=
  f x - P.condExp (Finset.univ.erase i) f x

/-- Coordinate influence is the expected squared coordinate Laplacian, equivalently the
expected conditional variance in that coordinate. [OD14, §8.3] -/
noncomputable def influence (i : Fin n) (f : P.Point → ℝ) : ℝ :=
  P.expect (fun x => (P.laplacian i f x) ^ 2)

/-- Total influence is the sum of coordinate influences. [OD14, §8.3] -/
noncomputable def totalInfluence (f : P.Point → ℝ) : ℝ := ∑ i, P.influence i f

/-- Stable influence uses weight `ρ ^ (|S|-1)` on the squared norm of each component
containing `i`. This definition includes `ρ = 0`. [OD14, §8.3; Thm. 10.26] -/
noncomputable def stableInfluence (ρ : ℝ) (i : Fin n) (f : P.Point → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then
    ρ ^ (S.card - 1) * P.expect (fun x => (P.component S f x) ^ 2) else 0

/-- Noise stability is the inner product of a function with its noisy version.
[OD14, §8.2; Thm. 10.25] -/
noncomputable def stability (ρ : ℝ) (f : P.Point → ℝ) : ℝ :=
  P.expect (fun x => f x * P.noise ρ f x)

/-- Every coordinate atom has mass at least `lam`. [OD14, General Hypercontractivity Theorem] -/
def AtomBound (lam : ℝ) : Prop := ∀ i x, lam ≤ P.weight i x

/-- A product function is Boolean-valued in the book's sign convention if every output is
either `-1` or `1`. [OD14, §10.3] -/
def IsBoolean (f : P.Point → ℝ) : Prop := ∀ x, f x = -1 ∨ f x = 1


/-- The product probability masses sum to one. [OD14, §8.1]

**Proof sketch.** Factor the finite sum of products as the product of the coordinate
weight sums. Each coordinate sum equals one. -/
theorem mass_sum (P : FiniteProduct.{u} n) :
    ∑ x : P.Point, P.mass x = 1 := (by
  classical
  simpa only [mass, P.weight_sum, Finset.prod_const_one] using
    (Fintype.prod_sum P.weight).symm
)


/-- Exchanging coordinates outside `S` between two independent product samples preserves
the expectation of every function of the pair. [OD14, §8.1]
This is the finite weighted-sum formulation of independent-coordinate exchangeability.

**Proof sketch.** The coordinate exchange is an involution on pairs of product samples.
It preserves the joint mass coordinatewise, so reindex the double finite sum by this
involution. -/
theorem expect_swap_samples (P : FiniteProduct.{u} n) (S : Finset (Fin n))
    (F : P.Point → P.Point → ℝ) :
    P.expect (fun x => P.expect (fun y =>
      F (fun i => if i ∈ S then x i else y i)
        (fun i => if i ∈ S then y i else x i))) =
      P.expect (fun x => P.expect (fun y => F x y)) := (by
  classical
  let swap : P.Point × P.Point → P.Point × P.Point := fun z =>
    (fun i => if i ∈ S then z.1 i else z.2 i,
     fun i => if i ∈ S then z.2 i else z.1 i)
  have hswap : Function.Involutive swap := by
    intro z
    apply Prod.ext <;> funext i <;>
      by_cases hi : i ∈ S <;> simp [swap, hi]
  let e : P.Point × P.Point ≃ P.Point × P.Point :=
    { toFun := swap
      invFun := swap
      left_inv := hswap
      right_inv := hswap }
  have hmass (z : P.Point × P.Point) :
      P.mass (e z).1 * P.mass (e z).2 = P.mass z.1 * P.mass z.2 := by
    simp only [mass, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [e, swap, hi, mul_comm]
  simp only [expect, Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have hreindex := e.sum_comp
    (fun z => P.mass z.1 * P.mass z.2 * F z.1 z.2)
  simp only [hmass] at hreindex
  simpa only [e, swap] using hreindex
)


/-- The expectation of a constant function equals that constant. [OD14, §8.1]

**Proof sketch.** Factor the constant out of the weighted finite sum and use that the
product probability masses sum to one. -/
theorem expect_const (P : FiniteProduct.{u} n) (c : ℝ) :
    P.expect (fun _ => c) = c := (by
  simp only [expect, ← Finset.sum_mul, P.mass_sum, one_mul]
)


/-- Expectation commutes with finite real linear combinations.

**Proof sketch.** Distribute the probability masses, interchange the finite sums,
and factor each coefficient out of its weighted sum. -/
theorem expect_sum_mul (P : FiniteProduct.{u} n) {α : Type*}
    (s : Finset α) (a : α → ℝ) (F : α → P.Point → ℝ) :
    P.expect (fun x => ∑ i ∈ s, a i * F i x) =
      ∑ i ∈ s, a i * P.expect (F i) := (by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]
)


/-- Successive conditional expectations onto coordinate sets `S` and `T` equal
conditional expectation onto their intersection. [OD14, §8.3]

**Proof sketch.** In the double average, the coordinates in the intersection remain
fixed. Exchange the sampled coordinates in `T \ S` between the two independent copies.
The integrand then uses a single sample outside the intersection; normalization removes
the unused sample. -/
theorem condExp_comp (P : FiniteProduct.{u} n) (S T : Finset (Fin n))
    (f : P.Point → ℝ) (x : P.Point) :
    P.condExp S (P.condExp T f) x = P.condExp (S ∩ T) f x :=
      (by
  classical
  calc
    P.condExp S (P.condExp T f) x =
        P.expect (fun y => P.expect (fun z =>
          f (fun i => if i ∈ S ∩ T then x i
            else if i ∈ T \ S then y i else z i))) := by
      unfold condExp
      congr 1
      funext y
      congr 1
      funext z
      congr 1
      funext i
      by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp [hiS, hiT]
    _ = P.expect (fun y => P.expect (fun _ =>
          f (fun i => if i ∈ S ∩ T then x i else y i))) :=
      P.expect_swap_samples (T \ S)
        (fun y _ => f (fun i => if i ∈ S ∩ T then x i else y i))
    _ = P.condExp (S ∩ T) f x := by
      simp only [P.expect_const, condExp]
)


/-- Conditional expectation onto a coordinate set is self-adjoint for the product
expectation pairing. [OD14, §8.3]

**Proof sketch.** Expand the conditional average using a second independent sample.
Exchange the complementary coordinates of the two samples, preserving their joint law,
and factor out the functions that are constant within each inner average. -/
theorem condExp_selfAdjoint (P : FiniteProduct.{u} n) (S : Finset (Fin n))
    (f g : P.Point → ℝ) :
    P.expect (fun x => f x * P.condExp S g x) =
      P.expect (fun x => P.condExp S f x * g x) := (by
  classical
  calc
    P.expect (fun x => f x * P.condExp S g x) =
        P.expect (fun x => P.expect (fun y =>
          f x * g (fun i => if i ∈ S then x i else y i))) := by
      simp only [condExp, expect, Finset.mul_sum, mul_left_comm]
    _ = P.expect (fun x => P.expect (fun y =>
          f (fun i => if i ∈ S then x i else y i) * g x)) := by
      rw [← P.expect_swap_samples S
        (fun x y => f x * g (fun i => if i ∈ S then x i else y i))]
      congr 1
      funext x
      congr 1
      funext y
      congr 1
      congr 1
      funext i
      by_cases hi : i ∈ S <;> simp [hi]
    _ = P.expect (fun x => P.condExp S f x * g x) := by
      simp only [condExp, expect, Finset.mul_sum, mul_left_comm, mul_comm]
)



/-- Expectation commutes with finite sums of real-valued functions.

**Proof sketch.** Specialize linearity for finite real linear combinations to coefficients
equal to one. -/
theorem expect_sum (P : FiniteProduct.{u} n) {α : Type*}
    (s : Finset α) (F : α → P.Point → ℝ) :
    P.expect (fun x => ∑ i ∈ s, F i x) =
      ∑ i ∈ s, P.expect (F i) := (by
  simpa only [one_mul] using P.expect_sum_mul s (fun _ => 1) F
)


/-- Multiplication by a real constant commutes with expectation.

**Proof sketch.** Factor the constant out of the probability-weighted finite sum. -/
theorem expect_const_mul (P : FiniteProduct.{u} n) (a : ℝ) (f : P.Point → ℝ) :
    P.expect (fun x => a * f x) = a * P.expect f := (by
  simp only [expect, Finset.mul_sum, mul_left_comm]
)


/-- The second moment equals the sum of the second moments of the orthogonal components.
[OD14, Thm. 8.35, uniqueness proof]
The same independence argument extends the book's homogeneous product to possibly
different finite coordinate laws.

**Proof sketch.** Expand each component square into signed pairings of conditional
averages. Self-adjointness and composition reduce each pairing to the conditional
average on the intersection of its coordinate sets. Signed subset-energy cancellation
leaves the conditional average on all coordinates, which equals the original function
by normalization. -/
theorem parseval (P : FiniteProduct.{u} n) (f : P.Point → ℝ) :
    P.expect (fun x => f x ^ 2) =
      ∑ S : Finset (Fin n), P.expect (fun x => P.component S f x ^ 2) :=
        (by
  classical
  have hpair (A B : Finset (Fin n)) :
      P.expect (fun x => P.condExp A f x * P.condExp B f x) =
        P.expect (fun x => f x * P.condExp (A ∩ B) f x) := by
    simpa only [P.condExp_comp, Finset.inter_comm, mul_comm] using
      P.condExp_selfAdjoint B (P.condExp A f) f
  have henergy (S : Finset (Fin n)) :
      P.expect (fun x => P.component S f x ^ 2) =
        signedIntersectionEnergy S
          (fun T => P.expect (fun x => f x * P.condExp T f x)) := by
    simp only [component, pow_two, Finset.sum_mul, Finset.mul_sum,
      signedIntersectionEnergy]
    rw [P.expect_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [P.expect_sum]
    apply Finset.sum_congr rfl
    intro B _
    calc
      _ = ((-1 : ℝ) ^ (S.card - A.card) *
            (-1 : ℝ) ^ (S.card - B.card)) *
          P.expect (fun x => P.condExp A f x * P.condExp B f x) := by
        rw [← P.expect_const_mul]
        congr 1
        funext x
        ring
      _ = _ := by rw [hpair]
  symm
  calc
    (∑ S : Finset (Fin n), P.expect (fun x => P.component S f x ^ 2)) =
        ∑ S : Finset (Fin n), signedIntersectionEnergy S
          (fun T => P.expect (fun x => f x * P.condExp T f x)) := by
      simp only [henergy]
    _ = P.expect (fun x => f x * P.condExp Finset.univ f x) := by
      simpa only [Finset.powerset_univ] using
        sum_powerset_signed_inter (Finset.univ : Finset (Fin n))
          (fun T => P.expect (fun x => f x * P.condExp T f x))
    _ = P.expect (fun x => f x ^ 2) := by
      simp only [condExp, Finset.mem_univ, ite_true, P.expect_const, pow_two]
)

end FiniteProduct
end BooleanAnalysis.Hypercontractivity
