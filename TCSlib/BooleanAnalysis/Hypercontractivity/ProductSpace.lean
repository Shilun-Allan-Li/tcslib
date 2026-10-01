/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
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

This file contains definitions only; statement skeletons are in `ProductHypercontractivity`
and `ProductApplications`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §§8.1–8.3 and Chapters 9–10.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u

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

end FiniteProduct
end BooleanAnalysis.Hypercontractivity
