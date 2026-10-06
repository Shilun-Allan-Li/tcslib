import TCSlib.BooleanAnalysis.Hypercontractivity.ProductSpace
import TCSlib.BooleanAnalysis.Hypercontractivity.CubeBasic
import TCSlib.BooleanAnalysis.Switching
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Monotone.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Boosters, pseudo-juntas, and sharp-threshold definitions

## Main definitions

* `IsBooster`: a restriction increasing or decreasing the mean by a signed amount.
* `IsPseudoJunta`: dependence on observations selected by local tests of bounded expected size.
* `thresholdCurve`, `IsIncreasing`, `IsTransitiveSymmetric`: biased threshold data.
* `IsGraphProperty`, `IsMonotoneDNF`: the syntax used in Friedgut's graph theorem.

## Main results

This definitions layer contains no theorem statements.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §8.4, Theorem 10.29, Definition 10.46, §10.5 and Exercise 10.39.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- A restriction boosts the mean by at least the nonzero signed amount in its indicated
direction. The full input represents its restriction to `T`; outside values are ignored.
The definition extends the source's Boolean-function formula to real-valued functions.
[OD14, Def. 10.46] -/
def IsBooster {n : ℕ} (P : FiniteProduct.{u} n) (f : P.Point → ℝ)
    (T : Finset (Fin n)) (x : P.Point) (τ : ℝ) : Prop :=
  (0 < τ ∧ P.expect f + τ ≤ P.condExp T f x) ∨
    (τ < 0 ∧ P.condExp T f x ≤ P.expect f + τ)

/-- Triggered coordinates are the union of the domains of the local tests accepting the
input. [OD14, Ex. 10.39] -/
noncomputable def pseudoJuntaCoordinates {n m : ℕ} {P : FiniteProduct.{u} n}
    (J : Fin m → Finset (Fin n)) (trigger : Fin m → P.Point → Bool)
    (x : P.Point) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ j, trigger j x = true ∧ i ∈ J j)

/-- A pseudo-junta observation records values on triggered coordinates and masks the
others with `none`, thereby also recording the exposed set. [OD14, Ex. 10.39] -/
noncomputable def pseudoJuntaObservation {n m : ℕ} (P : FiniteProduct.{u} n)
    (J : Fin m → Finset (Fin n)) (trigger : Fin m → P.Point → Bool)
    (x : P.Point) : (i : Fin n) → Option (P.Ω i) :=
  fun i => if i ∈ pseudoJuntaCoordinates J trigger x then some (x i) else none

/-- A `K`-pseudo-junta is determined by locally triggered observations exposing at most
`K` coordinates in expectation. Every test depends only on its declared domain.
This specializes the source's arbitrary output codomain to real-valued functions.
[OD14, Ex. 10.39 and §10.5, Hatami's Theorem] -/
def IsPseudoJunta {n : ℕ} (P : FiniteProduct.{u} n) (h : P.Point → ℝ) (K : ℝ) : Prop :=
  ∃ (m : ℕ) (J : Fin m → Finset (Fin n)) (trigger : Fin m → P.Point → Bool)
    (g : ((i : Fin n) → Option (P.Ω i)) → ℝ),
    (∀ j, _root_.DependsOn (trigger j) (J j : Set (Fin n))) ∧
    (∀ x, h x = g (pseudoJuntaObservation P J trigger x)) ∧
    P.expect (fun x => ((pseudoJuntaCoordinates J trigger x).card : ℝ)) ≤ K

/-- For `0 ≤ p ≤ 1`, biased cube probability samples true independently with probability
`p` per coordinate. True represents the sign `-1` in the book's convention.
The formula extends polynomially to all real `p`; outside `[0,1]` it need not be a probability.
[OD14, §10.3, threshold setup] -/
noncomputable def biasedProbability {n : ℕ} (p : ℝ) (A : BoolCube n → Prop) : ℝ :=
  ∑ x : BoolCube n, (∏ i : Fin n, if x i then p else 1 - p) * cubeIndicator A x

/-- For `p ∈ [0,1]`, the threshold curve is the biased probability of a true output.
Outside that interval this definition is its polynomial extension. [OD14, Thm. 10.29] -/
noncomputable def thresholdCurve {n : ℕ} (f : BoolCube n → Bool) (p : ℝ) : ℝ :=
  biasedProbability p (fun x => f x = true)

/-- An increasing Boolean function remains true when false input coordinates become true.
[OD14, Thm. 10.29 and §10.5] This is monotonicity for the pointwise Boolean order. -/
abbrev IsIncreasing {n : ℕ} (f : BoolCube n → Bool) : Prop :=
  Monotone f

/-- Transitive symmetry means each coordinate can be moved to any other by a permutation
preserving the function. [OD14, Thm. 10.29] -/
def IsTransitiveSymmetric {n : ℕ} (f : BoolCube n → Bool) : Prop :=
  ∀ i j : Fin n, ∃ σ : Equiv.Perm (Fin n), σ i = j ∧
    ∀ x : BoolCube n, f (fun k => x (σ k)) = f x

/-- Biased total influence is `4p(1-p)` times the sum of pivotal probabilities, matching
the conditional-variance influence of the sign-valued function. [OD14, §8.4 and §10.3] -/
noncomputable def biasedTotalInfluence {n : ℕ} (p : ℝ) (f : BoolCube n → Bool) : ℝ :=
  4 * p * (1 - p) * ∑ i : Fin n,
    biasedProbability p (fun x =>
      f (Function.update x i false) ≠ f (Function.update x i true))

/-- An edge of a labeled simple graph is a two-element vertex set.
[OD14, §10.5, Friedgut's Sharp Threshold Theorem] -/
abbrev GraphEdge (v : ℕ) := {S : Finset (Fin v) // S.card = 2}

/-- A cube function on all graph edges is a graph property if vertex relabelings preserve
its value. The edge bijection excludes loops and repeated coordinates.
[OD14, §10.5, Friedgut's Sharp Threshold Theorem] -/
def IsGraphProperty {v n : ℕ} (edge : Fin n ≃ GraphEdge v)
    (f : BoolCube n → Bool) : Prop :=
  ∀ (σ : Equiv.Perm (Fin v)) (x y : BoolCube n),
    (∀ i j, (edge j).val = (edge i).val.image σ → y j = x i) → f y = f x

/-- A monotone DNF uses only positive literals in every term, reusing the repository syntax.
[OD14, §10.5, Friedgut's Sharp Threshold Theorem] -/
def IsMonotoneDNF {n : ℕ} (d : DNF n) : Prop := ∀ t ∈ d.terms, ∀ l ∈ t, l.neg = false

end BooleanAnalysis.Hypercontractivity
