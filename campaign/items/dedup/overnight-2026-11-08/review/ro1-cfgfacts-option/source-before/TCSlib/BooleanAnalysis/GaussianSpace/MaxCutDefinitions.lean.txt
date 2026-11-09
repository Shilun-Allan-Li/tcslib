/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Definitions
import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Max-Cut and its semidefinite relaxation

## Main definitions

* `MaxCut.IsValid`: normalized symmetric nonnegative weights on the existing graph model.
* `MaxCut.cutValue`, `optimum`: the normalized objective and its optimum.
* `MaxCut.sdpValue`, `sdpOptimum`: the unit-vector semidefinite relaxation.
* `MaxCut.gaussianRounding`: the random Gaussian hyperplane assignment.
* `MaxCut.gwConstant`, `gwAngle`: the exact Goemans–Williamson ratio and minimizing angle.
* `MaxCut.fiveCycle`, `fiveCycleSDP`: the source's explicit integrality-gap example.

## Main results

Definitions only. `MaxCut` supplies analytic statements; the encoded promise
problem in `UniqueGames` uses this same optimization objective.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, equations (11.34)–(11.36), Example 11.73.
* [GW95] M. Goemans and D. Williamson, Improved approximation algorithms for
  maximum cut and satisfiability problems using semidefinite programming,
  Journal of the ACM 42 (1995), 1115–1145.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.MaxCut

open Hypercontractivity

/-- A valid weighted Max-Cut graph has nonnegative symmetric weights of total
one and no loops. [OD14, §11.7, random-edge convention]
Unweighted finite graphs embed by normalizing their ordered edge counts. -/
def IsValid {n : ℕ} (G : WeightedDigraph (Fin n)) : Prop :=
  (∀ v w, 0 ≤ G.edgeWeight v w) ∧
    (∀ v w, G.edgeWeight v w = G.edgeWeight w v) ∧
    (∑ v, ∑ w, G.edgeWeight v w) = 1 ∧ (∀ v, G.edgeWeight v v = 0)

/-- The total normalized weight of edges cut by a Boolean assignment. The existing
weighted graph model supplies the weights. [OD14, §11.7, `Val_G(F)`] -/
noncomputable def cutValue {n : ℕ} (G : WeightedDigraph (Fin n)) (F : Fin n → Bool) : ℝ :=
  ∑ v, ∑ w, if F v ≠ F w then G.edgeWeight v w else 0

/-- The normalized Max-Cut optimum over all assignments. [OD14, §11.7, `Opt(G)`] -/
noncomputable def optimum {n : ℕ} (G : WeightedDigraph (Fin n)) : ℝ :=
  sSup (Set.range (cutValue G))

/-- A feasible semidefinite assignment places a unit vector at every vertex.
[OD14, §11.7, (SDP)] -/
def IsSDPAssignment {n : ℕ} (U : Fin n → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ v, ‖U v‖ = 1

/-- The semidefinite objective is the expected half of one minus the endpoint
inner product. [OD14, §11.7, (SDP)] -/
noncomputable def sdpValue {n : ℕ} (G : WeightedDigraph (Fin n))
    (U : Fin n → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ v, ∑ w, G.edgeWeight v w * ((1 - inner ℝ (U v) (U w)) / 2)

/-- The supremum of feasible unit-vector objectives. [OD14, §11.7, `SDPOpt(G)`] -/
noncomputable def sdpOptimum {n : ℕ} (G : WeightedDigraph (Fin n)) : ℝ :=
  sSup {s : ℝ | ∃ U : Fin n → EuclideanSpace ℝ (Fin n),
    IsSDPAssignment U ∧ sdpValue G U = s}

/-- Gaussian hyperplane rounding assigns each vertex the sign of its projection
onto the sampled Gaussian direction. [OD14, §11.7, Goemans–Williamson algorithm]
Zero projections are assigned `true`, matching the existing nonnegative sign convention. -/
noncomputable def gaussianRounding {n : ℕ}
    (U : Fin n → EuclideanSpace ℝ (Fin n)) (g : Fin n → ℝ) : Fin n → Bool :=
  fun v => decide (0 ≤ inner ℝ (U v) (WithLp.toLp 2 g))

/-- The Goemans–Williamson approximation constant is the infimum of the angle
ratio over positive angles at most π; zero is excluded to avoid a spurious
totalized `0/0`. [OD14, equation (11.36)] -/
noncomputable def gwConstant : ℝ :=
  sInf {c : ℝ | ∃ θ ∈ Set.Ioc (0 : ℝ) Real.pi,
    c = (θ / Real.pi) / ((1 - Real.cos θ) / 2)}

/-- The positive minimizing angle is the unique root of `tan(θ/2)=θ` in `(0,π)`.
This definition uses an infimum before the characterization obligation is proved.
[OD14, Thm. 11.72] -/
noncomputable def gwAngle : ℝ :=
  sInf {θ : ℝ | θ ∈ Set.Ioo (0 : ℝ) Real.pi ∧ Real.tan (θ / 2) = θ}

/-- The five-cycle has weight one tenth on each of its ten oriented edges.
[OD14, Example 11.73] -/
noncomputable def fiveCycle : WeightedDigraph (Fin 5) where
  graph := ⟨fun v w => (v.val + 1) % 5 = w.val ∨ (w.val + 1) % 5 = v.val⟩
  edgeWeight v w := if (v.val + 1) % 5 = w.val ∨ (w.val + 1) % 5 = v.val
    then 1 / 10 else 0

/-- The planar pentagram assignment embedded in five-dimensional Euclidean space.
[OD14, Example 11.73] -/
noncomputable def fiveCycleSDP (v : Fin 5) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (fun i => if i = 0 then Real.cos (4 * Real.pi * v.val / 5)
    else if i = 1 then Real.sin (4 * Real.pi * v.val / 5) else 0)

end BooleanAnalysis.GaussianSpace.MaxCut
