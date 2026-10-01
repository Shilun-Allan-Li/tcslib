/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.General
import TCSlib.BooleanAnalysis.Hypercontractivity.CubeBasic
import Mathlib.Combinatorics.Digraph.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The weighted stable hypercube graph

## Main definitions

* Uniform cube probability and norms are imported from `CubeBasic`.
* `WeightedDigraph`, `stableCubeGraph`, `noisyCubeGraph`: graph objects whose edge weights
  are the joint law of a correlated pair, including self-loops.

## Main results

No theorem proofs are supplied in this definitions layer.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §§9.1–9.2 and §9.5, especially Definition 9.10.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- A directed graph allowing loops, with a real weight on every ordered vertex pair.
This bundles the graph and weights used in [OD14, Def. 9.10]; the stable-cube validity
properties are stated separately. -/
structure WeightedDigraph (V : Type*) where
  /-- The underlying directed graph, including possible self-loops. -/
  graph : Digraph V
  /-- The weight of an ordered pair of vertices. -/
  edgeWeight : V → V → ℝ

/-- The `ρ`-stable cube is the complete directed graph including loops with edge weight
`Pr[X=x,Y=y] = 2⁻ⁿ Kρ(x,y)`. The intended range is `-1 ≤ ρ ≤ 1`.
[OD14, Def. 9.10] The definition also permits dimension zero. -/
noncomputable def stableCubeGraph (n : ℕ) (ρ : ℝ) : WeightedDigraph (BoolCube n) where
  graph := ⊤
  edgeWeight x y := uniformWeight n * GeneralHypercontractivity.noiseKernel ρ x y

/-- The `δ`-noisy cube is the `(1-2δ)`-stable cube, for intended range `0 ≤ δ ≤ 1`.
[OD14, Def. 9.10] -/
noncomputable def noisyCubeGraph (n : ℕ) (δ : ℝ) : WeightedDigraph (BoolCube n) :=
  stableCubeGraph n (1 - 2 * δ)

end BooleanAnalysis.Hypercontractivity
