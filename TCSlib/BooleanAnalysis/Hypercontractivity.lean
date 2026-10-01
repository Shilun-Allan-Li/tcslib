/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications
import TCSlib.BooleanAnalysis.Hypercontractivity.Bonami
import TCSlib.BooleanAnalysis.Hypercontractivity.CubeDefinitions
import TCSlib.BooleanAnalysis.Hypercontractivity.CubeBasic
import TCSlib.BooleanAnalysis.Hypercontractivity.CubeConsequences
import TCSlib.BooleanAnalysis.Hypercontractivity.Decomposition
import TCSlib.BooleanAnalysis.Hypercontractivity.EvenMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.General
import TCSlib.BooleanAnalysis.Hypercontractivity.KKLStatements
import TCSlib.BooleanAnalysis.Hypercontractivity.OneBit
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import TCSlib.BooleanAnalysis.Hypercontractivity.ProductSpace
import TCSlib.BooleanAnalysis.Hypercontractivity.ProductHypercontractivity
import TCSlib.BooleanAnalysis.Hypercontractivity.ProductApplications
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesBasic
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomizationDefs
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization
import TCSlib.BooleanAnalysis.Hypercontractivity.ReverseBonamiBeckner
import TCSlib.BooleanAnalysis.Hypercontractivity.SharpThresholdDefs
import TCSlib.BooleanAnalysis.Hypercontractivity.SharpThresholds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hypercontractivity

This facade exports the Boolean-cube development and statement skeletons for the remaining
Chapter 9–10 results on random variables, finite product spaces, juntas, and sharp thresholds.
Distinct theorem skeletons retain `sorry`; elementary identities and repeated corollaries
reuse existing proofs. Definitions have concrete bodies.
See `Hypercontractivity/COVERAGE.md` for the textbook-to-declaration map and validation notes.

## Main definitions

The definitions layers provide weighted cube graphs, affine random-variable hypercontractivity,
finite product spaces, orthogonal components, randomization, boosters, and pseudo-juntas.

## Main results

Hypercontractive inequalities and their concentration, influence, junta, and threshold applications.

## Contents

* `Applications`: small-set expansion on the uniform cube.
* `Bonami`: the fourth-moment Bonami bound.
* `CubeBasic`: shared cube indicators, probability, variance, and norms.
* `CubeDefinitions`: the weighted stable graph.
* `CubeConsequences`: Chapter 9 concentration and level inequalities.
* `Decomposition`: coordinate decomposition.
* `EvenMoments`: even-moment hypercontractivity.
* `General`: general-exponent hypercontractivity on the cube.
* `KKLStatements`: full KKL and dimension-independent exponential junta skeletons.
* `MomentBounds`: fourth-moment and Paley–Zygmund bounds.
* `OneBit`: two-point inequalities.
* `Parameters`: sharp noise radii and limiting norm constants.
* `ProductSpace`: heterogeneous finite-product definitions.
* `ProductHypercontractivity`: the General Hypercontractivity Theorem.
* `ProductApplications`: low-degree norms, concentration, KKL, and juntas on products.
* `RandomVariablesBasic`: hypercontractive random-variable definitions.
* `RandomVariables`: general random-variable inequalities and symmetrization.
* `RandomizationDefs`: randomized components and notable-coordinate families.
* `Randomization`: Fourier identities, norm contraction, and low-degree projection skeletons.
* `ReverseBonamiBeckner`: reverse hypercontractivity.
* `SharpThresholdDefs`: boosters, pseudo-juntas, and graph-property definitions.
* `SharpThresholds`: Friedgut–Kalai, Friedgut, Bourgain, and Hatami skeletons.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapters 9--10.
-/
