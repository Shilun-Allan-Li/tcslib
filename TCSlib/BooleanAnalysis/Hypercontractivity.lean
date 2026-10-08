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
import TCSlib.BooleanAnalysis.Hypercontractivity.FiniteNoiseDuality
import TCSlib.BooleanAnalysis.Hypercontractivity.FiniteNoiseContraction
import TCSlib.BooleanAnalysis.Hypercontractivity.FiniteNoiseOptimization
import TCSlib.BooleanAnalysis.Hypercontractivity.KKLStatements
import TCSlib.BooleanAnalysis.Hypercontractivity.OneBit
import TCSlib.BooleanAnalysis.Hypercontractivity.BiasedTwoPoint
import TCSlib.BooleanAnalysis.Hypercontractivity.BiasedTwoPointContraction
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import TCSlib.BooleanAnalysis.Hypercontractivity.SharpParameters
import TCSlib.BooleanAnalysis.Hypercontractivity.ProductSpace
import TCSlib.BooleanAnalysis.Hypercontractivity.ProductHypercontractivity
import TCSlib.BooleanAnalysis.Hypercontractivity.ProductApplications
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesBasic
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesFiniteLaw
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesTwoPoint
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesSharp
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesPolynomial
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesTensorization
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesNorms
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesSymmetric
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
* `FiniteNoiseDuality`: signed witnesses and duality for finite weighted noise.
* `FiniteNoiseContraction`: grouping finite functions and sharp noise contraction.
* `FiniteNoiseOptimization`: compactness and variational reduction for finite weighted noise.
* `KKLStatements`: full KKL and dimension-independent exponential junta skeletons.
* `MomentBounds`: fourth-moment and Paley–Zygmund bounds.
* `OneBit`: two-point inequalities.
* `BiasedTwoPoint`: scalar calculus for the sharp biased two-point inequality.
* `BiasedTwoPointContraction`: sharp inequalities for signed two-point inputs.
* `Parameters`: sharp noise radii and limiting norm constants.
* `SharpParameters`: identities and bounds for sharp discrete parameters.
* `ProductSpace`: heterogeneous finite-product definitions.
* `ProductHypercontractivity`: the General Hypercontractivity Theorem.
* `ProductApplications`: low-degree norms, concentration, KKL, and juntas on products.
* `RandomVariablesBasic`: hypercontractive random-variable definitions.
* `RandomVariablesFiniteLaw`: finite-law expectation and norm computations.
* `RandomVariablesTwoPoint`: sharp contraction for centered two-point laws.
* `RandomVariablesSharp`: sharp finite-law contraction for arbitrary probability spaces.
* `RandomVariablesPolynomial`: fourth moments of independent multilinear polynomials.
* `RandomVariablesTensorization`: product-law contraction, including infinite exponents.
* `RandomVariablesNorms`: symmetrization and randomization of affine norms.
* `RandomVariablesSymmetric`: hypercontractivity of symmetric random variables.
* `RandomVariables`: general and discrete random-variable inequalities.
* `RandomizationDefs`: randomized components and notable-coordinate families.
* `Randomization`: Fourier identities, norm contraction, and low-degree projection skeletons.
* `ReverseBonamiBeckner`: reverse hypercontractivity.
* `SharpThresholdDefs`: boosters, pseudo-juntas, and graph-property definitions.
* `SharpThresholds`: Friedgut–Kalai, Friedgut, Bourgain, and Hatami skeletons.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapters 9--10.
-/
