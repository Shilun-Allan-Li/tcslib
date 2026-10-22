/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Definitions
import TCSlib.BooleanAnalysis.GaussianSpace.Profile
import TCSlib.BooleanAnalysis.GaussianSpace.Inputs
import TCSlib.BooleanAnalysis.GaussianSpace.InputMoments
import TCSlib.BooleanAnalysis.GaussianSpace.GaussianDensity
import TCSlib.BooleanAnalysis.GaussianSpace.ProductDensity
import TCSlib.BooleanAnalysis.GaussianSpace.ProductDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.ProductBounds
import TCSlib.BooleanAnalysis.GaussianSpace.ProductHessian
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import TCSlib.BooleanAnalysis.GaussianSpace.Halfspace
import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorSmoothing
import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorRegularity
import TCSlib.BooleanAnalysis.GaussianSpace.ProfileApproximation
import TCSlib.BooleanAnalysis.GaussianSpace.SmoothVariation
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Walk
import TCSlib.BooleanAnalysis.GaussianSpace.BooleanBlocks
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedSums
import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedBlocks
import TCSlib.BooleanAnalysis.GaussianSpace.GaussianBobkov
import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck
import TCSlib.BooleanAnalysis.GaussianSpace.HermiteDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite
import TCSlib.BooleanAnalysis.GaussianSpace.Borell
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceRelaxation
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples
import TCSlib.BooleanAnalysis.GaussianSpace.SumInvariance
import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceExtensions
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration
import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest
import TCSlib.BooleanAnalysis.GaussianSpace.MaxCutDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.MaxCut
import TCSlib.BooleanAnalysis.GaussianSpace.UniqueGamesDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.UniqueGames
import TCSlib.BooleanAnalysis.GaussianSpace.MaxCutAlgorithm
import TCSlib.BooleanAnalysis.GaussianSpace.Condorcet

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian space and invariance principles

## Contents

* `Definitions`: rotation sensitivity, rotation-limit surface area, and a profile endpoint adapter.
* `Profile`: Gaussian quantile calculus, reflection, convexity, and profile endpoint continuity.
* `Inputs`: fourth-moment hypotheses using the existing general-input Bonami definitions.
* `InputMoments`: standard Gaussian and uniform Boolean input-moment instances.
* `GaussianDensity`: scalar Gaussian averaging derivatives and regularity bounds.
* `ProductDensity`: finite-product Gaussian densities and affine integration adapters.
* `ProductDifferentiation`: continuous differentiability of bounded product Gaussian averages.
* `ProductBounds`: coordinate first- and second-derivative moment bounds.
* `ProductHessian`: second differentiation and Lipschitz derivatives of Gaussian averages.
* `Rotation`: Theorem 11.43 and Corollary 11.44.
* `Halfspace`: Gaussian projection and the halfspace crossing-probability limit.
* `IndicatorSmoothing`: integral approximation and mean preservation for averaged indicators.
* `IndicatorRegularity`: differentiability and explicit derivative bounds for averaged indicators.
* `ProfileApproximation`: vanishing profile integrals for averaged Gaussian indicators.
* `SmoothVariation`: directional rotation limits and nonnegative integral gradient bounds.
* `SurfaceArea`: Definition 11.48, Proposition 11.49, and Theorems 11.51–11.52.
* `Bobkov`: the Boolean two-point and full inequalities, and Theorem 11.55.
* `Bobkov/Walk`: the optional stopped-walk Claim 11.54 as a submartingale statement.
* `BooleanBlocks`: Boolean Bobkov under finite coordinate reindexing and currying.
* `Invariance`: the general-input fourth-order Basic Invariance Principle and Corollaries 11.67–11.68.
* `NormalizedSums`: quantitative Lipschitz approximation of normalized sums by a Gaussian.
* `NormalizedBlocks`: finite-dimensional approximation by independent normalized Boolean blocks.
* `GaussianBobkov`: the smooth Gaussian inequality for bounded Lipschitz derivatives.
* `NoiseDefinitions`: the correlated Gaussian law, Mehler noise, and stability.
* `Noise`: Gaussian noise analysis, polynomial density, and hypercontractivity statements.
* `OrnsteinUhlenbeck`: strong generator domain, integration by parts, and log-Sobolev statements.
* `HermiteDefinitions`: normalized Mathlib Hermites, product polynomials, and coefficients.
* `Hermite`: orthonormal basis, expansions, and noise/generator spectral statements.
* `Borell`: general-volume noise stability and all-angle balanced rotation statements.
* `SurfaceRelaxation`: smooth relaxation, attainment, and regular Minkowski comparison statements.
* `SurfaceExamples`: interval, ball, convex, polytope, cone, and polynomial-threshold statements.
* `SumInvariance`: scalar sum invariance, full smooth approximation, and distributional statements.
* `InvarianceExtensions`: third-order, no-notables, tail, and Lévy comparison statements.
* `Anticoncentration`: arbitrary-polynomial Carbery–Wright and multilinear CDF statements.
* `MajorityIsStablest`: quantitative general-volume and no-notables statements.
* `MaxCutDefinitions`: the existing graph model's cut/SDP objectives and Gaussian rounding.
* `MaxCut`: analytic Goemans–Williamson and five-cycle integrality-gap statements.
* `UniqueGamesDefinitions`: concrete CSP encodings, promise reductions, and UGC.
* `UniqueGames`: codec transport and genuine conditional Max-Cut hardness statements.
* `MaxCutAlgorithm`: finite-precision polynomial-time randomized approximation statements.
* `Condorcet`: the final small-influence voting-rationality application.

## Main definitions

All new objects live in `BooleanAnalysis.GaussianSpace`; existing Gaussian, polynomial,
Fourier, moment, and influence definitions are reused. See `GaussianSpace/COVERAGE.md`
for the source inventory, reuse decisions, precise domains, and proof obligations.

## Main results

The rotation-sensitivity estimates, all three Boolean Bobkov inequalities,
the general-input fourth-order invariance principle, both quantitative invariance
corollaries, and smooth Gaussian Bobkov for bounded Lipschitz derivatives are proved.
All six surface-area statements are proved, including the general-volume Gaussian
isoperimetric inequality. See `GaussianSpace/COVERAGE.md` for the exact boundary.
The remaining main-text chapter material now has a concrete definition and statement
layer, whose theorem proofs intentionally remain `sorry`. Existing local Berry–Esseen,
Sheppard, polynomial, Fourier, moment, influence and voting APIs are reused.
External overlap does not exclude statements from this layer: those projects cannot
be imported into this toolchain. Exercises are outside the main-text inventory.
No dependency or toolchain changes are part of this development.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Chapter 11, pp. 327–370.
-/
