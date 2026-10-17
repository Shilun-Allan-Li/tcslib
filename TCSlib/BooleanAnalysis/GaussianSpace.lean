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
import TCSlib.BooleanAnalysis.GaussianSpace.BooleanBlocks
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedSums
import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedBlocks
import TCSlib.BooleanAnalysis.GaussianSpace.GaussianBobkov

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
* `BooleanBlocks`: Boolean Bobkov under finite coordinate reindexing and currying.
* `Invariance`: the general-input fourth-order Basic Invariance Principle and Corollaries 11.67–11.68.
* `NormalizedSums`: quantitative Lipschitz approximation of normalized sums by a Gaussian.
* `NormalizedBlocks`: finite-dimensional approximation by independent normalized Boolean blocks.
* `GaussianBobkov`: the smooth Gaussian inequality for bounded Lipschitz derivatives.

## Main definitions

All new objects live in `BooleanAnalysis.GaussianSpace`; existing Gaussian, polynomial,
Fourier, moment, and influence definitions are reused. See `GaussianSpace/COVERAGE.md`
for the source inventory, external-library exclusions, and deferred integration work.

## Main results

The rotation-sensitivity estimates, all three Boolean Bobkov inequalities,
the general-input fourth-order invariance principle, both quantitative invariance
corollaries, and smooth Gaussian Bobkov for bounded Lipschitz derivatives are proved.
All six surface-area statements are proved, including the general-volume Gaussian
isoperimetric inequality. See `GaussianSpace/COVERAGE.md` for the exact boundary.
This partial chapter development omits existing local or external results, including Berry–Esseen,
Hermite/Ornstein–Uhlenbeck theory, Gaussian hypercontractivity, and Majority Is Stablest.
No dependency or toolchain changes are part of this development.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Chapter 11, pp. 327–370.
-/
