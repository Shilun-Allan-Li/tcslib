/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Definitions
import TCSlib.BooleanAnalysis.GaussianSpace.Profile
import TCSlib.BooleanAnalysis.GaussianSpace.Inputs
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian space and invariance principles

## Contents

* `Definitions`: rotation sensitivity, rotation-limit surface area, and a profile endpoint adapter.
* `Profile`: Gaussian quantile calculus, reflection, convexity, and profile endpoint continuity.
* `Inputs`: fourth-moment hypotheses using the existing general-input Bonami definitions.
* `Rotation`: Theorem 11.43 and Corollary 11.44.
* `SurfaceArea`: Definition 11.48, Proposition 11.49, and Theorems 11.51–11.52.
* `Bobkov`: the Boolean two-point and full inequalities, and Theorem 11.55.
* `Invariance`: the general-input fourth-order Basic Invariance Principle and Corollaries 11.67–11.68.

## Main definitions

All new objects live in `BooleanAnalysis.GaussianSpace`; existing Gaussian, polynomial,
Fourier, moment, and influence definitions are reused. See `GaussianSpace/COVERAGE.md`
for the source inventory, external-library exclusions, and deferred integration work.

## Main results

The rotation-sensitivity estimates, all three Boolean Bobkov inequalities,
the general-input fourth-order invariance principle, and both quantitative invariance
corollaries are proved. The six surface-area statements remain a skeleton;
see `GaussianSpace/COVERAGE.md` for the exact boundary.
This partial chapter development omits existing local or external results, including Berry–Esseen,
Hermite/Ornstein–Uhlenbeck theory, Gaussian hypercontractivity, and Majority Is Stablest.
No dependency or toolchain changes are part of this development.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Chapter 11, pp. 327–370.
-/
