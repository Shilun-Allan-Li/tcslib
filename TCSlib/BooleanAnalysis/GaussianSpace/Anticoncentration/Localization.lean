/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Basic
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Covering
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Antipodal
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Bisection
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Geometry
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Shrinking
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.CoordinateCuts
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Limits
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ConcaveCompactness
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.DensityLimit
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.SegmentDensity
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ConcaveLocalization
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ProfileDensity
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ProfileAnticoncentration
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.LogConcavePolynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Foundations for polynomial localization

## Contents

* `Localization.Basic`: compact truncation, plane embeddings, and half-space integrals.
* `Localization.Covering`: local sections and covering maps of topological groups.
* `Localization.Antipodal`: the continuous-angle obstruction and the odd-map zero theorem.
* `Localization.Bisection`: simultaneous bisection and cuts through prescribed affine pivots.
* `Localization.Geometry`: coordinate projections that detect two-dimensional convex sets.
* `Localization.Shrinking`: nested preserving cuts with a collinear intersection.
* `Localization.CoordinateCuts`: prescribed cuts and shrinking preserving positive integrals.
* `Localization.Limits`: integral signs on limits of shrinking sets.
* `Localization.ConcaveCompactness`: subsequence selection for bounded concave profiles.
* `Localization.BrunnMinkowski`: foundations for volume inequalities.
* `Localization.DensityLimit`: integral transfer to a limiting affine graph.
* `Localization.SegmentDensity`: concave profiles on arbitrary limiting segments.
* `Localization.ConcaveLocalization`: localization to a point or a concave segment profile.
* `Localization.ProfileDensity`: bounded log-concave probability densities from segment profiles.
* `Localization.ProfileAnticoncentration`: polynomial small-ball estimates for segment profiles.
* `Localization.LogConcavePolynomial`: multivariate polynomial estimates under log-concave densities.

## Main definitions

No new definitions.

## Main results

Continuity of half-space integrals at parameters with null boundary, and
continuity on every nonzero cut parameter for Haar measure. Circle exponential
covering and continuous-angle lifting prove the antipodal obstruction and the
punctured-space odd-map zero theorem, which gives simultaneous integral bisection.
Constrained single-integral bisection supplies cuts through prescribed affine pivots,
with a choice of side preserving positivity of a second integral.
Coordinate projections detect noncollinearity; preserving cuts through rational
pivots give nested compact convex sets with a nonempty collinear intersection.
The positive-integral invariant is supplied by prescribed coordinate cuts, and
a nonempty compact convex collinear set has a closed-segment representation.
Weighted real sum-set volume bounds and layer cake give the one-dimensional
Prékopa–Leindler inequality for bounded first and second inputs. Finite-dimensional
induction yields compact Brunn–Minkowski and concavity of section-volume roots.

## References

* Mathlib, `Mathlib.MeasureTheory.Integral.Bochner.Basic`:
  dominated continuity of parameterized integrals.
* Mathlib, `Mathlib.Topology.Covering` and `Mathlib.Topology.Homotopy.Lifting`:
  covering-space lifting and uniqueness.
* [LS93] L. Lovász and M. Simonovits, *Random Walks in a Convex Body and an
  Improved Volume Algorithm*, Random Structures & Algorithms 4(4) (1993),
  359–412, Lemma 2.5, proof of Claim 1.
-/
