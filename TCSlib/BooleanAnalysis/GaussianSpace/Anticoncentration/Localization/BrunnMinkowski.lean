/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Real
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Marginal
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.FiniteDimensional
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Compact
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.Sections
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.BrunnMinkowski.PrekopaLeindler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Brunn–Minkowski foundations

## Contents

* `BrunnMinkowski.Real`: volume inequalities for real sum sets.
* `BrunnMinkowski.Marginal`: integrability and support of fiber integrals.
* `BrunnMinkowski.FiniteDimensional`: finite-dimensional functional inequality.
* `BrunnMinkowski.Compact`: volume inequalities for compact sets.
* `BrunnMinkowski.Sections`: concavity of dimension-root section volumes.
* `BrunnMinkowski.PrekopaLeindler`: the normalized one-dimensional functional inequality.

## Main definitions

No new definitions.

## Main results

The weighted lengths of nonempty measurable real sets are bounded by the length
of any set containing their weighted sum. Layer cake yields the normalized
one-dimensional Prékopa–Leindler arithmetic integral bound and the multiplicative
inequality for bounded first and second inputs. Finite-dimensional induction
gives the compact-set root-volume inequality and concavity of section-volume roots.

## References

* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405, Theorems 2.1, 4.1, 4.2, 5.2 and Corollary 5.3.
-/
