/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Centered
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Contraction
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Definitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.General
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.ProjectionBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomization and notable coordinates

Definitions and estimates for randomized Fourier components.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Basic`: Orthogonal-component identities and conditional moment bounds.
* `Centered`: Scalar and centered-variable negative contraction.
* `Contraction`: Coordinate and signed anisotropic noise contraction.
* `Definitions`: Randomized Fourier components and notable-coordinate predicates.
* `General`: Randomization inequalities and structural statements.
* `ProjectionBounds`: Spectral identities and norm bounds for low-degree projections.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
