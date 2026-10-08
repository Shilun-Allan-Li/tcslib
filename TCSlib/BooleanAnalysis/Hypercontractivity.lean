/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables
import TCSlib.BooleanAnalysis.Hypercontractivity.Products
import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization
import TCSlib.BooleanAnalysis.Hypercontractivity.SharpThresholds
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hypercontractivity

Shared foundations and organized cube, random-variable, finite-product, and application developments.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Parameters`: Shared reasonability parameters.
* `MomentBounds`: Probability moments, integrability, and reasonability estimates.
* `Cube`: Uniform-cube definitions and forward and reverse noise inequalities.
* `RandomVariables`: General, symmetric, multilinear, and discrete random-variable bounds.
* `Products`: Finite-product spaces, hypercontractivity, and applications.
* `Randomization`: Randomized Fourier components and notable coordinates.
* `SharpThresholds`: Boosters, pseudo-juntas, and sharp-threshold statements.
* `Applications`: Small-set expansion, low-degree consequences, influences, and KKL.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
