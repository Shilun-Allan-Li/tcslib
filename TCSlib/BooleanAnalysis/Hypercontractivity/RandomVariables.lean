/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Discrete
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.FiniteLaw
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.General
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Norms
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Polynomial
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Symmetric
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Tensorization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random-variable hypercontractivity

General, symmetric, multilinear, and discrete random-variable results.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Basic`: Random-variable classes, moments, and independent affine sums.
* `Discrete`: Discrete contraction, the sharp radius, and optimality.
* `FiniteLaw`: Finite-support laws and probability-mass lower bounds.
* `General`: Independent sums and the centered-variable sufficient bound.
* `Norms`: Norm formulations and randomization estimates.
* `Polynomial`: Reasonability of independent multilinear polynomials.
* `Sharp`: Scalar and finite-law ingredients for the sharp discrete radius.
* `Symmetric`: Symmetric variables and symmetrization.
* `Tensorization`: Product-integral estimates for affine sections.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
