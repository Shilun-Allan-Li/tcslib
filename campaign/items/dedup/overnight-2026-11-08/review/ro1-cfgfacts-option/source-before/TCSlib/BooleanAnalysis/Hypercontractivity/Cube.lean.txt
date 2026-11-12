/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Bonami
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Decomposition
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Definitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.EvenMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.FourthMoment
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.OneBit
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform-cube hypercontractivity

Forward and reverse noise bounds and their coordinate infrastructure.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Basic`: Power means and elementary estimates on the uniform cube.
* `Bonami`: Bounded-degree fourth moments and their measure formulation.
* `Decomposition`: Final-coordinate restriction, averages, differences, and moments.
* `Definitions`: Cube norm and hypercontractivity predicates.
* `EvenMoments`: Even-integer output exponents and their dual bounds.
* `FourthMoment`: Coordinate induction for the (2,4) noise bound.
* `General`: Forward hypercontractivity for general real exponents.
* `OneBit`: Scalar two-point inequalities and one-bit norm duality.
* `Reverse`: Extended power means and reverse hypercontractivity.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
