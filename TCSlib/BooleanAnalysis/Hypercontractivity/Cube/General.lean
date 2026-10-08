/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Kernel
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Tensorization
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Duality
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.TwoPoint
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# General cube hypercontractivity

Kernel formulas, tensorization, duality, scalar estimates, and the final general-exponent bounds.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Kernel`: Kernel formulas and final-coordinate factorization.
* `Tensorization`: Dimension induction for two-function bounds.
* `Duality`: Same-exponent contraction, duality, and bridging across two.
* `TwoPoint`: Scalar bounds for exponents between one and two.
* `Bounds`: The general one-function and two-function theorems.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
