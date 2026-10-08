/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteLaw
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseContraction
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseDuality
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseOptimization
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.Parameters
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.TwoPointCalculus
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.TwoPointContraction
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.TwoPointLaw

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp discrete random-variable bounds

Scalar, finite-space, and finite-law layers of the sharp discrete hypercontractivity proof.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `FiniteLaw`: Transferring finite-space contraction to discrete laws.
* `FiniteNoiseContraction`: Sharp contraction on arbitrary finite spaces.
* `FiniteNoiseDuality`: Finite-space noise, Hölder extremizers, and duality.
* `FiniteNoiseOptimization`: Finite-space optimization and two-value reduction.
* `Parameters`: Sharp radius parameters and elementary scalar identities.
* `TwoPointCalculus`: Biased two-point means and calculus estimates.
* `TwoPointContraction`: Sharp contraction on a biased two-point space.
* `TwoPointLaw`: Transferring two-point contraction to random-variable laws.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
