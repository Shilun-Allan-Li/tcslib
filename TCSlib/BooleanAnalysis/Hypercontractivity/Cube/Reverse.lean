/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.TwoPoint
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Tensorization
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Holder
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Extension
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.TwoFunction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reverse cube hypercontractivity

Extended means, the reverse two-point estimate, tensorization, exponent extensions, and the two-function theorem.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Basic`: Power-mean conventions, including zero and negative exponents.
* `TwoPoint`: The scalar reverse inequality and its one-bit formulation.
* `Tensorization`: Mixed means, dimension induction, and noise monotonicity.
* `Holder`: Reverse Young and Hölder inequalities.
* `Extension`: Endpoint and negative-exponent extensions.
* `TwoFunction`: Exponent monotonicity and the final two-function bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
