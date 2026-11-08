/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.Influence
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.LowDegree
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.SmallSetExpansion

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Applications of hypercontractivity

Small-set expansion, low-degree estimates, stable influence, and KKL statements.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Influence`: Stable influence and Fourier-level inequalities.
* `KKL`: KKL and biased-cube influence statements.
* `LowDegree`: Low-degree, concentration, and spectral consequences.
* `SmallSetExpansion`: Small-set expansion and tail estimates.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
