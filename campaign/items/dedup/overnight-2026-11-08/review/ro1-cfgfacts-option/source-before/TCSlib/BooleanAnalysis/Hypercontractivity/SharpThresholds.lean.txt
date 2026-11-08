/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.SharpThresholds.Definitions
import TCSlib.BooleanAnalysis.Hypercontractivity.SharpThresholds.General

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp thresholds

Definitions and statements for boosters, pseudo-juntas, and sharp thresholds.

## Main definitions

Definitions live in the child modules.

## Main results

This facade exports the complete development in its folder.

## Contents

* `Definitions`: Booster and pseudo-junta predicates.
* `General`: Sharp-threshold and pseudo-junta statements.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Chapters 9–10.
-/
