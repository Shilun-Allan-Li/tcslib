/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp hypercontractive parameters

## Main definitions

* `sharpDiscreteRadius`: the optimal radius from the biased two-point inequality.
* `productNormComparisonConstant`: the limiting low-degree norm-comparison constant.

## Main results

No theorem statements; these concrete formulas are shared by the random-variable and
finite-product developments.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Theorems 10.18 and 10.22.
-/

open scoped Classical

namespace BooleanAnalysis.Hypercontractivity

/-- The sharp radius for a discrete law of minimum mass `lam < 1/2`, using
`u = log((1-lam)/lam)` and conjugate exponent `q/(q-1)`.
[OD14, Thm. 10.18, equation (10.5)] -/
noncomputable def sharpDiscreteRadius (q lam : ℝ) : ℝ :=
  let u := Real.log ((1 - lam) / lam)
  Real.sqrt (Real.sinh (u / q) / Real.sinh (u / (q / (q - 1))))

/-- The limiting norm-comparison constant is `((1-lam)/lam)^(1/(2(1-2lam)))`,
continuously extended to `e` at `lam=1/2`. Its intended range is `0 < lam ≤ 1/2`.
[OD14, Thm. 10.22] -/
noncomputable def productNormComparisonConstant (lam : ℝ) : ℝ :=
  if lam = 1 / 2 then Real.exp 1 else ((1 - lam) / lam) ^ (1 / (2 * (1 - 2 * lam)))

end BooleanAnalysis.Hypercontractivity
