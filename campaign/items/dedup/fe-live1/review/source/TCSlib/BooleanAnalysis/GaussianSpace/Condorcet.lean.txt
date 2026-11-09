/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest
import TCSlib.BooleanAnalysis.ArrowTheorem

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Condorcet rationality with small influences: statement layer

## Main definitions

The voting profile and the three pairwise vote vectors are reused from
`ArrowTheorem`. A rational outcome means the three social comparisons do not
form a cycle; no second voting model or probability convention is introduced.

## Main results

The final main-text application in §11.7: majority asymptotically maximizes
rationality among small-influence voting rules. Both new proofs are placeholders.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, pp. 369–370, final Condorcet application;
  §2.5, Theorem 2.56.
-/

open MeasureTheory Filter
open scoped Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- No small-influence ±1-valued voting rule asymptotically exceeds majority's
three-candidate rationality. [OD14, §11.7, final application]
Oddness and unbiasedness are not required: the odd part controls the relevant
negative-correlation stability.

**Proof sketch.** Use Kalai's cycle formula in the existing voting model, bound
negative-correlation stability by positive-correlation stability of the odd
part, and apply balanced Majority Is Stablest at correlation one third. -/
theorem condorcet_rationality_small_influences :
    ∀ η : ℝ, 0 < η → ∃ τ : ℝ, 0 < τ ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      isPmOne f → maxInfluence f ≤ τ →
        ((PMF.uniformOfFintype (ArrowTheorem.Profile n)).toMeasure
          {p | ¬ (f (ArrowTheorem.abVotes p) = f (ArrowTheorem.bcVotes p) ∧
            f (ArrowTheorem.bcVotes p) = f (ArrowTheorem.caVotes p))}).toReal ≤
          3 / 4 + 3 / (2 * Real.pi) * Real.arcsin (1 / 3) + η := sorry

/-- Odd majorities attain the limiting rationality in the small-influence
upper bound. [OD14, §11.7, final application; §2.5, Thm. 2.56]

**Proof sketch.** Majority is odd, so Kalai's formula is equality with its
positive one-third stability. Use the existing majority stability limit and
the scalar Sheppard formula. -/
theorem majority_condorcet_rationality_tendsto :
    Tendsto (fun k : ℕ =>
      ((PMF.uniformOfFintype (ArrowTheorem.Profile (2 * k + 1))).toMeasure
        {p | ¬ (majority k (ArrowTheorem.abVotes p) = majority k (ArrowTheorem.bcVotes p) ∧
          majority k (ArrowTheorem.bcVotes p) = majority k (ArrowTheorem.caVotes p))}).toReal)
      atTop (𝓝 (3 / 4 + 3 / (2 * Real.pi) * Real.arcsin (1 / 3))) := sorry

end BooleanAnalysis.GaussianSpace
