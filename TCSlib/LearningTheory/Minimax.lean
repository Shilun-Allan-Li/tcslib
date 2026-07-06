/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/

import TCSlib.LearningTheory.Minimax.FiniteMinimax
import TCSlib.LearningTheory.Minimax.CCE
import TCSlib.LearningTheory.Minimax.ConvexMinimaxCore
import TCSlib.LearningTheory.Minimax.ConvexMinimaxSeparation
import TCSlib.LearningTheory.Minimax.ConvexMinimaxNoRegret

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Finset BigOperators

namespace OnlineLearning

/-!
# Convex-Compact Minimax

## Main results

- `convex_compact_minimax`: proves equality of upper and lower values for payoff functions on subsets of ℝ under nonempty compact convex row set, nonempty convex column set, boundedness, convex-concavity, and continuity assumptions

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-- Public convex-compact minimax theorem for this project.

The hypotheses are bundled in `ConvexCompactMinimaxHypotheses`: nonempty compact
convex row set, nonempty convex column set, boundedness, convexity in the row
variable, concavity in the column variable, and the relevant continuity
assumptions.  The conclusion `ConvexCompactMinimaxStatement` is the equality of
the upper and lower values.

This theorem is intentionally a thin wrapper.  It hides the proof-route choice
from downstream files and currently delegates to the completed separation proof. -/
theorem convex_compact_minimax {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ConvexCompactMinimaxStatement X Y f := by
  -- Keep the public theorem independent of proof-route details.  At present,
  -- the separation proof is the strongest completed route.
  exact convex_compact_minimax_by_separation h

end OnlineLearning
