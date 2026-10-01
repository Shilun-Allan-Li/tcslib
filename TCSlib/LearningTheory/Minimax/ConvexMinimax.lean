/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.ConvexMinimaxCore
import TCSlib.LearningTheory.Minimax.ConvexMinimaxSeparation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Convex-Compact Minimax

## Main definitions

None (this file only states the public convex-compact minimax theorem).

## Main results

- `convex_compact_minimax`: equality of the upper and lower values of a payoff function on
  subsets of `ℝ`, for a nonempty compact convex row set, a nonempty convex column set, and
  a bounded payoff that is convex and continuous in the row variable and concave in the
  column variable [CBL06, Thm 7.1].

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Chapter 7 (Theorem 7.1).

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

namespace OnlineLearning

/-- The convex-compact minimax theorem: for a nonempty compact convex `X ⊆ ℝ`, a nonempty
convex `Y ⊆ ℝ`, and a bounded payoff `f` that is convex and continuous in the row
variable `x` for each `y ∈ Y` and concave in the column variable `y` for each `x ∈ X`
(the hypotheses bundled in `ConvexCompactMinimaxHypotheses`), the upper value
`inf_{x ∈ X} sup_{y ∈ Y} f x y` equals the lower value `sup_{y ∈ Y} inf_{x ∈ X} f x y`
(the conclusion `ConvexCompactMinimaxStatement`). [CBL06, Thm 7.1]. Deviation:
specialized to subsets of `ℝ`, and proved via the Hahn–Banach separation route of
`ConvexMinimaxSeparation` rather than the source's no-regret argument, whose last step
needs an extra uniformity hypothesis (see `ConvexMinimaxNoRegret`).

This theorem is intentionally a thin wrapper.  It hides the proof-route choice
from downstream files and currently delegates to the completed separation proof. -/
theorem convex_compact_minimax {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ConvexCompactMinimaxStatement X Y f := by
  -- Keep the public theorem independent of proof-route details.  At present,
  -- the separation proof is the strongest completed route.
  exact convex_compact_minimax_by_separation h

end OnlineLearning
