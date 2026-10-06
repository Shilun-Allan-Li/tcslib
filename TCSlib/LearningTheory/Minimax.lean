/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.ZeroSumGame
import TCSlib.LearningTheory.Minimax.HedgeInteraction
import TCSlib.LearningTheory.Minimax.FiniteMinimax
import TCSlib.LearningTheory.Minimax.CCE
import TCSlib.LearningTheory.Minimax.ConvexMinimaxCore
import TCSlib.LearningTheory.Minimax.ConvexMinimaxSeparation
import TCSlib.LearningTheory.Minimax.ConvexMinimaxNoRegret
import TCSlib.LearningTheory.Minimax.ConvexMinimax

/-!
# Minimax Theorems via No-Regret Learning

Finite zero-sum games, the Hedge-vs-best-response construction of approximate
saddle points, coarse correlated equilibria, and two routes to the convex-compact
minimax theorem (Cesa-Bianchi–Lugosi Thm 7.1).

## Contents

- `Minimax.ZeroSumGame`: finite zero-sum games, mixed strategies, best responses, weak duality
- `Minimax.HedgeInteraction`: game loss sequence, average/empirical strategies, Hedge prefixes
- `Minimax.FiniteMinimax`: regret-to-payoff bridge and the ε-approximate minimax theorem
- `Minimax.CCE`: (approximate) coarse correlated equilibria; no-regret empirical play is an ε-CCE
- `Minimax.ConvexMinimaxCore`: exact finite value, convex-compact hypotheses, Jensen, sublevel sets
- `Minimax.ConvexMinimaxSeparation`: Hahn–Banach/finite-column route (unconditional)
- `Minimax.ConvexMinimaxNoRegret`: no-regret/finite-approximation route, strengthened hypotheses
- `Minimax.ConvexMinimax`: the public `convex_compact_minimax`
-/
