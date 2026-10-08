/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Function.Basic
import TCSlib.Complexity.Formulas.QBF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite perfect-information games: determinacy

[AB09, Exercise 4.10] (Zermelo): in every finite two-person game with perfect
information and no draws, one of the two players has a winning strategy. The
connection to `PSPACE` is Example 4.15's QBF game — "player 1 has a winning
strategy" *is* the truth of an alternating quantified formula — and this
module supplies the game vocabulary and the determinacy statement at the
same binary granularity as `Complexity.QBF`. Phase P4.3 of
`AroraBarakChapters3-4Plan.md`.

## Design

* **The game is `n` alternating binary moves**: player one moves at even
  plies, player two at odd plies, the history is the list of moves (most
  recent last), and `W` decides the winner from the complete history —
  `true` meaning player one wins. No draws, matching the exercise's premise;
  finite games with draws reduce by splitting the draw outcome.
* A **strategy** is a function from the history so far to the next move;
  `playOut` folds two strategies into the complete history. This is
  deliberately the plainest rendering — richer game trees (variable
  branching, chess-like boards) are out of scope, as [AB09]'s own discussion
  of generalized boards notes (p. 87).

## Main definitions

* `Complexity.Game.playOut` — the history of a strategy pair.
* `Complexity.Game.FirstWins`, `Complexity.Game.SecondWins` — the two
  winning-strategy predicates.

## Main results (sorried; phase-P4.3 statement)

* `Complexity.Game.determined` — [AB09, Exercise 4.10].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.2, Example 4.15, Exercise 4.10.)
-/

namespace Complexity.Game

/-- The complete history of an `n`-ply game under the strategy pair
`(s₁, s₂)`: at each ply the mover — player one on even plies, player two on
odd — applies their strategy to the history so far, and the move is
appended. -/
def playOut (s₁ s₂ : List Bool → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let h := playOut s₁ s₂ n
    h ++ [if h.length % 2 = 0 then s₁ h else s₂ h]

/-- Player one has a **winning strategy** in the `n`-ply game with win
predicate `W` (`true` = player one wins the completed history): some
strategy of theirs beats every strategy of player two.
[AB09, §4.2.2 and Exercise 4.10] -/
def FirstWins (n : ℕ) (W : List Bool → Bool) : Prop :=
  ∃ s₁ : List Bool → Bool, ∀ s₂ : List Bool → Bool, W (playOut s₁ s₂ n) = true

/-- Player two has a winning strategy: some strategy of theirs defeats every
strategy of player one. -/
def SecondWins (n : ℕ) (W : List Bool → Bool) : Prop :=
  ∃ s₂ : List Bool → Bool, ∀ s₁ : List Bool → Bool, W (playOut s₁ s₂ n) = false

/-- **Zermelo determinacy** ([AB09, Exercise 4.10]; spec, fill pending —
phase P4.3): every finite two-person perfect-information game without draws
is determined — exactly one quantifier alternation wins, so in particular
one of the players has a winning strategy.

**Proof sketch.** Backward induction on the remaining plies, generalized
over the history prefix: the position value
`V h := "the mover from h can force a win for their side"` satisfies the
alternating recursion `V h = ∃/∀ b, V (h ++ [b])` by ply parity, with the
base `V` of complete histories read off `W`; classical excluded middle turns
"not every move loses" into a winning move at each `∀`-node (the
`Complexity.QBF.truthAux` recursion is the same shape, which is Example
4.15's point). Assembling the per-position choices into whole strategies is
the only bookkeeping: define `s₁` by choosing a winning move wherever `V`
holds (classical choice), arbitrary elsewhere. Mutual exclusion (`¬(FirstWins
∧ SecondWins)`) follows by playing the two winning strategies against each
other — not claimed in this statement, which renders the exercise's "one of
the two players has a winning strategy" disjunction. -/
theorem determined (n : ℕ) (W : List Bool → Bool) :
    FirstWins n W ∨ SecondWins n W := by
  sorry

end Complexity.Game
