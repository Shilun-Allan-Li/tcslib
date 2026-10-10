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

## Main results

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

/-- G1: the remaining-game value, always from player one's perspective:
terminal value is `W`, even plies use OR and odd plies use AND. -/
private def positionValue (W : List Bool → Bool) : ℕ → List Bool → Bool
  | 0, h => W h
  | r + 1, h =>
      if h.length % 2 = 0 then
        positionValue W r (h ++ [true]) || positionValue W r (h ++ [false])
      else
        positionValue W r (h ++ [true]) && positionValue W r (h ++ [false])

/-- G2: append the move prescribed by the current mover's strategy. -/
private def ply (s₁ s₂ : List Bool → Bool) (h : List Bool) : List Bool :=
  h ++ [if h.length % 2 = 0 then s₁ h else s₂ h]

/-- The recursive play history takes one ply at its successor horizon. -/
private theorem playOut_succ_ply (s₁ s₂ : List Bool → Bool) (r : ℕ) :
    playOut s₁ s₂ (r + 1) = ply s₁ s₂ (playOut s₁ s₂ r) := rfl

/-- G2: playing from the empty history is iteration of the one-ply map. -/
private theorem playOut_eq_iterate (s₁ s₂ : List Bool → Bool) (r : ℕ) :
    playOut s₁ s₂ r = (ply s₁ s₂)^[r] [] := by
  induction r with
  | zero => rfl
  | succ r ih => rw [playOut_succ_ply, ih, Function.iterate_succ_apply']

/-- G3: player one takes the true move exactly when that child has true
value at the remaining horizon. -/
private def firstGreedy (n : ℕ) (W : List Bool → Bool) (h : List Bool) : Bool :=
  positionValue W (n - (h.length + 1)) (h ++ [true])

/-- G3: player two takes the true move exactly when that child's value is
false at the remaining horizon. -/
private def secondGreedy (n : ℕ) (W : List Bool → Bool) (h : List Bool) : Bool :=
  !(firstGreedy n W h)

/-- G4: the player selected by the target bit can maintain the current
value through the remaining play by following its greedy strategy.

**Proof sketch.** Induct on the remaining plies. The horizon equation makes
the greedy look-ahead equal to the child's remaining horizon. At the
constrained player's turn the greedy move preserves the value. At the
other player's turn, a false OR or a true AND fixes both child values.
The induction hypothesis applies to the chosen child. At horizon zero
position value is the terminal predicate. -/
private theorem winner_of_value (n : ℕ) (W : List Bool → Bool)
    (s₁ s₂ : List Bool → Bool) (b : Bool)
    (hs₁ : b = true → s₁ = firstGreedy n W)
    (hs₂ : b = false → s₂ = secondGreedy n W)
    (r : ℕ) (h : List Bool) (hlen : h.length + r = n)
    (hv : positionValue W r h = b) :
    W ((ply s₁ s₂)^[r] h) = b := by
  induction r generalizing h with
  | zero => exact hv
  | succ r ih =>
      have hr : n - (h.length + 1) = r := by omega
      rw [Function.iterate_succ_apply]
      refine ih (ply s₁ s₂ h) ?_ ?_
      · simp only [ply, List.length_append, List.length_singleton]
        omega
      · cases b <;> by_cases heven : h.length % 2 = 0 <;>
          cases htrue : positionValue W r (h ++ [true]) <;>
          cases hfalse : positionValue W r (h ++ [false]) <;>
          cases hmove : (if h.length % 2 = 0 then s₁ h else s₂ h) <;>
          simp_all [positionValue, ply, firstGreedy, secondGreedy]

/-- **Zermelo determinacy** ([AB09, Exercise 4.10]): every finite two-person perfect-information game without draws
is determined — exactly one quantifier alternation wins, so in particular
one of the players has a winning strategy.

**Proof sketch.** Backward induction on the remaining plies, generalized
over the history prefix: the position value is taken at the **fixed player-one
perspective**, `V h := "player one can force W = true from h"` — a
mover-relative value flips polarity with the turn and breaks the recursion
(round-1 finding 9) — and satisfies `V h = ∃ b, V (h ++ [b])` at even
histories, `V h = ∀ b, V (h ++ [b])` at odd ones, with the base read off `W`
(the `Complexity.QBF.truthAux` recursion is the same shape, which is Example
4.15's point). Strategy assembly covers both polarities: if `V []` holds,
`s₁` picks a true-valued child at every even node it can reach; if not, `s₂`
picks a false-valued child at every odd node — each extended arbitrarily off
its winning tree. At fixed horizon the case analysis is finite, so classical
instances are available but not essential. Mutual exclusion (`¬(FirstWins
∧ SecondWins)`) follows by playing the two winning strategies against each
other — not claimed in this statement, which renders the exercise's "one of
the two players has a winning strategy" disjunction. -/
theorem determined (n : ℕ) (W : List Bool → Bool) :
    FirstWins n W ∨ SecondWins n W := by
  cases hv : positionValue W n [] with
  | false =>
      refine Or.inr ⟨secondGreedy n W, fun s₁ => ?_⟩
      rw [playOut_eq_iterate]
      exact winner_of_value n W s₁ (secondGreedy n W) false
        (by simp) (fun _ => rfl) n [] (by simp) hv
  | true =>
      refine Or.inl ⟨firstGreedy n W, fun s₂ => ?_⟩
      rw [playOut_eq_iterate]
      exact winner_of_value n W (firstGreedy n W) s₂ true
        (fun _ => rfl) (by simp) n [] (by simp) hv

end Complexity.Game
