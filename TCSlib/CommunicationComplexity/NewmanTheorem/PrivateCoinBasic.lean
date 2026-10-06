/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-Coin Protocol Model

A private-coin protocol is a randomized protocol in which Alice and Bob each sample their own
random string, hidden from the other player [RY20, Ch. 3, §Variants of Randomized Protocols:
private coins]. It is modelled as a deterministic protocol (`Deterministic.Protocol`) whose
inputs are the pairs `(ω_x, x)` and `(ω_y, y)`, so that every result about deterministic
protocols applies verbatim once the randomness is fixed. Correctness is measured by the
worst-case error over inputs, with the probability taken over the product of the two private
randomness spaces.

## Main definitions

- `PrivateCoin.Protocol`: a deterministic protocol on `(Ω_X × X) × (Ω_Y × Y)`, i.e. one where
  Alice sees her private randomness `ω_x : Ω_X` and Bob sees his private randomness
  `ω_y : Ω_Y`.
- `PrivateCoin.Protocol.output`, `PrivateCoin.Protocol.alice`, `PrivateCoin.Protocol.bob`:
  the constructors, with message functions taking the input and the player's own randomness.
- `PrivateCoin.Protocol.rrun`: the output of the protocol on inputs `x`, `y` and randomness
  `ω_x`, `ω_y`.
- `PrivateCoin.Protocol.ApproxSatisfies`, `PrivateCoin.Protocol.ApproxComputes`: a
  private-coin protocol `ε`-computes a function if on every input the probability of an
  incorrect answer is at most `ε`; the predicate version replaces "incorrect" by the failure
  of a relation.

## Main results

- `PrivateCoin.Protocol.ApproxComputes_eq_ApproxSatisfies`: `ε`-computing `f` is the same
  as `ε`-satisfying the relation "the output equals `f x y`".

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PrivateCoin

/-- A private-coin protocol with randomness `Ω_X` for Alice and `Ω_Y` for Bob, inputs `X`,
`Y` and outputs `α`: a deterministic protocol where Alice's input is augmented with her
private randomness and Bob's with his, so Alice's message functions see `(ω_x, x)` and Bob's
see `(ω_y, y)`, and neither player sees the other's coins
[RY20, Ch. 3, §Variants of Randomized Protocols: private coins]. -/
abbrev Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω_X × X) (Ω_Y × Y) α

namespace Protocol

variable {Ω_X Ω_Y : Type*} {X Y α : Type*}

/-- The private-coin protocol that sends no message and outputs `a` on every input and every
pair of random strings. -/
def output (a : α) : Protocol Ω_X Ω_Y X Y α :=
  Deterministic.Protocol.output a

/-- Alice sends a bit depending on her input `x` and private
randomness `ω_x`. -/
def alice (f : X → Ω_X → Bool)
    (P : Bool → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P

/-- Bob sends a bit depending on his input `y` and private
randomness `ω_y`. -/
def bob (f : Y → Ω_Y → Bool)
    (P : Bool → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.Protocol.bob (fun ⟨ω, y⟩ => f y ω) P

/-- The output of the private-coin protocol `p` on inputs `x`, `y` when Alice's private
random string is `ω_x` and Bob's is `ω_y`: the deterministic run of `p` on `(ω_x, x)` and
`(ω_y, y)` [RY20, Ch. 3, §Variants of Randomized Protocols: private coins]. -/
def rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)

/-- Running a private-coin protocol on inputs `x`, `y` with randomness `ω_x`, `ω_y` is the
same as running the underlying deterministic protocol on `(ω_x, x)` and `(ω_y, y)`.
Definitional unfolding lemma for `rrun`. -/
@[simp]
theorem rrun_eq (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.rrun x y ω_x ω_y = p.run (ω_x, x) (ω_y, y) := rfl

/-- A private-coin protocol `ε`-satisfies a predicate `Q` if for every
input `(x, y)`, the probability that `Q x y (p.rrun ...)` fails
is at most `ε`. -/
def ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      ¬Q x y (p.rrun x y ω.1 ω.2)}).toReal ≤ ε

/-- A private-coin protocol `ε`-computes a function `f` if for every
input `(x, y)`, the probability (under the product of the two coin-flip measures)
of producing an incorrect answer is at most `ε`; this is worst-case error `ε`
[RY20, Ch. 3, §Variants of Randomized Protocols: worst-case error e]. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

/-- A private-coin protocol `ε`-computes `f` if and only if it `ε`-satisfies the relation
"the output on `(x, y)` equals `f x y`"; the two propositions are equal. -/
theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

end Protocol

end PrivateCoin

end CommunicationComplexity
