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

## Main results

- `PrivateCoin.Protocol`: A private-coin protocol is a deterministic protocol where Alice and Bob each have independent private randomness
- `PrivateCoin.Protocol.ApproxComputes`: A private-coin protocol ε-computes a function if for every input, the probability of producing an incorrect answer is at most ε

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PrivateCoin

/-- A private-coin protocol is a deterministic protocol where Alice's
input is augmented with private randomness `Ω_X` and Bob's with `Ω_Y`.
Alice's message function sees `(ω_x, x)` and Bob's sees `(ω_y, y)`. -/
abbrev Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω_X × X) (Ω_Y × Y) α

namespace Protocol

variable {Ω_X Ω_Y : Type*} {X Y α : Type*}

/-- Output node for a private-coin protocol. -/
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

/-- Execute a private-coin protocol on inputs `x`, `y` with
private randomness `ω_x` for Alice and `ω_y` for Bob. -/
def rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)

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
input `(x, y)`, the probability (under the coin-flip measure)
of producing an incorrect answer is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

end Protocol

end PrivateCoin

end CommunicationComplexity
