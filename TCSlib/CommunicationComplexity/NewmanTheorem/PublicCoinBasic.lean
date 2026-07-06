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
# Public-Coin Communication Protocol

## Main results

- `PublicCoin.Protocol`: A deterministic protocol where both players see shared randomness
- `PublicCoin.Protocol.ApproxComputes`: A public-coin protocol ε-computes a function if the probability of an incorrect answer is at most ε

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

/-- A public-coin protocol is a deterministic protocol where both
Alice and Bob see shared randomness `Ω`. Alice's input is `(ω, x)`
and Bob's is `(ω, y)`. -/
abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω × X) (Ω × Y) α

namespace Protocol

variable {Ω : Type*} {X Y α : Type*}

/-- Output node for a public-coin protocol. -/
def output (a : α) : Protocol Ω X Y α :=
  Deterministic.Protocol.output a

/-- Alice sends a bit depending on her input `x` and shared
randomness `ω`. -/
def alice (f : X → Ω → Bool)
    (P : Bool → Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P

/-- Bob sends a bit depending on his input `y` and shared
randomness `ω`. -/
def bob (f : Y → Ω → Bool)
    (P : Bool → Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.Protocol.bob (fun ⟨ω, y⟩ => f y ω) P

/-- Execute a public-coin protocol on inputs `x`, `y` with
shared randomness `ω`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)

@[simp]
theorem rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl

/-- A public-coin protocol `ε`-satisfies a predicate `Q` if for every
input `(x, y)`, the probability that `Q x y (p.rrun ...)` fails
is at most `ε`. -/
def ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω |
      ¬Q x y (p.rrun x y ω)}).toReal ≤ ε

/-- A public-coin protocol `ε`-computes a function `f` if for every
input `(x, y)`, the probability (under the shared coin-flip measure)
of producing an incorrect answer is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω |
      p.rrun x y ω ≠ f x y}).toReal ≤ ε

theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

end Protocol

end PublicCoin

end CommunicationComplexity
