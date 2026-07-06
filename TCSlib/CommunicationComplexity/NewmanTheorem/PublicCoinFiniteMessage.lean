/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinBasic
import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-Coin Finite-Message Protocols

## Main results

- `PublicCoin.FiniteMessage.Protocol.ApproxComputes`: a public-coin finite-message protocol ε-computes a function if for every input pair the probability of an incorrect answer is at most ε
- `PublicCoin.FiniteMessage.Protocol.toCoinTape`: converts a public-coin finite-message protocol to a CoinTape-randomness protocol while preserving run behavior and complexity

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory

namespace PublicCoin

/-- A public-coin finite-message protocol is a deterministic
finite-message protocol where Alice's input is `Ω × X` and
Bob's is `Ω × Y`. -/
abbrev FiniteMessage.Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω × X) (Ω × Y) α

namespace FiniteMessage.Protocol

variable {Ω : Type*} {X Y α : Type*}

/-- Output node for a public-coin finite-message protocol. -/
def output (a : α) : Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.output a

/-- Alice sends a `β`-valued message depending on her input `x` and
shared randomness `ω`. -/
def alice {β : Type} [Fintype β] [Nonempty β]
    (f : X → Ω → β) (P : β → Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P

/-- Bob sends a `β`-valued message depending on his input `y` and
shared randomness `ω`. -/
def bob {β : Type} [Fintype β] [Nonempty β]
    (f : Y → Ω → β) (P : β → Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.bob (fun ⟨ω, y⟩ => f y ω) P

/-- Execute a public-coin finite-message protocol on inputs `x`, `y`
with shared randomness `ω`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)

@[simp]
theorem rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl

/-- A public-coin finite-message protocol `ε`-satisfies a predicate `Q`
if for every input `(x, y)`, the probability that
`Q x y (p.rrun ...)` fails is at most `ε`. -/
def ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω |
      ¬Q x y (p.rrun x y ω)} ≤ ε

/-- A public-coin finite-message protocol `ε`-computes a function `f`
if for every input `(x, y)`, the probability of producing an
incorrect answer is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω |
      p.rrun x y ω ≠ f x y} ≤ ε

theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

/-- Convert a public-coin finite-message protocol to a binary
public-coin protocol. Delegates to `Deterministic.FiniteMessage.Protocol.toProtocol`. -/
noncomputable abbrev toProtocol (p : Protocol Ω X Y α) :
    PublicCoin.Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.toProtocol p

@[simp]
theorem toProtocol_rrun (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.toProtocol).rrun x y ω = p.rrun x y ω := by
  simp [PublicCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]

@[simp]
theorem toProtocol_complexity (p : Protocol Ω X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p

/-- Embed a binary public-coin protocol into a finite-message protocol.
Delegates to `Deterministic.FiniteMessage.Protocol.ofProtocol`. -/
abbrev ofProtocol (p : PublicCoin.Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p

@[simp]
theorem ofProtocol_rrun
    (p : PublicCoin.Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (ofProtocol p).rrun x y ω = p.rrun x y ω := by
  simp [rrun, PublicCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]

@[simp]
theorem ofProtocol_complexity
    (p : PublicCoin.Protocol Ω X Y α) :
    (ofProtocol p).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p

theorem ofProtocol_equiv
    (p : PublicCoin.Protocol Ω X Y α) :
    ∃ (P : Protocol Ω X Y α),
      (∀ x y ω, P.rrun x y ω = p.rrun x y ω) ∧
      P.complexity = p.complexity :=
  ⟨ofProtocol p,
   fun x y ω => ofProtocol_rrun p x y ω,
   ofProtocol_complexity p⟩

end FiniteMessage.Protocol

end PublicCoin

end CommunicationComplexity
