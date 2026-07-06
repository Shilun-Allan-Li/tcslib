/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinBasic
import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-Message Private-Coin Protocols

## Main results

- `PrivateCoin.FiniteMessage.Protocol`: a private-coin finite-message protocol, defined as a
  deterministic finite-message protocol where Alice's input is `Ω_X × X` and Bob's is `Ω_Y × Y`

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory

namespace PrivateCoin

/-- A private-coin finite-message protocol is a deterministic
finite-message protocol where Alice's input is `Ω_X × X` and
Bob's is `Ω_Y × Y`. -/
abbrev FiniteMessage.Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω_X × X) (Ω_Y × Y) α

namespace FiniteMessage.Protocol

variable {Ω_X Ω_Y : Type*} {X Y α : Type*}

/-- Output node for a private-coin finite-message protocol. -/
def output (a : α) : Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.output a

/-- Alice sends a `β`-valued message depending on her input `x` and
private randomness `ω_x`. -/
def alice {β : Type} [Fintype β] [Nonempty β]
    (f : X → Ω_X → β) (P : β → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P

/-- Bob sends a `β`-valued message depending on his input `y` and
private randomness `ω_y`. -/
def bob {β : Type} [Fintype β] [Nonempty β]
    (f : Y → Ω_Y → β) (P : β → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.bob (fun ⟨ω, y⟩ => f y ω) P

/-- Execute a private-coin finite-message protocol on inputs `x`, `y`
with private randomness `ω_x` for Alice and `ω_y` for Bob. -/
def rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)

@[simp]
theorem rrun_eq (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.rrun x y ω_x ω_y = p.run (ω_x, x) (ω_y, y) := rfl

/-- A finite-message protocol `ε`-satisfies a predicate `Q` if for
every input `(x, y)`, the probability that `Q x y (p.rrun ...)`
fails is at most `ε`. -/
def ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      ¬Q x y (p.rrun x y ω.1 ω.2)} ≤ ε

/-- A finite-message protocol `ε`-computes a function `f` if for
every input `(x, y)`, the probability of producing an incorrect
answer is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y} ≤ ε

theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

/-- Convert a private-coin finite-message protocol to a binary
private-coin protocol. Delegates to `Deterministic.FiniteMessage.Protocol.toProtocol`. -/
noncomputable abbrev toProtocol (p : Protocol Ω_X Ω_Y X Y α) :
    PrivateCoin.Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.toProtocol p

@[simp]
theorem toProtocol_rrun (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.toProtocol).rrun x y ω_x ω_y = p.rrun x y ω_x ω_y := by
  simp [PrivateCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]

@[simp]
theorem toProtocol_complexity (p : Protocol Ω_X Ω_Y X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p

/-- Embed a binary private-coin protocol into a finite-message protocol.
Delegates to `Deterministic.FiniteMessage.Protocol.ofProtocol`. -/
abbrev ofProtocol (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p

@[simp]
theorem ofProtocol_rrun
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (ofProtocol p).rrun x y ω_x ω_y = p.rrun x y ω_x ω_y := by
  simp [rrun, PrivateCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]

@[simp]
theorem ofProtocol_complexity
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    (ofProtocol p).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p

theorem ofProtocol_equiv
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    ∃ (P : Protocol Ω_X Ω_Y X Y α),
      (∀ x y ω_x ω_y,
        P.rrun x y ω_x ω_y = p.rrun x y ω_x ω_y) ∧
      P.complexity = p.complexity :=
  ⟨ofProtocol p,
   fun x y ω_x ω_y => ofProtocol_rrun p x y ω_x ω_y,
   ofProtocol_complexity p⟩

end FiniteMessage.Protocol

end PrivateCoin

end CommunicationComplexity
