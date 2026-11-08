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

The private-coin model of `PrivateCoinBasic` with messages drawn from arbitrary finite types
instead of single bits, built on `Deterministic.FiniteMessage.Protocol`: a private-coin
finite-message protocol is a deterministic finite-message protocol whose inputs are
`(ω_x, x)` and `(ω_y, y)` for private random strings `ω_x` of Alice and `ω_y` of Bob
[RY20, Ch. 3, §Variants of Randomized Protocols]. Sending a message from a finite type `β`
costs `⌈log₂ |β|⌉` bits. The two conversions to and from binary private-coin protocols
preserve the run function and the complexity, so the finite-message model is a convenience,
not a change of the measure of communication.

## Main definitions

- `PrivateCoin.FiniteMessage.Protocol`: a deterministic finite-message protocol on
  `(Ω_X × X) × (Ω_Y × Y)`, i.e. one where Alice sees her private randomness `ω_x : Ω_X` and
  Bob sees his private randomness `ω_y : Ω_Y`.
- `PrivateCoin.FiniteMessage.Protocol.output`, `PrivateCoin.FiniteMessage.Protocol.alice`,
  `PrivateCoin.FiniteMessage.Protocol.bob`: the constructors, with message functions taking
  the input and the player's own randomness.
- `PrivateCoin.FiniteMessage.Protocol.rrun`: the output of the protocol on inputs `x`, `y`
  and randomness `ω_x`, `ω_y`.
- `PrivateCoin.FiniteMessage.Protocol.ApproxSatisfies`,
  `PrivateCoin.FiniteMessage.Protocol.ApproxComputes`: a private-coin finite-message
  protocol `ε`-computes a function if for every input pair the probability of an incorrect
  answer is at most `ε`.
- `PrivateCoin.FiniteMessage.Protocol.toProtocol`,
  `PrivateCoin.FiniteMessage.Protocol.ofProtocol`: the conversions to and from binary
  private-coin protocols.

## Main results

- `PrivateCoin.FiniteMessage.Protocol.toProtocol_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.toProtocol_complexity`: the binary protocol obtained
  from a finite-message protocol has the same run function and the same complexity.
- `PrivateCoin.FiniteMessage.Protocol.ofProtocol_rrun`,
  `PrivateCoin.FiniteMessage.Protocol.ofProtocol_complexity`,
  `PrivateCoin.FiniteMessage.Protocol.ofProtocol_equiv`: the finite-message protocol
  obtained from a binary protocol has the same run function and the same complexity.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory

namespace PrivateCoin

/-- A private-coin finite-message protocol with randomness `Ω_X` for Alice and `Ω_Y` for
Bob, inputs `X`, `Y` and outputs `α`: a deterministic finite-message protocol where Alice's
input is `Ω_X × X` and Bob's is `Ω_Y × Y`, so each player sees only their own random string
[RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: each message is an element of
an arbitrary finite type rather than a single bit, charged `⌈log₂ |β|⌉` bits. -/
abbrev FiniteMessage.Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω_X × X) (Ω_Y × Y) α

namespace FiniteMessage.Protocol

variable {Ω_X Ω_Y : Type*} {X Y α : Type*}

/-- The private-coin finite-message protocol that sends no message and outputs `a` on every
input and every pair of random strings. -/
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

/-- The output of the private-coin finite-message protocol `p` on inputs `x`, `y` when
Alice's private random string is `ω_x` and Bob's is `ω_y`: the deterministic run of `p` on
`(ω_x, x)` and `(ω_y, y)`. -/
def rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)

/-- Running a private-coin finite-message protocol on inputs `x`, `y` with randomness
`ω_x`, `ω_y` is the same as running the underlying deterministic finite-message protocol on
`(ω_x, x)` and `(ω_y, y)`. Definitional unfolding lemma for `rrun`. -/
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

/-- A private-coin finite-message protocol `ε`-computes a function `f` if for
every input `(x, y)`, the probability (over the product of the two private randomness
spaces) of producing an incorrect answer is at most `ε`; this is worst-case error `ε`
[RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: messages come from arbitrary
finite types rather than being single bits. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y} ≤ ε

/-- A private-coin finite-message protocol `ε`-computes `f` if and only if it `ε`-satisfies
the relation "the output on `(x, y)` equals `f x y`"; the two propositions are equal. -/
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

/-- The binary private-coin protocol obtained from a finite-message protocol `p` by
`toProtocol` has the same output as `p` on every input `x`, `y` and every pair of random
strings `ω_x`, `ω_y`. -/
@[simp]
theorem toProtocol_rrun (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.toProtocol).rrun x y ω_x ω_y = p.rrun x y ω_x ω_y := by
  simp [PrivateCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]

/-- The binary private-coin protocol obtained from a finite-message protocol `p` by
`toProtocol` has exactly the complexity of `p`, where a `β`-valued message of `p` is charged
`⌈log₂ |β|⌉` bits. -/
@[simp]
theorem toProtocol_complexity (p : Protocol Ω_X Ω_Y X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p

/-- Embed a binary private-coin protocol into a finite-message protocol.
Delegates to `Deterministic.FiniteMessage.Protocol.ofProtocol`. -/
abbrev ofProtocol (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p

/-- The finite-message protocol obtained from a binary private-coin protocol `p` by
`ofProtocol` has the same output as `p` on every input `x`, `y` and every pair of random
strings `ω_x`, `ω_y`. -/
@[simp]
theorem ofProtocol_rrun
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (ofProtocol p).rrun x y ω_x ω_y = p.rrun x y ω_x ω_y := by
  simp [rrun, PrivateCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]

/-- The finite-message protocol obtained from a binary private-coin protocol `p` by
`ofProtocol` has exactly the complexity of `p`. -/
@[simp]
theorem ofProtocol_complexity
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    (ofProtocol p).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p

/-- Every binary private-coin protocol `p` is equivalent to some private-coin finite-message
protocol: there is a finite-message protocol with the same output as `p` on every input and
pair of random strings and with the same complexity (namely `ofProtocol p`). -/
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
