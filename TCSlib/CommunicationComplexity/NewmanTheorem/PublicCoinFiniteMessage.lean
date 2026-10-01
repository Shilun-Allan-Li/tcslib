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

The public-coin model of `PublicCoinBasic` with messages drawn from arbitrary finite types
instead of single bits, built on `Deterministic.FiniteMessage.Protocol`: a public-coin
finite-message protocol is a deterministic finite-message protocol whose inputs are `(ω, x)`
and `(ω, y)` for a shared random string `ω` [RY20, Ch. 3, §Variants of Randomized Protocols].
Sending a message from a finite type `β` costs `⌈log₂ |β|⌉` bits. The two conversions to and
from binary public-coin protocols preserve the run function and the complexity, so the
finite-message model is a convenience, not a change of the measure of communication.

## Main definitions

- `PublicCoin.FiniteMessage.Protocol`: a deterministic finite-message protocol on
  `(Ω × X) × (Ω × Y)`, i.e. one where both players see the shared randomness `ω : Ω`.
- `PublicCoin.FiniteMessage.Protocol.output`, `PublicCoin.FiniteMessage.Protocol.alice`,
  `PublicCoin.FiniteMessage.Protocol.bob`: the constructors, with message functions taking
  the input and the shared randomness.
- `PublicCoin.FiniteMessage.Protocol.rrun`: the output of the protocol on inputs `x`, `y`
  and randomness `ω`.
- `PublicCoin.FiniteMessage.Protocol.ApproxSatisfies`,
  `PublicCoin.FiniteMessage.Protocol.ApproxComputes`: a public-coin finite-message protocol
  `ε`-computes a function if for every input pair the probability of an incorrect answer is
  at most `ε`.
- `PublicCoin.FiniteMessage.Protocol.toProtocol`, `PublicCoin.FiniteMessage.Protocol.ofProtocol`:
  the conversions to and from binary public-coin protocols.

## Main results

- `PublicCoin.FiniteMessage.Protocol.toProtocol_rrun`,
  `PublicCoin.FiniteMessage.Protocol.toProtocol_complexity`: the binary protocol obtained from
  a finite-message protocol has the same run function and the same complexity.
- `PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun`,
  `PublicCoin.FiniteMessage.Protocol.ofProtocol_complexity`,
  `PublicCoin.FiniteMessage.Protocol.ofProtocol_equiv`: the finite-message protocol obtained
  from a binary protocol has the same run function and the same complexity.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory

namespace PublicCoin

/-- A public-coin finite-message protocol with randomness `Ω`, inputs `X`, `Y` and outputs
`α`: a deterministic finite-message protocol where Alice's input is `Ω × X` and Bob's is
`Ω × Y`, so both players see the shared random string
[RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: each message is an element of
an arbitrary finite type rather than a single bit, charged `⌈log₂ |β|⌉` bits. -/
abbrev FiniteMessage.Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω × X) (Ω × Y) α

namespace FiniteMessage.Protocol

variable {Ω : Type*} {X Y α : Type*}

/-- The public-coin finite-message protocol that sends no message and outputs `a` on every
input and every random string. -/
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

/-- The output of the public-coin finite-message protocol `p` on inputs `x`, `y` when the
shared random string is `ω`: the deterministic run of `p` on `(ω, x)` and `(ω, y)`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)

/-- Running a public-coin finite-message protocol on inputs `x`, `y` with randomness `ω` is
the same as running the underlying deterministic finite-message protocol on `(ω, x)` and
`(ω, y)`. Definitional unfolding lemma for `rrun`. -/
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
if for every input `(x, y)`, the probability (over the shared randomness) of producing an
incorrect answer is at most `ε`; this is worst-case error `ε`
[RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: messages come from arbitrary
finite types rather than being single bits. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω |
      p.rrun x y ω ≠ f x y} ≤ ε

/-- A public-coin finite-message protocol `ε`-computes `f` if and only if it `ε`-satisfies
the relation "the output on `(x, y)` equals `f x y`"; the two propositions are equal. -/
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

/-- The binary public-coin protocol obtained from a finite-message protocol `p` by
`toProtocol` has the same output as `p` on every input `x`, `y` and every random string
`ω`. -/
@[simp]
theorem toProtocol_rrun (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.toProtocol).rrun x y ω = p.rrun x y ω := by
  simp [PublicCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]

/-- The binary public-coin protocol obtained from a finite-message protocol `p` by
`toProtocol` has exactly the complexity of `p`, where a `β`-valued message of `p` is charged
`⌈log₂ |β|⌉` bits. -/
@[simp]
theorem toProtocol_complexity (p : Protocol Ω X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p

/-- Embed a binary public-coin protocol into a finite-message protocol.
Delegates to `Deterministic.FiniteMessage.Protocol.ofProtocol`. -/
abbrev ofProtocol (p : PublicCoin.Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p

/-- The finite-message protocol obtained from a binary public-coin protocol `p` by
`ofProtocol` has the same output as `p` on every input `x`, `y` and every random string
`ω`. -/
@[simp]
theorem ofProtocol_rrun
    (p : PublicCoin.Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (ofProtocol p).rrun x y ω = p.rrun x y ω := by
  simp [rrun, PublicCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]

/-- The finite-message protocol obtained from a binary public-coin protocol `p` by
`ofProtocol` has exactly the complexity of `p`. -/
@[simp]
theorem ofProtocol_complexity
    (p : PublicCoin.Protocol Ω X Y α) :
    (ofProtocol p).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p

/-- Every binary public-coin protocol `p` is equivalent to some public-coin finite-message
protocol: there is a finite-message protocol with the same output as `p` on every input and
random string and with the same complexity (namely `ofProtocol p`). -/
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
