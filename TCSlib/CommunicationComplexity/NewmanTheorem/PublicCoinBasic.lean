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

A public-coin protocol is a randomized protocol in which Alice and Bob share one random string
`ω` [RY20, Ch. 3, §Variants of Randomized Protocols: public coins]. It is modelled as a
deterministic protocol (`Deterministic.Protocol`) whose inputs are the pairs `(ω, x)` and
`(ω, y)`, so that every result about deterministic protocols applies verbatim once the
randomness is fixed. Correctness is measured by the worst-case error over inputs, with the
probability taken over the shared randomness.

## Main definitions

- `PublicCoin.Protocol`: a deterministic protocol on `(Ω × X) × (Ω × Y)`, i.e. one where
  both players see the shared randomness `ω : Ω`.
- `PublicCoin.Protocol.output`, `PublicCoin.Protocol.alice`, `PublicCoin.Protocol.bob`: the
  constructors, with message functions taking the input and the shared randomness.
- `PublicCoin.Protocol.rrun`: the output of the protocol on inputs `x`, `y` and randomness
  `ω`.
- `PublicCoin.Protocol.ApproxSatisfies`, `PublicCoin.Protocol.ApproxComputes`: a public-coin
  protocol `ε`-computes a function if on every input the probability of an incorrect answer
  is at most `ε`; the predicate version replaces "incorrect" by the failure of a relation.

## Main results

- `PublicCoin.Protocol.ApproxComputes_eq_ApproxSatisfies`: `ε`-computing `f` is the same as
  `ε`-satisfying the relation "the output equals `f x y`".

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

/-- A public-coin protocol with randomness `Ω`, inputs `X`, `Y` and outputs `α`: a
deterministic protocol where both Alice and Bob see the shared random string `ω : Ω` in
addition to their own inputs, so Alice's input is `(ω, x)` and Bob's is `(ω, y)`
[RY20, Ch. 3, §Variants of Randomized Protocols: public coins]. -/
abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω × X) (Ω × Y) α

namespace Protocol

variable {Ω : Type*} {X Y α : Type*}

/-- The public-coin protocol that sends no message and outputs `a` on every input and every
random string. -/
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

/-- The output of the public-coin protocol `p` on inputs `x`, `y` when the shared random
string is `ω`: the deterministic run of `p` on `(ω, x)` and `(ω, y)`
[RY20, Ch. 3, §Variants of Randomized Protocols: public coins]. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)

/-- Running a public-coin protocol on inputs `x`, `y` with randomness `ω` is the same as
running the underlying deterministic protocol on `(ω, x)` and `(ω, y)`. Definitional
unfolding lemma for `rrun`. -/
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
of producing an incorrect answer is at most `ε`; this is worst-case error `ε`
[RY20, Ch. 3, §Variants of Randomized Protocols: worst-case error e]. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω |
      p.rrun x y ω ≠ f x y}).toReal ≤ ε

/-- A public-coin protocol `ε`-computes `f` if and only if it `ε`-satisfies the relation
"the output on `(x, y)` equals `f x y`"; the two propositions are equal. -/
theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]

end Protocol

end PublicCoin

end CommunicationComplexity
