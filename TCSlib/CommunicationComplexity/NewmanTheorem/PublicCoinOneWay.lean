/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.OneWay
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import Mathlib.Data.ENat.Lattice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-Way Public-Coin Protocols and Complexity

In a one-way protocol Alice sends a single message to Bob, who must then output the answer
[Rou16, §1.7]; in the public-coin randomized version both players additionally see a shared
random string [Rou16, §2.2]. This file defines public-coin one-way protocols as deterministic
one-way protocols (`Deterministic.OneWay.Protocol`) whose inputs are `(ω, x)` and `(ω, y)`,
the worst-case error criterion, and the resulting `ε`-error one-way public-coin
communication complexity, with the same infimum characterisations as in
`PublicCoinComplexity`.

## Main definitions

- `PublicCoin.OneWay.Protocol`: one-way public-coin protocols, defined as deterministic
  one-way protocols over shared randomness × input spaces.
- `PublicCoin.OneWay.Protocol.rrun`: the output on inputs `x`, `y` and randomness `ω`.
- `PublicCoin.OneWay.Protocol.ApproxComputes`: a protocol `ε`-computes a function if for
  every input pair, the error probability over shared randomness is at most `ε`.
- `PublicCoin.OneWay.communicationComplexity`: the `ε`-error one-way public-coin
  communication complexity of a function, as the minimum one-way message cost over all
  approximating protocols.

## Main results

- `PublicCoin.OneWay.communicationComplexity_le_iff`,
  `PublicCoin.OneWay.le_communicationComplexity_iff`: the complexity is at most `m` if and
  only if some approximating protocol has cost at most `m`, and at least `m` if and only if
  every approximating protocol has cost at least `m`.
- `PublicCoin.OneWay.communicationComplexity_mono`: communication complexity is monotone in
  `ε`.

## References

* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity
namespace PublicCoin
namespace OneWay

open MeasureTheory ProbabilityTheory

/-- A one-way public-coin protocol with randomness `Ω`, inputs `X`, `Y` and outputs `α`: a
deterministic one-way protocol in which Alice sends a single message computed from her input
and the shared random string `(ω, x)`, and Bob outputs an answer from that message and
`(ω, y)` [Rou16, §1.7 Definition (one-way protocol)],
[Rou16, §2.2 Assumption (Public coins), Assumption (Two-sided error)]. -/
abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  CommunicationComplexity.Deterministic.OneWay.Protocol (Ω × X) (Ω × Y) α

namespace Protocol

variable {Ω X Y α : Type*}

/-- Execute a one-way public-coin protocol on inputs `x`, `y` with
shared randomness `ω`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.decode (p.send (ω, x)) (ω, y)

/-- A one-way public-coin protocol `ε`-computes `f` if for every input
pair `(x, y)`, the error probability over shared randomness is at most `ε` (two-sided
worst-case error) [Rou16, §1.7 Definition (one-way protocol)],
[Rou16, §2.2 Assumption (Public coins), Assumption (Two-sided error)]. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω | p.rrun x y ω ≠ f x y}).toReal ≤ ε

end Protocol

/-- The `ε`-error one-way public-coin communication complexity of `f`,
defined as the minimum one-way message cost over all shared-randomness
protocols that compute `f` with error at most `ε` on every input
[Rou16, §1.7 Definition (one-way protocol)],
[Rou16, §2.2 Assumption (Public coins), Assumption (Two-sided error)]. Deviation: the minimum is an
infimum in `ℕ∞` (equal to `⊤` if no protocol qualifies), and the shared randomness is a
coin tape `CoinTape n` of some finite length `n`, quantified over all `n`. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol (CoinTape n) X Y α)
    (_ : Protocol.ApproxComputes p f ε),
    (p.cost : ENat)

/-- The `ε`-error one-way public-coin communication complexity of `f` is at most `m` if and
only if there is a one-way public-coin protocol, over a coin tape of some length `n`, that
`ε`-computes `f` with message cost at most `m`. -/
theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        Protocol.ApproxComputes p f ε ∧
        p.cost ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

/-- The `ε`-error one-way public-coin communication complexity of `f` is at least `m` if and
only if every one-way public-coin protocol over a coin tape (of any length) that
`ε`-computes `f` has message cost at least `m`. This is the form in which lower bounds are
proved. -/
theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        Protocol.ApproxComputes p f ε →
        m ≤ p.cost := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

/-- One-way public-coin communication complexity is antitone in the error: if `ε' ≤ ε` then
the complexity at error `ε` is at most the complexity at error `ε'`, since allowing more
error can only make computation easier. -/
theorem communicationComplexity_mono
    {X Y α} (f : X → Y → α) {ε ε' : ℝ} (h : ε' ≤ ε) :
    communicationComplexity f ε ≤ communicationComplexity f ε' := by
  match hm : communicationComplexity f ε' with
  | ⊤ => exact le_top
  | (m : ℕ) =>
    obtain ⟨n, p, hp, hc⟩ :=
      (communicationComplexity_le_iff f ε' m).mp (le_of_eq hm)
    exact (communicationComplexity_le_iff f ε m).mpr
      ⟨n, p, fun x y => le_trans (hp x y) h, hc⟩

end OneWay
end PublicCoin
end CommunicationComplexity
