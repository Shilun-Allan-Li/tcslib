/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinApproximation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-Coin Randomized Communication Complexity

The `ε`-error public-coin randomized communication complexity `R^pub_ε(f)` of a function `f`
is the least communication cost of a public-coin protocol that computes `f` with worst-case
error at most `ε` [RY20, Ch. 3, §Variants of Randomized Protocols]. Here the shared
randomness ranges over coin tapes `CoinTape n` of every finite length `n`, the infimum is
taken in `ℕ∞` (so it is `⊤` when no protocol qualifies, e.g. for `ε < 0` and nonempty
inputs), and the
characterisations below let one pass freely between binary protocols, finite-message
protocols over coin tapes, and finite-message protocols over arbitrary finite probability
spaces (at the price of an arbitrarily small increase in the error).

## Main definitions

- `PublicCoin.communicationComplexity`: the `ε`-error public-coin randomized communication
  complexity of a function, defined as the minimum worst-case bits exchanged over all
  public-coin protocols computing the function with error at most `ε`.

## Main results

- `PublicCoin.communicationComplexity_le_iff`,
  `PublicCoin.le_communicationComplexity_iff`: the complexity is at most `m` if and only if
  some approximating protocol has complexity at most `m`, and at least `m` if and only if
  every approximating protocol has complexity at least `m`.
- `PublicCoin.communicationComplexity_le_iff_finiteMessage`: the same upper-bound
  characterisation with finite-message protocols in place of binary ones.
- `PublicCoin.communicationComplexity_mono`: communication complexity is monotone in `ε`:
  allowing more error makes computation no harder.
- `PublicCoin.communicationComplexity_le_of_finiteMessage`: a finite-message protocol over
  any finite probability space with error `ε' < ε` bounds the complexity at error `ε`.

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

/-- The `ε`-error public-coin randomized communication complexity `R^pub_ε(f)` of `f`,
defined as the minimum worst-case number of bits exchanged over all
public-coin randomized protocols that compute `f` with error at most
`ε` on every input [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: the minimum
is an infimum in `ℕ∞` (equal to `⊤` if no protocol qualifies), and the shared randomness is
a coin tape `CoinTape n` of some finite length `n`, quantified over all `n`. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol (CoinTape n) X Y α)
    (_ : p.ApproxComputes f ε),
    (p.complexity : ENat)

/-- The `ε`-error public-coin communication complexity of `f` is at most `m` if and only if
there is a public-coin protocol, over a coin tape of some length `n`, that `ε`-computes `f`
with complexity at most `m`. -/
theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

/-- The `ε`-error public-coin communication complexity of `f` is at least `m` if and only if
every public-coin protocol over a coin tape (of any length) that `ε`-computes `f` has
complexity at least `m`. This is the form in which lower bounds are proved. -/
theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε →
        m ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

/-- The `ε`-error public-coin communication complexity of `f` is at most `m` if and only if
there is a public-coin *finite-message* protocol, over a coin tape of some length `n`, that
`ε`-computes `f` with complexity at most `m`. Both directions convert the protocol with
`ofProtocol` / `toProtocol`, which preserve the run function and the complexity.

**Proof sketch.** Rewrite the left side (`communicationComplexity_le_iff`) as the existence of
a binary protocol that `ε`-computes `f` with complexity at most the bound. Forward: given a
binary protocol, `ofProtocol` yields a finite-message protocol with the same run on every
input and the same complexity, so the error bound and the complexity bound carry over.
Backward: `toProtocol` turns a finite-message protocol into a binary one; unfolding the
failure event on each input and rewriting with `toProtocol_run` shows the error is unchanged,
and the complexity is preserved. -/
theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ)
        (p : FiniteMessage.Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ m := by
  rw [communicationComplexity_le_iff]
  constructor
  · -- Binary → FiniteMessage via ofProtocol
    rintro ⟨n, p, hp, hc⟩
    refine ⟨n, FiniteMessage.Protocol.ofProtocol p, ?_,
      Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p ▸ hc⟩
    intro x y
    simp only [FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.ofProtocol_run]
    exact hp x y
  · -- FiniteMessage → Binary via toProtocol
    rintro ⟨n, p, hp, hc⟩
    refine ⟨n, p.toProtocol, ?_,
      Deterministic.FiniteMessage.Protocol.toProtocol_complexity p ▸ hc⟩
    intro x y
    change (volume {ω : CoinTape n |
      Deterministic.Protocol.run (Deterministic.FiniteMessage.Protocol.toProtocol p)
        (ω, x) (ω, y) ≠ f x y}).toReal ≤ ε
    simp only [Deterministic.FiniteMessage.Protocol.toProtocol_run]
    exact hp x y

/-- Public-coin communication complexity is antitone in the error: if `ε' ≤ ε` then the
complexity at error `ε` is at most the complexity at error `ε'`, since allowing more error
can only make computation easier. -/
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

/-- If a public-coin finite-message protocol over an arbitrary finite
probability space `ε'`-computes `f` with `ε' < ε`, then the public-coin
communication complexity at error `ε` is at most the protocol's complexity. The strict
inequality pays for replacing the given probability space by a coin tape via `toCoinTape`,
which approximates the distribution to within the slack `ε - ε'` at no cost in
communication. -/
theorem communicationComplexity_le_of_finiteMessage
    {X Y α} {Ω : Type*} [FiniteProbabilitySpace Ω]
    (f : X → Y → α) (ε ε' : ℝ) (hε : ε' < ε)
    (p : FiniteMessage.Protocol Ω X Y α)
    (hp : p.ApproxComputes f ε') :
    PublicCoin.communicationComplexity f ε ≤ p.complexity := by
  rw [communicationComplexity_le_iff_finiteMessage]
  rw [FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies] at hp
  have hδ : 0 < ε - ε' := sub_pos.mpr hε
  let tc := p.toCoinTape (ε - ε') hδ
  refine ⟨tc.1, tc.2, ?_, le_of_eq ?_⟩
  · rw [FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies]
    have h := p.toCoinTape_approxSatisfies _ ε' (ε - ε') hδ hp
    convert h using 1; ring
  · exact p.toCoinTape_complexity (ε - ε') hδ

end PublicCoin

end CommunicationComplexity
