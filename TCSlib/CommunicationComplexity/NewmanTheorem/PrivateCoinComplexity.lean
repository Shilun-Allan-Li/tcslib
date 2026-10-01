/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinApproximation
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-Coin Randomized Communication Complexity

The `ε`-error private-coin randomized communication complexity `R^priv_ε(f)` of a function
`f` is the least communication cost of a private-coin protocol that computes `f` with
worst-case error at most `ε` [RY20, Ch. 3, §Variants of Randomized Protocols]. Here Alice's
and Bob's private randomness range over coin tapes `CoinTape nX` and `CoinTape nY` of every
pair of finite lengths, the infimum is taken in `ℕ∞` (so it is `⊤` when no protocol
qualifies, e.g. for `ε < 0`), and the characterisations below let one pass freely between
binary protocols, finite-message protocols over coin tapes, and finite-message protocols over
arbitrary finite probability spaces (at the price of an arbitrarily small increase in the
error).

## Main definitions

- `PrivateCoin.communicationComplexity`: the `ε`-error private-coin randomized communication
  complexity of a function, defined as the minimum worst-case bits exchanged over all
  private-coin randomized protocols computing the function with error at most `ε`.

## Main results

- `PrivateCoin.communicationComplexity_le_iff`,
  `PrivateCoin.le_communicationComplexity_iff`: the complexity is at most `n` if and only if
  some approximating protocol has complexity at most `n`, and at least `n` if and only if
  every approximating protocol has complexity at least `n`.
- `PrivateCoin.communicationComplexity_le_iff_finiteMessage`: the same upper-bound
  characterisation with finite-message protocols in place of binary ones.
- `PrivateCoin.communicationComplexity_mono`: communication complexity is monotone in `ε`:
  allowing more error makes computation no harder.
- `PrivateCoin.communicationComplexity_le_of_finiteMessage`: a finite-message protocol over
  any pair of finite probability spaces with error `ε' < ε` bounds the complexity at error
  `ε`.

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

/-- The `ε`-error private-coin randomized communication complexity `R^priv_ε(f)` of `f`,
defined as the minimum worst-case number of bits exchanged over all
private-coin randomized protocols that compute `f` with error at most
`ε` on every input [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: the minimum
is an infimum in `ℕ∞` (equal to `⊤` if no protocol qualifies), and the two players' private
randomness are coin tapes `CoinTape nX` and `CoinTape nY` of some finite lengths, quantified
over all `nX`, `nY`. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (nX : ℕ) (nY : ℕ)
    (p : Protocol (CoinTape nX) (CoinTape nY) X Y α)
    (_ : p.ApproxComputes f ε),
    (p.complexity : ENat)

/-- The `ε`-error private-coin communication complexity of `f` is at most `n` if and only if
there is a private-coin protocol, over coin tapes of some lengths `nX`, `nY`, that
`ε`-computes `f` with complexity at most `n`. -/
theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ)
        (p : Protocol (CoinTape nX) (CoinTape nY) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ n := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

/-- The `ε`-error private-coin communication complexity of `f` is at least `n` if and only
if every private-coin protocol over coin tapes (of any lengths) that `ε`-computes `f` has
complexity at least `n`. This is the form in which lower bounds are proved. -/
theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ε ↔
      ∀ (nX nY : ℕ)
        (p : Protocol (CoinTape nX) (CoinTape nY) X Y α),
        p.ApproxComputes f ε →
        n ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

/-- The `ε`-error private-coin communication complexity of `f` is at most `n` if and only if
there is a private-coin *finite-message* protocol, over coin tapes of some lengths `nX`,
`nY`, that `ε`-computes `f` with complexity at most `n`. Both directions convert the
protocol with `ofProtocol` / `toProtocol`, which preserve the run function and the
complexity.

**Proof sketch.** Rewrite the left side (`communicationComplexity_le_iff`) as the existence of
a binary protocol that `ε`-computes `f` with complexity at most the bound. Forward: given a
binary protocol, `ofProtocol` yields a finite-message protocol with the same run on every
input and the same complexity, so the error bound and the complexity bound carry over.
Backward: `toProtocol` turns a finite-message protocol into a binary one; unfolding the
failure event on each input and rewriting with `toProtocol_run` shows the error is unchanged,
and the complexity is preserved. -/
theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ)
        (p : FiniteMessage.Protocol (CoinTape nX) (CoinTape nY) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · -- Binary → FiniteMessage via ofProtocol
    rintro ⟨nX, nY, p, hp, hc⟩
    refine ⟨nX, nY, FiniteMessage.Protocol.ofProtocol p, ?_,
      Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p ▸ hc⟩
    intro x y
    simp only [FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.ofProtocol_run]
    exact hp x y
  · -- FiniteMessage → Binary via toProtocol
    rintro ⟨nX, nY, p, hp, hc⟩
    refine ⟨nX, nY, p.toProtocol, ?_,
      Deterministic.FiniteMessage.Protocol.toProtocol_complexity p ▸ hc⟩
    intro x y
    change (volume {ω : CoinTape nX × CoinTape nY |
      Deterministic.Protocol.run (Deterministic.FiniteMessage.Protocol.toProtocol p)
        (ω.1, x) (ω.2, y) ≠ f x y}).toReal ≤ ε
    simp only [Deterministic.FiniteMessage.Protocol.toProtocol_run]
    exact hp x y

/-- Private-coin communication complexity is antitone in the error: if `ε' ≤ ε` then the
complexity at error `ε` is at most the complexity at error `ε'`, since allowing more error
can only make computation easier. -/
theorem communicationComplexity_mono
    {X Y α} (f : X → Y → α) {ε ε' : ℝ} (h : ε' ≤ ε) :
    communicationComplexity f ε ≤ communicationComplexity f ε' := by
  match hm : communicationComplexity f ε' with
  | ⊤ => exact le_top
  | (m : ℕ) =>
    obtain ⟨nX, nY, p, hp, hc⟩ :=
      (communicationComplexity_le_iff f ε' m).mp (le_of_eq hm)
    exact (communicationComplexity_le_iff f ε m).mpr
      ⟨nX, nY, p, fun x y => le_trans (hp x y) h, hc⟩

/-- If a private-coin finite-message protocol over arbitrary finite probability
spaces `ε'`-computes `f` with `ε' < ε`, then the private-coin communication
complexity at error `ε` is at most the protocol's complexity. The strict inequality pays
for replacing the two given probability spaces by coin tapes via `toCoinTape`, which
approximates the distributions to within the slack `ε - ε'` at no cost in communication. -/
theorem communicationComplexity_le_of_finiteMessage
    {X Y α} {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    (f : X → Y → α) (ε ε' : ℝ) (hε : ε' < ε)
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (hp : p.ApproxComputes f ε') :
    PrivateCoin.communicationComplexity f ε ≤ p.complexity := by
  rw [communicationComplexity_le_iff_finiteMessage]
  -- Convert ApproxComputes to ApproxSatisfies
  rw [FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies] at hp
  -- Use toCoinTape to get a CoinTape-based protocol
  have hδ : 0 < ε - ε' := sub_pos.mpr hε
  let tc := p.toCoinTape (ε - ε') hδ
  refine ⟨tc.1, tc.2.1, tc.2.2, ?_, le_of_eq ?_⟩
  · -- ApproxComputes at error ε
    rw [FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies]
    -- toCoinTape_approxSatisfies gives error ε' + (ε - ε') = ε
    have h := p.toCoinTape_approxSatisfies _ ε' (ε - ε') hδ hp
    convert h using 1; ring
  · exact p.toCoinTape_complexity (ε - ε') hδ

end PrivateCoin

end CommunicationComplexity
