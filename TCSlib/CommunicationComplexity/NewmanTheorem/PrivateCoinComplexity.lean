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

## Main results

- `PrivateCoin.communicationComplexity`: The ε-error private-coin randomized communication
  complexity of a function, defined as the minimum worst-case bits exchanged over all
  private-coin randomized protocols computing the function with error at most ε.
- `PrivateCoin.communicationComplexity_le_iff_finiteMessage`: Characterization of
  private-coin complexity in terms of finite-message protocols over arbitrary finite
  probability spaces.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PrivateCoin

/-- The `ε`-error randomized communication complexity of `f`,
defined as the minimum worst-case number of bits exchanged over all
coin-flip randomized protocols that compute `f` with error at most
`ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (nX : ℕ) (nY : ℕ)
    (p : Protocol (CoinTape nX) (CoinTape nY) X Y α)
    (_ : p.ApproxComputes f ε),
    (p.complexity : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ)
        (p : Protocol (CoinTape nX) (CoinTape nY) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ n := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ε ↔
      ∀ (nX nY : ℕ)
        (p : Protocol (CoinTape nX) (CoinTape nY) X Y α),
        p.ApproxComputes f ε →
        n ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

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

/-- Communication complexity is monotone in ε: allowing more error can
only make computation easier. -/
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

/-- If a finite-message protocol over arbitrary finite probability
spaces ε'-computes f with ε' < ε, then the private-coin communication
complexity at error ε is at most the protocol's complexity. -/
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
