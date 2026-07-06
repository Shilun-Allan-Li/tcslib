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

## Main results

- `PublicCoin.communicationComplexity`: The ε-error public-coin randomized communication
  complexity of a function, defined as the minimum worst-case bits exchanged over all
  public-coin protocols computing the function with error at most ε.
- `PublicCoin.communicationComplexity_le_iff`: Characterization of when the complexity
  is at most m in terms of existence of an approximating protocol.
- `PublicCoin.communicationComplexity_mono`: Communication complexity is monotone in ε:
  allowing more error makes computation no harder.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

/-- The `ε`-error public-coin randomized communication complexity of `f`,
defined as the minimum worst-case number of bits exchanged over all
public-coin randomized protocols that compute `f` with error at most
`ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol (CoinTape n) X Y α)
    (_ : p.ApproxComputes f ε),
    (p.complexity : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        p.ApproxComputes f ε →
        m ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

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

/-- Communication complexity is monotone in ε: allowing more error can
only make computation easier. -/
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
probability space ε'-computes f with ε' < ε, then the public-coin
communication complexity at error ε is at most the protocol's complexity. -/
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
